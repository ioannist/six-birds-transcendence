import CSTTT.FullNative02.SelectorEquivalence

namespace CSTTT.FullNative02.SelectorEquivalence
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

theorem partition_permutation (w : World) (parent left right : Nat)
    (xs ys xs' ys' : List Token) (hx : xs.Perm xs') (hy : ys.Perm ys') :
    (partition w parent left right xs ys).map world=(partition w parent left right xs' ys').map world := by
  have memx : ∀ t : Token,(t∈xs)=(t∈xs') := fun t => propext hx.mem_iff
  have memy : ∀ t : Token,(t∈ys)=(t∈ys') := fun t => propext hy.mem_iff
  have primaryX := least_owned_permutation xs xs' hx
  have primaryY := least_owned_permutation ys ys' hy
  simp only [leastOwned] at primaryX primaryY
  unfold partition
  rw [primaryX,primaryY]
  simp only [memx,memy,hx.nodup_iff,hy.nodup_iff]
  cases enabled : FullNative02.binding w parent with
  | none => rfl
  | some data =>
    rcases data with ⟨r,rom,key⟩
    cases x : (tokens.filter fun t => decide (t∈xs')).head? with
    | none => rfl
    | some first =>
      cases y : (tokens.filter fun t => decide (t∈ys')).head? with
      | none => rfl
      | some second =>
        simp only [Bind.bind,Option.bind]
        split
        · simp only [Option.map_some,world,events,List.map_append,List.map_cons,List.map_nil,event,
            canonical_keys_permutation xs xs' hx,canonical_keys_permutation ys ys' hy]
        · rfl

theorem receipt (supply : Supply) (w : World) (owner : Nat) (r : Resident) (rom : ROM)
    (key : Token) (action : Bool) (edge : FullNative.State × Nat) :
    makeReceipt supply (world w) owner r rom key action edge=makeReceipt supply w owner r rom key action edge := rfl

theorem advance (supply : Supply) (w : World) (owner : Nat) (r : Resident) (rom : ROM)
    (key : Token) (action : Bool) (edge : FullNative.State × Nat) :
    world (FullNative02.advance supply w owner r rom key action edge)=
      FullNative02.advance supply (world w) owner r rom key action edge := by
  simp only [FullNative02.advance,receipt,world,events,List.map_append,List.map_cons,List.map_nil,event,List.length_map]

theorem rows (supply : Supply) (w : World) (owner : Nat) (action : Bool) :
    (nativeRows supply w owner action).map (fun e => (world e.1,e.2))=
      nativeRows supply (world w) owner action := by
  simp only [nativeRows,access]
  cases enabled : FullNative02.access w owner with
  | none => rfl
  | some data =>
    rcases data with ⟨r,rom,key⟩
    simp only [List.map_map,Function.comp_def,advance]

theorem choose (supply : Supply) (w : World) (owner : Nat) (action : Bool) (state : FullNative.State) :
    (chooseNative supply w owner action state).map world=chooseNative supply (world w) owner action state := by
  simp only [chooseNative,←rows,List.find?_map,Function.comp_def,world]
  simp only [Option.map_map,Function.comp_def]

theorem run (supply : Supply) (w : World) (owner : Nat) (path : List FullNative.State) :
    (runChoices supply w owner path).map world=runChoices supply (world w) owner path := by
  induction path generalizing w with
  | nil => rfl
  | cons state rest ih =>
    simp only [runChoices,←choose]
    cases selected : chooseNative supply w owner false state with
    | none => rfl
    | some v => simpa only [Option.map_some] using ih v

/-- Arbitrary supported acquisition histories; no selector-order or sortedness
premise. Both continuations are real native paths with the same requested states. -/
theorem selector_permutation_admission_on_supported_histories
    (supply : Supply) (inventory : Nat) (rom : ROM) (w first second v z : World)
    (parent left right owner : Nat) (xs ys xs' ys' : List Token)
    (hx : xs.Perm xs') (hy : ys.Perm ys') (path : List FullNative.State)
    (history : History supply inventory rom w)
    (a : partition w parent left right xs ys=some first)
    (b : partition w parent left right xs' ys'=some second)
    (c : runChoices supply first owner path=some v)
    (d : runChoices supply second owner path=some z) :
    History supply inventory rom v ∧ History supply inventory rom z ∧ Epoch.accept v owner=Epoch.accept z owner := by
  have births := partition_permutation w parent left right xs ys xs' ys' hx hy
  rw [a,b] at births
  have same : world first=world second := Option.some.inj births
  have endings := congrArg (fun x => runChoices supply x owner path) same
  change runChoices supply (world first) owner path=runChoices supply (world second) owner path at endings
  rw [←run,←run,c,d] at endings
  have readout : world v=world z := Option.some.inj endings
  exact ⟨run_choices_history _ _ _ _ _ _ _ c (.next history (.partition a)),
    run_choices_history _ _ _ _ _ _ _ d (.next history (.partition b)),
    (admission v owner).symm.trans ((congrArg (fun x => Epoch.accept x owner) readout).trans (admission z owner))⟩

end CSTTT.FullNative02.SelectorEquivalence
