import CSTTT.FullNative02.Protocol

namespace CSTTT.FullNative02
set_option autoImplicit false

theorem chosen_native_step (supply : Supply) (w v : World) (owner : Nat)
    (action : Bool) (state : FullNative.State)
    (h : chooseNative supply w owner action state=some v) : Step supply w v := by
  cases hf : (nativeRows supply w owner action).find? (fun e =>
      decide ((e.1.residents owner).map Resident.current=some state)) with
  | none => simp only [chooseNative,hf,Option.map_none] at h; cases h
  | some entry =>
    have eq : entry.1=v := by simpa only [chooseNative,hf,Option.map_some,Option.some.injEq] using h
    cases eq
    exact .native (List.mem_of_find?_eq_some hf)

theorem run_choices_history (supply : Supply) (inventory : Nat) (rom : ROM)
    (w v : World) (owner : Nat) (path : List FullNative.State)
    (h : runChoices supply w owner path=some v) (history : History supply inventory rom w) :
    History supply inventory rom v := by
  induction path generalizing w v with
  | nil => simp only [runChoices,Option.some.injEq] at h; cases h; exact history
  | cons state rest ih =>
    cases hc : chooseNative supply w owner false state with
    | none => simp [runChoices,hc] at h
    | some next =>
      simp only [runChoices,hc,Bind.bind,Option.bind] at h
      exact ih next v h (History.next history (chosen_native_step _ _ _ _ _ _ hc))

theorem bootstrap_history (supply : Supply) (inventory : Nat) (rom : ROM)
    (w v : World) (source left right : Nat) (h : bootstrap w source left right=some v)
    (history : History supply inventory rom w) : History supply inventory rom v := by
  cases hs : writeSnapshot w source left right with
  | none => simp [bootstrap,hs] at h
  | some staged =>
    cases hl : activate staged left with
    | none => simp [bootstrap,hs,hl] at h
    | some first =>
      simp only [bootstrap,hs,hl,Bind.bind,Option.bind] at h
      exact .next (.next (.next history (.snapshot hs)) (.activation hl)) (.activation h)

theorem source_history : History renewable 8 .canonical32 sourceWorld := by
  exact run_choices_history _ _ _ _ _ _ _ (Option.some_get source_run_available).symm (.initial (by decide))

theorem branches_history : History renewable 8 .canonical32 branchesWorld := by
  have eq : branchesRun=some branchesWorld := (Option.some_get branches_run_available).symm
  cases hb : bootstrap sourceWorld 0 1 2 with
  | none => simp [branchesRun,hb] at eq
  | some copied =>
    have hc := bootstrap_history renewable 8 .canonical32 sourceWorld copied 0 1 2 hb source_history
    cases hl : runChoices renewable copied 1 sixCycle with
    | none => simp [branchesRun,hb,hl] at eq
    | some left =>
      have hleft := run_choices_history _ _ _ _ _ _ _ hl hc
      cases hr : runChoices renewable left 2 sixCycle with
      | none => simp [branchesRun,hb,hl,hr] at eq
      | some right =>
        have hright := run_choices_history _ _ _ _ _ _ _ hr hleft
        have final : withdraw right=branchesWorld := by simpa [branchesRun,hb,hl,hr] using eq
        rw [← final]
        exact .next hright (.withdraw right)

/-- Original relation-valued return and operational invariants share the same
computed output, for EVERY actual supported branch of the positive script. -/
theorem ttf04_owned_operational_realization (outcome : Settlement) (probability : Rat)
    (member : (outcome,probability)∈fusionRows renewable branchesWorld mainRequest) :
    History renewable 8 .canonical32 outcome.world ∧ Ordered outcome.world ∧ Housed outcome.world ∧
    0<probability ∧
    Prospects.FallbackFissionFusionEmpty Node (ancestry outcome.world) (.birth 0)
      mainParents.left.version mainParents.right.version (.birth 24)
      (EmptyTarget renewable branchesWorld mainRequest) := by
  have history := History.next branches_history (Step.fusion member)
  have facts := full_actual_positive_return outcome probability member
  obtain ⟨_,_,_,positive,_,_,_,_,_,_,_,_,_,original⟩ := facts
  have length : branchesWorld.events.length=22 := by decide +kernel
  exact ⟨history,(history_invariants _ _ _ _ history).2,
    all_history_accounts_housed _ _ _ _ history,positive,by simpa only [length] using original⟩

end CSTTT.FullNative02
