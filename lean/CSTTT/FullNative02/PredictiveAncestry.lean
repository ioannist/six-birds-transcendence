import CSTTT.FullNative02.Autonomy

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

def SourceOwned (w : World) (owner : Nat) : Prop :=
  ∃ r key,access w owner=some (r,.canonical32,key) ∧ ancestry w (.birth 0) r.version

theorem native_source_owned (w v : World) (owner : Nat) (source : SourceOwned w owner)
    (n : Nat) (edge : (v,n)∈nativeRows renewable w owner false) : SourceOwned v owner := by
  obtain ⟨r,key,enabled,past⟩ := source
  rw [native_rows_from_access _ _ _ _ _ _ enabled false] at edge
  obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
  have world : v=advance renewable w owner r .canonical32 key false e := (congrArg Prod.fst eq).symm
  rw [world]
  have retained := footprint_ancestry _ _ (advance_footprint renewable w owner r .canonical32 key false e none)
    (.birth 0) r.version past
  refine ⟨_,key,renewable_access_after _ _ _ _ _ enabled false e,?_⟩
  apply Path.extend (y:=.event w.events.length)
  · apply Path.extend retained
    simp [ledgerEdges,advance,ledger_append,ledgerEdgesFrom,eventEdges]
  · simp [ledgerEdges,advance,ledger_append,ledgerEdgesFrom,eventEdges]

theorem retained_source_owned (owner : Nat) (start w : World) (source : SourceOwned start owner)
    (history : Retained owner start w) : SourceOwned w owner := by
  induction history with
  | root => exact source
  | next past v n edge ih => exact native_source_owned _ _ owner ih n edge
  | @foreign w past other different action v n edge ih =>
    obtain ⟨r,key,enabled,ancestral⟩ := ih
    cases foreign : access w other with
    | none => simp [nativeRows,foreign] at edge
    | some data =>
      rcases data with ⟨s,rom,k⟩
      rw [native_rows_from_access _ _ _ _ _ _ foreign action] at edge
      obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
      have world : v=advance renewable w other s rom k action e := (congrArg Prod.fst eq).symm
      rw [world]
      exact ⟨r,key,foreign_access_after _ _ _ _ _ _ _ _ _ enabled foreign different action e,
        footprint_ancestry _ _ (advance_footprint renewable w other s rom k action e none)
          _ _ ancestral⟩

theorem both_children_source_owned : SourceOwned branchesWorld 1 ∧ SourceOwned branchesWorld 2 := by
  have left : (access branchesWorld 1).map (fun data => data.1.version)=some (.version 15) := by decide +kernel
  have right : (access branchesWorld 2).map (fun data => data.1.version)=some (.version 21) := by decide +kernel
  obtain ⟨l,lk,enabledL,_,_,_⟩ := Epoch.accepted_access branchesWorld 1 both_withdrawn_children_accept.1
  obtain ⟨r,rk,enabledR,_,_,_⟩ := Epoch.accepted_access branchesWorld 2 both_withdrawn_children_accept.2
  have lv : l.version=.version 15 := by simpa only [enabledL,Option.map_some,Option.some.injEq] using left
  have rv : r.version=.version 21 := by simpa only [enabledR,Option.map_some,Option.some.injEq] using right
  have lp : ancestry branchesWorld (.birth 0) (.version 15) := by
    simpa only [main_resource_context.2.2.2.1] using branches_source_ancestry.1
  have rp : ancestry branchesWorld (.birth 0) (.version 21) := by
    simpa only [main_resource_context.2.2.2.2.1] using branches_source_ancestry.2
  exact ⟨⟨l,lk,enabledL,lv.symm ▸ lp⟩,⟨r,rk,enabledR,rv.symm ▸ rp⟩⟩

theorem every_fusion_birth_source_owned (e : Settlement × Rat)
    (member : e∈fusionRows renewable branchesWorld mainRequest) : SourceOwned e.1.world 3 := by
  have readout : ∀ e∈fusionRows renewable branchesWorld mainRequest,
      (access e.1.world 3).map (fun data => (data.2.1,data.2.2,data.1.version))=
        some (.canonical32,1,.birth 24) := by decide +kernel
  have bound : branchesWorld.events.length=22 := by decide +kernel
  have born : ancestry e.1.world (.birth 0) (.birth 24) := by
    rw [main_positive_rows] at member
    obtain ⟨pair,_,eq⟩ := List.mem_map.mp member
    cases eq
    have old := fusion_preserves_old_ancestry renewable branchesWorld mainRequest mainParents pair
      (pairProbability mainParents.rom mainParents.left.current mainParents.right.current false false pair)
      _ _ branches_source_ancestry.1
    have fused := (both_actual_parent_paths renewable branchesWorld mainRequest mainParents pair
      (pairProbability mainParents.rom mainParents.left.current mainParents.right.current false false pair)).1
    simpa only [bound] using path_trans old fused
  cases enabled : access e.1.world 3 with
  | none =>
    have fields := readout e member
    simp only [enabled,Option.map_none] at fields
    cases fields
  | some data =>
    rcases data with ⟨r,rom,key⟩
    have fields := readout e member
    simp only [enabled,Option.map_some,Option.some.injEq,Prod.mk.injEq] at fields
    obtain ⟨rfl,rfl,version⟩ := fields
    exact ⟨r,1,enabled,version.symm ▸ born⟩

theorem run_choices_retained (w v : World) (owner : Nat) (states : List State)
    (h : runChoices renewable w owner states=some v) : Retained owner w v := by
  induction states generalizing w v with
  | nil => simp only [runChoices,Option.some.injEq] at h; subst v; exact .root _
  | cons state rest ih =>
    cases selected : chooseNative renewable w owner false state with
    | none => simp [runChoices,selected] at h
    | some next =>
      have actual : ∃ n,(next,n)∈nativeRows renewable w owner false := by
        cases chosen : (nativeRows renewable w owner false).find? (fun e =>
            decide ((e.1.residents owner).map Resident.current=some state)) with
        | none => simp only [chooseNative,chosen,Option.map_none] at selected; cases selected
        | some edge =>
          have same : edge.1=next := by
            simpa only [chooseNative,chosen,Option.map_some,Option.some.injEq] using selected
          exact ⟨edge.2,same ▸ List.mem_of_find?_eq_some chosen⟩
      obtain ⟨n,edge⟩ := actual
      exact retained_trans owner _ _ _ (.next (.root w) next n edge)
        (ih next v (by simpa [runChoices,selected] using h))

theorem every_warm_output_source_owned (e : Settlement × Rat)
    (member : e∈fusionRows renewable branchesWorld mainRequest) (v : World)
    (h : outputWarmup e.1.world=some v) : SourceOwned v 3 := by
  cases present : e.1.world.residents 3 with
  | none => simp [outputWarmup,present] at h
  | some r =>
    cases selected : chooseNative renewable e.1.world 3 false ⟨false,false,false,false,!r.current.phase⟩ with
    | none => simp [outputWarmup,present,selected] at h
    | some next =>
      have first : runChoices renewable e.1.world 3 [⟨false,false,false,false,!r.current.phase⟩]=some next := by
        simp [runChoices,selected]
      have after := retained_source_owned 3 _ _ (every_fusion_birth_source_owned e member)
        (run_choices_retained _ _ _ _ first)
      exact retained_source_owned 3 _ _ after (run_choices_retained _ _ _ _
        (by simpa [outputWarmup,present,selected] using h))

def Predictive (w : World) (owner : Nat) : Prop :=
  SourceOwned w owner ∧
  (∃ source key,access sourceWorld 0=some (source,.canonical32,key) ∧ source.receipts.length=6) ∧
  ∀ r key,access w owner=some (r,.canonical32,key)→∀ word trace,
    WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
      (fun w => (Temporal.actual w owner).map Temporal.observe) w word trace=
    WeightedFuture.law Temporal.rows (fun r => some (Temporal.observe r))
      (Temporal.frame w r key) word trace

theorem predictive_from_same_execution (w : World) (owner : Nat) (source : SourceOwned w owner) : Predictive w owner := by
  have readout : (access sourceWorld 0).map (fun data => (data.2.1,data.1.receipts.length))=
      some (.canonical32,6) := by decide +kernel
  refine ⟨source,?_,fun r key enabled => Temporal.actual_all_words _ _ _ _ enabled⟩
  cases enabled : access sourceWorld 0 with
  | none => simp [enabled] at readout
  | some data =>
    rcases data with ⟨r,rom,key⟩
    simp only [enabled,Option.map_some,Option.some.injEq,Prod.mk.injEq] at readout
    obtain ⟨rfl,count⟩ := readout
    exact ⟨r,key,rfl,count⟩

end CSTTT.FullNative02
