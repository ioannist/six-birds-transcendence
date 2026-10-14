import CSTTT.FullNative02.HistoryLift

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

def Withdrawn (w : World) : Prop :=
  w.residents 0=none ∧ w.acquisition=false ∧ (∀ a,w.slots a=none) ∧
    (∀ key,w.accounts.custody key≠.external ∧ w.accounts.custody key≠.local 0)

theorem withdrawn_branches : Withdrawn branchesWorld := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_⟩
  · intro a
    simp [branchesWorld,branchesRun,withdraw]
  · intro key
    have bound := key.isLt
    have cases : key=0 ∨ key=1 ∨ key=2 ∨ key=3 := by simp only [Fin.ext_iff]; omega
    rcases cases with rfl | rfl | rfl | rfl <;> decide +kernel

theorem native_slots (supply : Supply) (w v : World) (owner : Nat) (action : Bool)
    (n : Nat) (edge : (v,n)∈nativeRows supply w owner action) : v.slots=w.slots := by
  cases enabled : access w owner with
  | none => simp [nativeRows,enabled] at edge
  | some data =>
    rcases data with ⟨r,rom,key⟩
    rw [native_rows_from_access _ _ _ _ _ _ enabled action] at edge
    obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
    cases eq
    rfl

theorem chosen_slots (w v : World) (owner : Nat) (state : State)
    (h : chooseNative renewable w owner false state=some v) : v.slots=w.slots := by
  cases selected : (nativeRows renewable w owner false).find? (fun e =>
      decide ((e.1.residents owner).map Resident.current=some state)) with
  | none => simp only [chooseNative,selected,Option.map_none] at h; cases h
  | some e =>
    have same : e.1=v := by simpa only [chooseNative,selected,Option.map_some,Option.some.injEq] using h
    rw [←same]
    exact native_slots _ _ _ _ _ _ (List.mem_of_find?_eq_some selected)

theorem run_choices_slots (w v : World) (owner : Nat) (path : List State)
    (h : runChoices renewable w owner path=some v) : v.slots=w.slots := by
  induction path generalizing w v with
  | nil => simp only [runChoices,Option.some.injEq] at h; subst v; rfl
  | cons state rest ih =>
    cases selected : chooseNative renewable w owner false state with
    | none => simp [runChoices,selected] at h
    | some next =>
      exact (ih next v (by simpa [runChoices,selected] using h)).trans
        (chosen_slots _ _ _ _ selected)

theorem warmup_slots (w v : World) (h : outputWarmup w=some v) : v.slots=w.slots := by
  cases present : w.residents 3 with
  | none => simp [outputWarmup,present] at h
  | some r =>
    cases selected : chooseNative renewable w 3 false ⟨false,false,false,false,!r.current.phase⟩ with
    | none => simp [outputWarmup,present,selected] at h
    | some next =>
      exact (run_choices_slots next v 3 _ (by simpa [outputWarmup,present,selected] using h)).trans
        (chosen_slots _ _ _ _ selected)

theorem fusion_slots (supply : Supply) (w : World) (q : FusionRequest)
    (e : Settlement × Rat) (h : e∈fusionRows supply w q) : e.1.world.slots=w.slots := by
  cases view : parentView w q with
  | none => simp [fusionRows,view] at h
  | some p =>
    simp only [fusionRows,view] at h
    split at h
    · simp only [List.mem_singleton] at h
      cases h
      rfl
    · obtain ⟨pair,_,eq⟩ := List.mem_map.mp h
      cases eq
      rfl

theorem withdrawn_all_acquired_outputs :
    ∀ e∈fusionRows renewable branchesWorld mainRequest,
      ∀ v∈(outputWarmup e.1.world).toList,Withdrawn v := by
  intro e he v hv
  have fields : v.residents 0=none ∧ v.acquisition=false ∧
      (∀ key∈tokens,v.accounts.custody key≠.external ∧ v.accounts.custody key≠.local 0) := by
    have finite : ∀ e∈fusionRows renewable branchesWorld mainRequest,
        ∀ v∈(outputWarmup e.1.world).toList,
          v.residents 0=none ∧ v.acquisition=false ∧
          (∀ key∈tokens,v.accounts.custody key≠.external ∧ v.accounts.custody key≠.local 0) := by decide +kernel
    exact finite e he v hv
  refine ⟨fields.1,fields.2.1,?_,?_⟩
  · intro a
    have done : outputWarmup e.1.world=some v := by simpa only [Option.mem_toList] using hv
    rw [warmup_slots _ _ done,fusion_slots _ _ _ _ he]
    exact withdrawn_branches.2.2.1 a
  · intro key
    have member : key∈tokens := by
      have bound := key.isLt
      have cases : key=0 ∨ key=1 ∨ key=2 ∨ key=3 := by simp only [Fin.ext_iff]; omega
      rcases cases with rfl | rfl | rfl | rfl <;> simp [tokens]
    exact fields.2.2 key member

theorem native_keeps_withdrawal (w v : World) (owner : Nat) (action : Bool) (n : Nat)
    (withdrawn : Withdrawn w) (edge : (v,n)∈nativeRows renewable w owner action) : Withdrawn v := by
  cases enabled : access w owner with
  | none => simp [nativeRows,enabled] at edge
  | some data =>
    rcases data with ⟨r,rom,key⟩
    have facts := binding_facts _ _ _ _ _ (access_facts _ _ _ _ _ enabled).1
    have different : 0≠owner := by
      intro same
      subst owner
      rw [withdrawn.1] at facts
      cases facts.1
    rw [native_rows_from_access _ _ _ _ _ _ enabled action] at edge
    obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
    have world : v=advance renewable w owner r rom key action e := (congrArg Prod.fst eq).symm
    rw [world]
    exact ⟨by simpa [advance,put,different] using withdrawn.1,withdrawn.2⟩

theorem retained_withdrawal (owner : Nat) (start w : World) (withdrawn : Withdrawn start)
    (history : Retained owner start w) : Withdrawn w := by
  induction history with
  | root => exact withdrawn
  | next past v n edge ih => exact native_keeps_withdrawal _ _ _ _ _ ih edge
  | foreign past other different action v n edge ih => exact native_keeps_withdrawal _ _ _ _ _ ih edge

end CSTTT.FullNative02
