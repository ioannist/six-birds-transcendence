import CSTTT.Targets.GenericHandoff.ViableSet
import CSTTT.Targets.ComputedFIACH.Autonomy

/-! Exact specialization of the extracted viable-set computation. This does
not assert a new finite-factor lift for run contexts or generic disturbances. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04Adapter
open CSTTT.POS04 CSTTT.Objecthood.T1Audit

theorem subsets_eq (xs : List KState) :
    ViableSet.subsets xs = Assigned.subsets8 xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ViableSet.subsets,Assigned.subsets8,ih]

theorem c8_engine_eq (d : Assigned.ViabilityInputs) (tag : Tag) :
    ViableSet.greatest kernel (Assigned.retain8 d tag) = Assigned.greatest8 d tag := by
  simp only [ViableSet.greatest,Assigned.greatest8,Assigned.candidates8,subsets_eq,
    Assigned.viableTest8]

theorem c8_retain_monotone (d : Assigned.ViabilityInputs) (tag : Tag) :
    ViableSet.Monotone (Assigned.retain8 d tag) := by
  intro A B h x hx
  exact Assigned.retain8_mono d tag h hx

theorem c8_generic_greatest (d : Assigned.ViabilityInputs) (tag : Tag)
    (S : List KState) (hv : Assigned.Viable8 d tag S) :
    S ⊆ Assigned.greatest8 d tag := by
  rw [← c8_engine_eq]
  exact ViableSet.greatest_contains_viable kernel (fun x => by cases x <;> decide)
    _ (c8_retain_monotone d tag) S hv

theorem full_engine_eq (m : CSTTT.TargetTheory.ComputedFIACH.RawLaneModel) :
    ViableSet.greatest kernel (CSTTT.TargetTheory.ComputedFIACH.retainF m) =
      CSTTT.TargetTheory.ComputedFIACH.greatestF m := by
  simp only [ViableSet.greatest,CSTTT.TargetTheory.ComputedFIACH.greatestF,
    Assigned.candidates8,subsets_eq]

theorem full_retain_monotone (m : CSTTT.TargetTheory.ComputedFIACH.RawLaneModel) :
    ViableSet.Monotone (CSTTT.TargetTheory.ComputedFIACH.retainF m) := by
  intro A B h x hx
  exact CSTTT.TargetTheory.ComputedFIACH.retainF_mono m h x hx
end CSTTT.TargetTheory.GenericHandoff.POS04Adapter
