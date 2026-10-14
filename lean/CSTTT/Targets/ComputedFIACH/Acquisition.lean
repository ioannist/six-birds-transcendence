import CSTTT.Targets.ComputedFIACH.AutonomyInstances
import CSTTT.POS04.AtomicCorridor

/-! One derived acquisition view of the staged immutable assignment.
G6_lane_spec.md:104–145,213–241. A view is never independently supplied to
certification: `checkedAcquisition` either rejects completeness or returns
exactly the staged assignment. Later projections read these same cells. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.CorridorTheory.AtomicChain

/-- Phase-2 inputs plus the raw signature/trace dependencies of BOTH carriers.
This scope deliberately excludes publishedC: deleting C1 evidence must not
break the independent lineage acquisition lane. -/
def acquisitionDependencies : List Cell :=
  phase2Dependencies ++ clauseScope .source .c6 ++ clauseScope .target .c6

def checkedAcquisition (m : RawLaneModel) : Option Assignment :=
  if Complete acquisitionDependencies (image m.assignment) then
    some (image m.assignment) else none

theorem acquisition_eq_staged (m : RawLaneModel) (a : Assignment)
    (h : checkedAcquisition m = some a) : a = image m.assignment := by
  unfold checkedAcquisition at h
  split at h
  · exact Option.some.inj h.symm
  · contradiction

theorem acquisition_complete (m : RawLaneModel) (a : Assignment)
    (h : checkedAcquisition m = some a) : Complete acquisitionDependencies a := by
  unfold checkedAcquisition at h
  split at h
  · rename_i hc
    cases Option.some.inj h
    exact hc
  · contradiction

theorem acquisition_missing_staged (m : RawLaneModel) (k : Cell)
    (hk : k ∈ acquisitionDependencies) (h : image m.assignment k = none) :
    checkedAcquisition m = none := by
  unfold checkedAcquisition
  split
  · rename_i hc
    have hp := hc k hk
    rw [h] at hp
    contradiction
  · rfl

theorem acquisition_missing_dependency (m : RawLaneModel) (k : Cell)
    (hk : k ∈ acquisitionDependencies) :
    checkedAcquisition {m with assignment := put m.assignment (swapCell k) none} = none :=
  acquisition_missing_staged _ k hk (image_delete_cell _ _)

/-- Future objects have no supplied candidate argument and no independent
positive table. They are the assigned C6 functions of the same view. -/
def acquisitionFuture (a : Assignment) (tag : Tag) := future6 a tag
def acquisitionDynamics (a : Assignment) (tag : Tag) := dynamics6 a tag
abbrev AcquisitionClosure (a : Assignment) (tag : Tag) := Closure6 a tag

theorem acquisition_future_equations (m : RawLaneModel) (a : Assignment)
    (h : checkedAcquisition m = some a) (t : Tag) :
    acquisitionFuture a t = future6 (image m.assignment) t ∧
    acquisitionDynamics a t = dynamics6 (image m.assignment) t := by
  rw [acquisition_eq_staged m a h]
  exact ⟨rfl,rfl⟩

theorem acquisition_readout_laws (a : Assignment) (t : Tag) :
    ClosureReadoutLaws6 a t := closure_readout_laws6 a t

/-- Exact exchange/update equations eliminate the dependent-cell normalization
obstruction before closed finite event checks are attempted. -/
theorem image_map_events (a : Assignment) (f : List CSTTT.POS04.Event → List CSTTT.POS04.Event) :
    image (mapCell a .eventTable f) = mapCell (image a) .eventTable f := by
  funext k
  cases k
  all_goals try (rename_i tag; cases tag)
  all_goals simp [image,exchangeAssignment,mapCell,put,swapCell,Function.comp_def]
  all_goals rfl

theorem events_update_agrees_off_scope (a : Assignment) (f : List CSTTT.POS04.Event → List CSTTT.POS04.Event)
    (scope : List Cell) (he : Cell.eventTable ∉ scope) :
    Agrees scope (mapCell a .eventTable f) a := by
  intro k hk
  have hn : k ≠ .eventTable := fun h => he (h ▸ hk)
  exact put_other a .eventTable k _ hn

theorem events_update_decoder_off_scope (a : Assignment) (f : List CSTTT.POS04.Event → List CSTTT.POS04.Event)
    (scope : List Cell) (he : Cell.eventTable ∉ scope) :
    decode scope (mapCell a .eventTable f) = decode scope a :=
  decoder_locality (events_update_agrees_off_scope a f scope he)

end CSTTT.TargetTheory.ComputedFIACH
