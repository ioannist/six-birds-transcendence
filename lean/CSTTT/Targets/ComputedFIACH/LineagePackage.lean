import CSTTT.Targets.ComputedFIACH.AtomicAcquisition

/-! The registered support intervention changes ONLY mix2.sourceSupport.
First expose the cell/exchange equation, then use locality on unaffected
clauses. C6 and C7 are inspected as the finite checks of the edited event
assignment; no acceptance rule is modified to facilitate normalization. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def dropMix2Source (es : List CSTTT.POS04.Event) :=
  es.map fun e => if e.id = .mix2 then {e with sourceSupport := false} else e
def lineageArrival := mapCell canonical .eventTable dropMix2Source

theorem lineage_staged_assignment : image lineageDeletion.assignment = lineageArrival := by
  change image (mapCell canonical .eventTable dropMix2Source) = lineageArrival
  rw [image_map_events,image_canonical]
  rfl

theorem lineage_unaffected_clause (t : Tag) (c : Clause)
    (hc : Cell.eventTable ∉ clauseScope t c) :
    clauseAccept lineageArrival t c ↔ clauseAccept canonical t c :=
  clause_accept_locality t c (events_update_agrees_off_scope canonical dropMix2Source _ hc)

theorem lineage_C6 (t : Tag) : C6Accept lineageArrival t := by
  cases t <;> decide

theorem lineage_C7 (t : Tag) : C7Accept lineageArrival t := by
  cases t <;> decide

theorem lineage_assigned_package (t : Tag) : AssignedPackagePass lineageArrival t := by
  intro c
  cases c with
  | c6 => exact lineage_C6 t
  | c7 => exact lineage_C7 t
  | c1 | c2 | c3 | c4 | c5 | c8 =>
    apply (lineage_unaffected_clause t _ (by cases t <;> decide)).mpr
    exact canonical_assigned_package t _

theorem lineage_deletion_package : PackageLane lineageDeletion.assignment := by
  apply (package_lane_iff _).mpr
  refine ⟨?_,?_⟩
  · decide
  · rw [lineage_staged_assignment]
    exact lineage_assigned_package .target

theorem lineage_withdrawn_assignment : withdrawnAssignment lineageDeletion = lineageArrival := by
  unfold withdrawnAssignment
  rw [lineage_staged_assignment]
  funext k
  cases k <;> try rfl
  case resources t => cases t <;> rfl

theorem lineage_packageAt (x : KState) : packageAtCheck lineageDeletion x = true := by
  unfold packageAtCheck
  rw [lineage_withdrawn_assignment]
  have hp : packageCheck lineageArrival .target = true :=
    (package_check_iff _ _).mpr (lineage_assigned_package .target)
  have hs : stateViewsCheck lineageArrival x = true := by unfold stateViewsCheck; decide
  have ha : advancementCheck lineageDeletion = true := by decide
  rw [show packageLaneCheck lineageDeletion.assignment = true from lineage_deletion_package,hp,hs,ha]
  rfl

/-- C8 resources and the declared response rows ignore the edited support bit;
this is exact decoder equality, not a supplied positive response predicate. -/
theorem lineage_response_equation (S : List KState) (x : KState)
    (d : LaneDisturbance) (a : Action) :
    responseCheck lineageDeletion S x d a = responseCheck baseline S x d a := rfl

theorem lineage_deletion_greatestF : greatestF lineageDeletion = kernel := by
  have hv : ViableF lineageDeletion kernel := by
    intro x _
    simp only [retainF,lineage_packageAt,Bool.true_and,List.any_eq_true]
    have hx : x ∈ greatestF baseline := by rw [baseline_greatestF]; cases x <;> decide
    obtain ⟨a,ha,hr⟩ := greatestF_all_support_responses baseline x hx .nominal
    exact ⟨a,ha,by rw [lineage_response_equation,← baseline_greatestF]; exact hr⟩
  apply List.filter_eq_self.mpr
  intro x hx
  exact (List.mem_filter.mp (greatestF_contains_viable lineageDeletion kernel hv hx)).2

theorem lineage_deletion_AF : AF lineageDeletion := by
  have hs : sharedAutonomyCheck lineageDeletion kernel = true := by
    have h := lineage_deletion_AO
    simpa [AO,operationalAutonomyCheck,lineage_deletion_greatestO] using h
  unfold AF fullAutonomyCheck
  rw [lineage_deletion_greatestF,hs]
  simp only [Bool.true_and,List.all_eq_true]
  intro x _
  exact lineage_packageAt x

end CSTTT.TargetTheory.ComputedFIACH
