import CSTTT.Targets.ComputedFIACH.Autonomy
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-! Raw G6 controls, verbatim intervention rules from
`audit/proposed_models/TTH06-LANES.model.json`, committed at 16d7274.
The package intervention deletes publishedC; the lineage intervention clears
ONLY mix2.sourceSupport; withdrawal removes ONLY retained target recharge.
No result table, lane verdict, safe set, or entry list is transcribed. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

def baseline : RawLaneModel := ⟨canonical,[.targetRecharge],removedRoles,false⟩
def packageDeletion : RawLaneModel :=
  {baseline with assignment := put canonical .publishedC none}
def lineageDeletion : RawLaneModel :=
  {baseline with assignment := mapCell canonical .eventTable (fun es =>
    es.map fun e => if e.id = .mix2 then {e with sourceSupport := false} else e)}
def withdrawalDeletion : RawLaneModel := {baseline with retained := []}

theorem baseline_withdrawn : withdrawnAssignment baseline = canonical := by
  unfold withdrawnAssignment
  change mapCell (image canonical) (.resources .target) _ = canonical
  rw [image_canonical]
  funext k
  cases k <;> try rfl
  case resources t => cases t <;> rfl

theorem baseline_packageAt (x : KState) : packageAtCheck baseline x = true := by
  unfold packageAtCheck
  rw [baseline_withdrawn]
  have hp : packageCheck canonical .target = true :=
    (package_check_iff _ _).mpr (canonical_assigned_package .target)
  have hs : stateViewsCheck canonical x = true := by unfold stateViewsCheck; decide
  have ha : advancementCheck baseline = true := by unfold advancementCheck; rw [baseline_withdrawn]; decide
  change packageLaneCheck canonical && packageCheck canonical .target && stateViewsCheck canonical x && advancementCheck baseline = true
  rw [show packageLaneCheck canonical = true from package_lane_positive,hp,hs,ha]
  rfl

theorem baseline_greatestF : greatestF baseline = kernel := by
  have hv : ViableF baseline kernel := by
    intro x _
    simp only [retainF,baseline_packageAt,Bool.true_and,List.any_eq_true]
    refine ⟨canonicalAction x,?_,?_⟩
    · cases x <;> decide
    · have hw : withdrawalCheck baseline = true := by decide
      have ha : advancementCheck baseline = true := by unfold advancementCheck; rw [baseline_withdrawn]; decide
      simp only [responseCheck,hw,ha,Bool.true_and,withdrawnInputs,baseline_withdrawn]
      cases x <;> decide
  apply List.filter_eq_self.mpr
  intro x hx
  exact (List.mem_filter.mp (greatestF_contains_viable baseline kernel hv hx)).2

theorem baseline_greatestO : greatestO baseline = kernel := by
  unfold greatestO withdrawnInputs
  rw [baseline_withdrawn]
  exact (controls8_greatest .funded .target).trans (c8_funded_greatest_is_kernel .target)

theorem package_deletion_package : ¬ PackageLane packageDeletion.assignment :=
  package_lane_missing .publishedC

theorem package_deletion_greatestF : greatestF packageDeletion = [] := by
  apply greatestF_missing_package_empty
  have hp := package_deletion_package
  cases he : packageLaneCheck packageDeletion.assignment with
  | false => rfl
  | true => exact False.elim (hp he)

theorem package_deletion_operational_inputs :
    withdrawnInputs packageDeletion = withdrawnInputs baseline := rfl
theorem lineage_deletion_operational_inputs :
    withdrawnInputs lineageDeletion = withdrawnInputs baseline := rfl
theorem package_deletion_greatestO : greatestO packageDeletion = kernel := by
  unfold greatestO
  rw [package_deletion_operational_inputs]
  exact baseline_greatestO
theorem lineage_deletion_greatestO : greatestO lineageDeletion = kernel := by
  unfold greatestO
  rw [lineage_deletion_operational_inputs]
  exact baseline_greatestO
theorem withdrawal_deletion_package : PackageLane withdrawalDeletion.assignment := package_lane_positive

theorem withdrawal_deletion_greatestF : greatestF withdrawalDeletion = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have hp := greatestF_packageInside withdrawalDeletion x hx
  have ha : advancementCheck withdrawalDeletion = false := by decide
  simp only [packageAtCheck,ha,Bool.and_false] at hp
  contradiction

theorem withdrawal_deletion_greatestO : greatestO withdrawalDeletion = [] := by
  exact unavailable8_empty _ _ (by decide)
end CSTTT.TargetTheory.ComputedFIACH
