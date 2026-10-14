import CSTTT.Targets.ComputedFIACH.Entries
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-! Kernel checks of the completed package/autonomy seam. These are NOT
TTH-06 certificates: lineage and the ExactAutonomyCertificate readout are
separate outstanding constructions, recorded in audit/G6c_tth06_lanes.md. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

theorem baseline_shared_autonomy : sharedAutonomyCheck baseline kernel = true := by
  unfold sharedAutonomyCheck
  decide

theorem baseline_AF : AF baseline := by
  unfold AF fullAutonomyCheck
  rw [baseline_greatestF,baseline_shared_autonomy]
  simp only [Bool.true_and,List.all_eq_true]
  intro s _
  exact baseline_packageAt s

theorem baseline_AO : AO baseline := by
  unfold AO operationalAutonomyCheck
  rw [baseline_greatestO]
  exact baseline_shared_autonomy

theorem package_deletion_not_AF : ¬ AF packageDeletion :=
  fun h => package_deletion_package (fullAutonomy_implies_package packageDeletion h)

theorem package_deletion_AO : AO packageDeletion := by
  unfold AO operationalAutonomyCheck
  rw [package_deletion_greatestO]
  unfold sharedAutonomyCheck
  decide

theorem lineage_deletion_AO : AO lineageDeletion := by
  unfold AO operationalAutonomyCheck
  rw [lineage_deletion_greatestO]
  unfold sharedAutonomyCheck
  decide

theorem withdrawal_deletion_not_AF : ¬ AF withdrawalDeletion := by
  simp [AF,fullAutonomyCheck,withdrawal_deletion_greatestF,sharedAutonomyCheck]
theorem withdrawal_deletion_not_AO : ¬ AO withdrawalDeletion := by
  simp [AO,operationalAutonomyCheck,withdrawal_deletion_greatestO,sharedAutonomyCheck]

/-- The source-absent sensitivity guard is about actual acquisition, not
about a ledger field or a positive-only corridor sibling check. -/
def sourceAbsent : RawLaneModel :=
  {baseline with assignment := withdraw8 canonical}
theorem source_absent_no_entries : entries sourceAbsent = [] := by
  apply phase2_unavailable_no_entries
  intro r _
  exact no_source_rejects_phase2 sourceAbsent (by rfl) r
theorem source_absent_not_AF : ¬ AF sourceAbsent := empty_entries_reject_F _ source_absent_no_entries
theorem source_absent_not_AO : ¬ AO sourceAbsent := empty_entries_reject_O _ source_absent_no_entries
end CSTTT.TargetTheory.ComputedFIACH
