import CSTTT.Targets.ComputedFIACH.Assembly

/-! G6 single-field sensitivity proposals; all other recipes stay fixed.
No proposal is an argument of certificate validity. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit CSTTT.TransportTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def acquisitionReadoutCorruption : RunReadoutField → POS04RawBridge
  | .predictive => { assignmentRawBridge baseline with runPredictive := fun _ => .exit2 }
  | .counter => { assignmentRawBridge baseline with runCounter := fun x => min x.2.counter 2 }
  | .ticks => { assignmentRawBridge baseline with runTicks := fun x => min x.2.ticks 2 }
  | .tickPhase => { assignmentRawBridge baseline with runTicks := fun x => min x.2.ticks 2 }
  | .progress => { assignmentRawBridge baseline with runProgress := fun x => min x.2.counter 2 }
  | .writer => { assignmentRawBridge baseline with runRecordWriter := fun _ => false }
  | .record => { assignmentRawBridge baseline with runRecord := fun _ => 0 }
  | .residue => { assignmentRawBridge baseline with runResidue := fun _ => ([],[]) }
  | .maintenance => { assignmentRawBridge baseline with runMaintenance := fun _ => false }
  | .owner => { assignmentRawBridge baseline with runOwner := fun _ => tagCarrierId .source }
  | .enabled => { assignmentRawBridge baseline with runEnabled := fun _ => false }
  | .sourceFactor => { assignmentRawBridge baseline with runSourceFactor := fun _ => none }
  | .targetFactor => { assignmentRawBridge baseline with runTargetFactor := fun _ => none }

local instance (f : RunReadoutField) : DecidableEq (acquisitionReadoutCorruption f).RunState :=
  by cases f <;> exact inferInstanceAs (DecidableEq AcquisitionRun)
local instance (f : RunReadoutField) : DecidableEq (acquisitionReadoutCorruption f).AuditIndex :=
  by cases f <;> exact inferInstanceAs (DecidableEq SnapshotIndex)

local instance (f : RunReadoutField) : DecidableEq (acquisitionReadoutCorruption f).RunOutcome := by
  cases f <;> exact inferInstanceAs (DecidableEq CSTTT.POS04.PredictiveNow)
local instance : DecidableEq (assignmentRawBridge baseline).RunPredictive :=
  inferInstanceAs (DecidableEq CSTTT.POS04.PredictiveNow)
local instance (f g : RunReadoutField) : DecidableEq (RunReadoutValue (acquisitionReadoutCorruption f) g) := by
  cases f <;> cases g <;> dsimp [RunReadoutValue,acquisitionReadoutCorruption] <;> infer_instance

theorem acquisition_predictive_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .predictive) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .predictive) .predictive
    (bridgeRootRun (acquisitionReadoutCorruption .predictive) false (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_counter_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .counter) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .counter) .counter
    (bridgeRootRun (acquisitionReadoutCorruption .counter) false (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_ticks_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .ticks) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .ticks) .ticks
    (bridgeRootRun (acquisitionReadoutCorruption .ticks) false (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_tickPhase_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .tickPhase) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .tickPhase) .tickPhase
    (bridgeRootRun (acquisitionReadoutCorruption .tickPhase) false (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_progress_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .progress) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .progress) .progress
    (bridgeRootRun (acquisitionReadoutCorruption .progress) false (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_writer_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .writer) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .writer) .writer
    (bridgeRootRun (acquisitionReadoutCorruption .writer) false (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_record_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .record) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .record) .record
    (bridgeRootRun (acquisitionReadoutCorruption .record) false (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_residue_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .residue) := by
  apply bridge_readout_initial_observation_guard (acquisitionReadoutCorruption .residue) false
    (.a,.endpoint) (by decide +kernel) (fun observation => observation.residue)
  decide +kernel

theorem acquisition_maintenance_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .maintenance) := by
  apply bridge_readout_initial_observation_guard (acquisitionReadoutCorruption .maintenance) false
    (.a,.endpoint) (by decide +kernel) (fun observation => observation.maintenance)
  decide +kernel

theorem acquisition_owner_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .owner) := by
  apply bridge_readout_initial_observation_guard (acquisitionReadoutCorruption .owner) true
    (.a,.endpoint) (by decide +kernel) (fun observation => observation.owner)
  decide +kernel

theorem acquisition_enabled_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .enabled) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .enabled) .enabled
    (bridgeRootRun (acquisitionReadoutCorruption .enabled) false (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_sourceFactor_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .sourceFactor) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .sourceFactor) .sourceFactor
    (bridgeRootRun (acquisitionReadoutCorruption .sourceFactor) false (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_targetFactor_readout_guard :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption .targetFactor) := by
  apply bridge_readout_field_update_guard (acquisitionReadoutCorruption .targetFactor) .targetFactor
    (bridgeRootRun (acquisitionReadoutCorruption .targetFactor) true (.a,.endpoint))
    (by apply FutureClosure.root; decide +kernel)
    .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) (by decide +kernel)
  decide +kernel

theorem acquisition_every_bridge_readout_guard (f : RunReadoutField) :
    ¬ BridgeRunReadoutLaws (acquisitionReadoutCorruption f) := by
  cases f
  · exact acquisition_predictive_readout_guard
  · exact acquisition_counter_readout_guard
  · exact acquisition_ticks_readout_guard
  · exact acquisition_tickPhase_readout_guard
  · exact acquisition_progress_readout_guard
  · exact acquisition_writer_readout_guard
  · exact acquisition_record_readout_guard
  · exact acquisition_residue_readout_guard
  · exact acquisition_maintenance_readout_guard
  · exact acquisition_owner_readout_guard
  · exact acquisition_enabled_readout_guard
  · exact acquisition_sourceFactor_readout_guard
  · exact acquisition_targetFactor_readout_guard

/-- The capped-update witnesses above use a real positive-support step,
not merely the future closure's zero-weight branches. -/
theorem acquisition_guard_step_supported (tag : Tag) :
    0 < (assignmentRawBridge baseline).runNumerator
      (if tag = .source then bridgeSourceRun (assignmentRawBridge baseline) (.a,.endpoint)
       else bridgeTargetRun (assignmentRawBridge baseline) (.a,.endpoint))
      .cw (predictive6 (runInputs6 canonical .source) (.inK .p2w1)) := by
  cases tag <;> decide +kernel

/-- Every named withdrawal role is independently required. -/
theorem missing_withdrawal_role_rejects (m : RawLaneModel) (r : RemovedRole)
    (hr : r ∉ m.removed) : withdrawalCheck m = false := by
  have hm : r ∈ removedRoles := by cases r <;> decide
  have ha : removedRoles.all m.removed.contains = false := by
    cases he : removedRoles.all m.removed.contains
    · rfl
    · have hmem := List.all_eq_true.mp he r hm
      have : r ∈ m.removed := List.mem_of_elem_eq_true hmem
      exact False.elim (hr this)
  simp [withdrawalCheck,ha]

theorem source_available_after_withdrawal_rejects (m : RawLaneModel)
    (h : m.sourcePresentAfterWithdrawal = true) : withdrawalCheck m = false := by
  simp [withdrawalCheck,h]

theorem withdrawal_failure_rejects_F_O (m : RawLaneModel)
    (h : withdrawalCheck m = false) : ¬ AF m ∧ ¬ AO m := by
  constructor
  · simp [AF,fullAutonomyCheck,sharedAutonomyCheck,h]
  · simp [AO,operationalAutonomyCheck,sharedAutonomyCheck,h]

end CSTTT.TargetTheory.ComputedFIACH
