import CSTTT.POS04.FrozenSnapshots

/-! G1c CR4: single-readout corruptions of a fixed POS-04 bridge. Update
recipes, raw dynamics, audit roots and all other readouts stay fixed. Each
of the 13 fields is checked, including derived tick phase (corrupting its
only raw input, ticks). These are sensitivity witnesses, not new models.
Sources: frozen M3 spec lines 22,30-33,40-44. -/
namespace CSTTT.POS04
open CSTTT.TransportTheory CSTTT.Objecthood.T1Audit

local instance : DecidableEq pos04SnapshotBridge.RunState :=
  inferInstanceAs (DecidableEq C6State)
local instance : LawfulBEq OutcomeClass where
  rfl := by intro a; cases a <;> rfl
  eq_of_beq := by intro a b h; cases a <;> cases b <;> cases h <;> rfl

/-- Only the selected readout changes; all law recipes remain fixed. -/
def pos04ReadoutCorruption : RunReadoutField → POS04RawBridge
  | .predictive => { pos04SnapshotBridge with runPredictive := fun _ => .exit2 }
  | .counter => { pos04SnapshotBridge with runCounter := fun x => min x.eventCount 2 }
  | .ticks | .tickPhase => { pos04SnapshotBridge with runTicks := fun x => min x.tickCount 2 }
  | .progress => { pos04SnapshotBridge with runProgress := fun x => min x.eventCount 2 }
  | .writer => { pos04SnapshotBridge with runRecordWriter := fun _ => false }
  | .record => { pos04SnapshotBridge with runRecord := fun _ => 0 }
  | .residue => { pos04SnapshotBridge with runResidue := fun _ => ([], []) }
  | .maintenance => { pos04SnapshotBridge with runMaintenance := fun _ => false }
  | .owner => { pos04SnapshotBridge with runOwner := fun _ => tagCarrierId .source }
  | .enabled => { pos04SnapshotBridge with runEnabled := fun _ => false }
  | .sourceFactor => { pos04SnapshotBridge with runSourceFactor := fun _ => none }
  | .targetFactor => { pos04SnapshotBridge with runTargetFactor := fun _ => none }


theorem pos04_predictive_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .predictive) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .predictive) .predictive
    (bridgeRootRun (pos04ReadoutCorruption .predictive) false (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04SourceSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change PredictiveNow.exit2 ≠ predictiveNow .source (classRepresentative .m3)
  decide

theorem pos04_counter_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .counter) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .counter) .counter
    (bridgeRootRun (pos04ReadoutCorruption .counter) false (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04SourceSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change (2 : Nat) ≠ 3
  decide

theorem pos04_ticks_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .ticks) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .ticks) .ticks
    (bridgeRootRun (pos04ReadoutCorruption .ticks) false (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04SourceSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change (2 : Nat) ≠ 3
  decide

theorem pos04_tickPhase_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .tickPhase) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .tickPhase) .tickPhase
    (bridgeRootRun (pos04ReadoutCorruption .tickPhase) false (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04SourceSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change (0 : Nat) ≠ 1
  decide

theorem pos04_progress_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .progress) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .progress) .progress
    (bridgeRootRun (pos04ReadoutCorruption .progress) false (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04SourceSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change (2 : Nat) ≠ 3
  decide

theorem pos04_writer_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .writer) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .writer) .writer
    (bridgeRootRun (pos04ReadoutCorruption .writer) false (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04SourceSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change false ≠ true
  decide

theorem pos04_record_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .record) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .record) .record
    (bridgeRootRun (pos04ReadoutCorruption .record) false (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04SourceSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change (0 : Nat) ≠ 3
  decide

theorem pos04_enabled_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .enabled) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .enabled) .enabled
    (bridgeRootRun (pos04ReadoutCorruption .enabled) false (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04SourceSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change false ≠ true
  decide

theorem pos04_sourceFactor_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .sourceFactor) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .sourceFactor) .sourceFactor
    (bridgeRootRun (pos04ReadoutCorruption .sourceFactor) false (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04SourceSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change (none : Option KState) ≠ some .p2w1
  decide

theorem pos04_targetFactor_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .targetFactor) := by
  apply bridge_readout_field_update_guard (pos04ReadoutCorruption .targetFactor) .targetFactor
    (bridgeRootRun (pos04ReadoutCorruption .targetFactor) true (.a, .endpoint))
    (by apply FutureClosure.root; change
      (pos04TargetSnapshotRun (.a, .endpoint)) ∈ pos04SnapshotFutureRoots; decide)
    .cw .m3 (by change OutcomeClass.m3 ∈ outcomeClasses; decide)
  change (none : Option KState) ≠ some .p2w1
  decide

theorem pos04_residue_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .residue) := by
  apply bridge_readout_initial_observation_guard (pos04ReadoutCorruption .residue) false
    (.a, .endpoint) (by change ((RouteId.a, SnapshotPosition.endpoint) : SnapshotIndex) ∈ pos04SnapshotBridge.auditFrontier; decide) (fun observation => observation.residue)
  decide

theorem pos04_maintenance_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .maintenance) := by
  apply bridge_readout_initial_observation_guard (pos04ReadoutCorruption .maintenance) false
    (.a, .endpoint) (by change ((RouteId.a, SnapshotPosition.endpoint) : SnapshotIndex) ∈ pos04SnapshotBridge.auditFrontier; decide) (fun observation => observation.maintenance)
  decide

theorem pos04_owner_readout_guard : ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption .owner) := by
  apply bridge_readout_initial_observation_guard (pos04ReadoutCorruption .owner) true
    (.a, .endpoint) (by change ((RouteId.a, SnapshotPosition.endpoint) : SnapshotIndex) ∈ pos04SnapshotBridge.auditFrontier; decide) (fun observation => observation.owner)
  decide

/-- Exhaustive field dispatch, with each case backed by its own corruption
and checked law. A field cannot disappear silently from the guard table. -/
theorem pos04_every_readout_corruption_fails (f : RunReadoutField) :
    ¬ BridgeRunReadoutLaws (pos04ReadoutCorruption f) := by
  cases f with
  | predictive => exact pos04_predictive_readout_guard
  | counter => exact pos04_counter_readout_guard
  | ticks => exact pos04_ticks_readout_guard
  | tickPhase => exact pos04_tickPhase_readout_guard
  | progress => exact pos04_progress_readout_guard
  | writer => exact pos04_writer_readout_guard
  | record => exact pos04_record_readout_guard
  | residue => exact pos04_residue_readout_guard
  | maintenance => exact pos04_maintenance_readout_guard
  | owner => exact pos04_owner_readout_guard
  | enabled => exact pos04_enabled_readout_guard
  | sourceFactor => exact pos04_sourceFactor_readout_guard
  | targetFactor => exact pos04_targetFactor_readout_guard

/-- Rejection propagates to the complete frozen certificate, not just a
standalone diagnostic. The proof parameters are arbitrary if they exist. -/
theorem pos04_corrupt_readout_no_frozen_result (f : RunReadoutField)
    (ha : BridgeAdmissible (pos04ReadoutCorruption f))
    (hl : BridgePrimitiveLaws (pos04ReadoutCorruption f))
    (hd : SnapshotAuditCheck (pos04ReadoutCorruption f)
      (bridgeSnapshotAudit (pos04ReadoutCorruption f)))
    (i : Audited (pos04ReadoutCorruption f).auditFrontier) :
    ¬ FrozenBridgeSnapshotResult (pos04ReadoutCorruption f) ha hl hd i :=
  fun h => pos04_every_readout_corruption_fails f h.readoutLaws

end CSTTT.POS04
