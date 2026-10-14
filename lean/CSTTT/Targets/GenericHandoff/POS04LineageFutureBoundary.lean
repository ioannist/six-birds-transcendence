import CSTTT.Targets.GenericHandoff.POS04SemanticExecution

/-! Direct arbitrary-assignment regression for the pending whole-lineage
adapter. The mutation relabels the lethal p2w0 outcome to lethal p5w1, ONLY
on p2w1's noncanonical cw row, preserving each existing probability numerator.
The original source namespace is edited; staging makes this the target row.
Canonical policy rows, acquisition history, ledger, events and route register
remain unchanged. This is a sensitivity proposal, not a new positive model.

The old finite bridge action check queries only destinations IN K. Both lethal
outcomes are outside K and have the same hazard Boolean, so the old class/map
and frozen-snapshot checks do not detect their different full future readouts.
The complete semantic execution readout DOES detect the actual branch weight
change. No failed sufficient gate is used to deny the semantic conclusion.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04LineageFutureBoundary
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TransportTheory
open RegisterInterpreter POS04RegisterDynamics
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def relabel (s : KState) (act : Action) : List (Ambient × Nat) :=
  if s = .p2w1 ∧ act = .cw then
    (actionRow .source s act).map (fun e => (if e.1 = .p2w0 then .p5w1 else e.1,e.2))
  else actionRow .source s act

def proposal : RawLaneModel :=
  {baseline with assignment := (put canonical (.rows .source) (some relabel))}

theorem noncanonical_intervention : canonicalAction .p2w1 ≠ Action.cw := by decide
theorem unchanged_policy_rows (s : KState) : relabel s (canonicalAction s) = canonicalRow s := by
  cases s <;> decide +kernel

theorem staged_target_relabel : image proposal.assignment (.rows .target) = some relabel := rfl
theorem staged_source_unchanged : image proposal.assignment (.rows .source) = canonical (.rows .source) := rfl

theorem legacy_gate_accepts : LineageLane proposal := by
  unfold LineageLane
  decide +kernel

theorem legacy_named_readout_accepts : ComputedFIACH.StrictTemporalLineage proposal :=
  derive_lineage_lane proposal legacy_gate_accepts

def start : Run6 := acquisitionInitialRun (image proposal.assignment) .source .a
def afterFirst : Run6 := actualUpdate6 (runInputs6 (image proposal.assignment) .source) start .cw (.inK .p2w1)

theorem source_complete : Complete POS04ExecutionFrontier.dependencies (image proposal.assignment) := by
  intro k hk
  cases k with
  | rows t => cases t <;> rfl
  | lower t => cases t <;> rfl
  | protocols t => cases t <;> rfl
  | ticks t => cases t <;> rfl
  | joint t => cases t <;> rfl
  | resources t => cases t <;> rfl
  | _ => rfl

theorem after_first_is_audit_snapshot :
    ExecutionFrontier.snapshot POS04ExecutionFrontier.raw (image proposal.assignment)
      (POS04ExecutionFrontier.ready _ source_complete) (.a,1) = encode afterFirst := by
  unfold ExecutionFrontier.snapshot
  rw [POS04ExecutionFrontier.initial_eq _ source_complete]
  change AcquisitionExecution.foldHistory POS04ExecutionFrontier.acquisition (image proposal.assignment) _
    (encode start) [(.nominal,.cw,.inK .p2w1)] = encode afterFirst
  rw [POS04ExecutedCorridor.fold_equation _ source_complete]
  rfl

/-- This is a supported audited source step, not a zero-probability artefact. -/
theorem first_step_probability : actualWeight6 (runInputs6 (image proposal.assignment) .source)
    start .cw (.inK .p2w1) = 1 := by decide +kernel

theorem after_first_in_closure : POS04SemanticExecution.Closure (image proposal.assignment) afterFirst := by
  apply FutureClosure.step (a := (LaneDisturbance.nominal,Action.cw)) (o := Ambient.inK .p2w1)
  · apply FutureClosure.root
    apply List.mem_map.mpr
    exact ⟨(.a,1),by decide,rfl⟩
  · decide

theorem actual_branch_difference :
    actualWeight6 (runInputs6 (image proposal.assignment) .target) afterFirst .cw .p2w0 = 0 ∧
    actualWeight6 (runInputs6 (image proposal.assignment) .source) afterFirst .cw .p2w0 = 1 := by
  decide +kernel

theorem no_semantic_transport : ¬ POS04SemanticExecution.TransportLaws (image proposal.assignment) := by
  rintro ⟨_,_,hrows,_⟩
  have he := hrows afterFirst after_first_in_closure .cw .p2w0
  rw [actual_branch_difference.1,actual_branch_difference.2] at he
  contradiction

theorem no_complete_execution_readout :
    ¬ ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw (image proposal.assignment) := by
  intro h
  exact no_semantic_transport ((POS04SemanticExecution.semantic_bridge_iff _).mp h).2.2

/-- Consequently the old named predicate cannot be the complete executed
bridge readout on arbitrary assignments. It must be retained as weaker legacy
evidence when the stronger whole-lineage adapter is assembled. -/
theorem legacy_readout_does_not_imply_complete_bridge :
    ¬ (∀ m : RawLaneModel, ComputedFIACH.StrictTemporalLineage m →
      ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw (image m.assignment)) := by
  intro h
  exact no_complete_execution_readout (h proposal legacy_named_readout_accepts)

end CSTTT.TargetTheory.GenericHandoff.POS04LineageFutureBoundary
