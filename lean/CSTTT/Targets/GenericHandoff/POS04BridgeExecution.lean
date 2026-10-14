import CSTTT.Targets.GenericHandoff.POS04ExecutedCorridor
import CSTTT.Targets.ComputedFIACH.BridgeCoherence

/-! G6d-4b actual execution link for the existing four-snapshot G1c adapter.
Both tags, all four snapshots and every actual history successor are covered.
The old representative-alignment check is retained and used as a proof, never
assumed globally. Actual executions write the actual outcome; future trace
laws use the already-proved exact probability lumping, with no lost branches.

This closes the actual-versus-quotient snapshot link. It is NOT yet the fully
polymorphic extraction of factor/record/route laws from runtime cells, nor an
arbitrary-partial equivalence for the final StrictTemporalLineage readout.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04BridgeExecution
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TransportTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Actual history dynamics; policy is read at the actual current factor. -/
def actualHistory (d : RunInputs6) : Run6 → List KState → Run6
  | x, [] => x
  | x, s::rest => actualHistory d
      (actualUpdate6 d x (historyAction6 d x) (.inK s)) rest

inductive ActualHistoryExecution (d : RunInputs6) : Run6 → List KState → Run6 → Prop where
  | nil (x) : ActualHistoryExecution d x [] x
  | step (x : Run6) (s : KState) (rest : List KState) (last : Run6)
      (supported : ∃ p, (.inK s,p) ∈ actualRows6 d x (historyAction6 d x) ∧ 0 < p)
      (tail : ActualHistoryExecution d
        (actualUpdate6 d x (historyAction6 d x) (.inK s)) rest last) :
      ActualHistoryExecution d x (s::rest) last

/-- This equality needs the actual checked alignment, not just equal M class. -/
theorem step_actual_of_alignment (d : RunInputs6) (x : Run6) (s : KState)
    (h : (historyNext6 d x s).factor = .inK s) :
    historyNext6 d x s = actualUpdate6 d x (historyAction6 d x) (.inK s) := by
  change representative6 d (predictive6 d (.inK s)) = .inK s at h
  simp only [historyNext6,update6,actualUpdate6,h]

private theorem positive_scaled (n : Nat) (h : 0 < n) : (0 : Rat) < (n : Rat)/4 := by
  have hp : (0 : Rat) < (n : Rat) := by exact_mod_cast h
  apply (Rat.lt_div_iff (by decide : (0 : Rat) < 4)).mpr
  simpa only [Rat.zero_mul] using hp

theorem checked_step_has_actual_support (d : RunInputs6) (x : Run6) (s : KState)
    (h : historyStepCheck6 d x s = true) :
    (∃ p, (.inK s,p) ∈ actualRows6 d x (historyAction6 d x) ∧ 0 < p) ∧
    historyNext6 d x s = actualUpdate6 d x (historyAction6 d x) (.inK s) := by
  obtain ⟨hew,hfactor⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hedge,hweight⟩ := Bool.and_eq_true_iff.mp hew
  have hw : weight6 d x (historyAction6 d x) (predictive6 d (.inK s)) > 0 := of_decide_eq_true hweight
  have enabled : enabled6 d x = true := by
    cases he : enabled6 d x
    · simp [weight6,he] at hw
    · rfl
  obtain ⟨⟨o,n⟩,hin,heq,hn⟩ := of_decide_eq_true hedge
  change o = .inK s at heq
  subst o
  refine ⟨⟨(n : Rat)/4,?_,positive_scaled n hn⟩,step_actual_of_alignment d x s (of_decide_eq_true hfactor)⟩
  simp only [actualRows6,enabled,if_true]
  exact List.mem_map_of_mem hin

/-- Every branch in the selected acquisition history is proved supported
and executed with the actual updater. This holds for arbitrary partial data;
completeness is supplied only at the acquisition decoder boundary below. -/
theorem checked_history_actual (d : RunInputs6) (x : Run6) (path : List KState)
    (h : historyExecutionCheck6 d x path = true) :
    executeHistory6 d x path = actualHistory d x path ∧
    ActualHistoryExecution d x path (actualHistory d x path) := by
  induction path generalizing x with
  | nil => exact ⟨rfl,.nil x⟩
  | cons s rest ih =>
    obtain ⟨hs,hr⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hp,he⟩ := checked_step_has_actual_support d x s hs
    rw [he] at hr
    obtain ⟨heq,hex⟩ := ih _ hr
    constructor
    · simp only [executeHistory6,actualHistory,he,heq]
    · exact .step x s rest _ hp hex

def actualSnapshot (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (i : SnapshotIndex) : Run6 :=
  actualHistory (runInputs6 a t) (acquisitionInitialRun a t i.1) (acquisitionExecutionPrefix a t i)

theorem checked_snapshot_actual (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (i : SnapshotIndex)
    (h : acquisitionExecutionAtCheck a t i = true) :
    actualSnapshot a t i = acquisitionSnapshotRun a t i ∧
    ActualHistoryExecution (runInputs6 a t) (acquisitionInitialRun a t i.1)
      (acquisitionExecutionPrefix a t i) (actualSnapshot a t i) := by
  obtain ⟨hrest,he⟩ := Bool.and_eq_true_iff.mp h
  have hr := (Bool.and_eq_true_iff.mp hrest).2
  obtain ⟨ha,hex⟩ := checked_history_actual _ _ _ hr
  have heq : acquisitionExecutedSnapshot a t i = acquisitionSnapshotRun a t i := of_decide_eq_true he
  exact ⟨ha.symm.trans heq,hex⟩

/-- A computed actual-execution readout. It explicitly requires the shared
checked acquisition view, so missing cells cannot support it via defaults. -/
def ActualSnapshots (m : RawLaneModel) : Prop :=
  ∃ a, checkedAcquisition m = some a ∧ ∀ t ∈ tags, ∀ i ∈ acquisitionSnapshotIndices,
    actualSnapshot a t i = acquisitionSnapshotRun a t i ∧
    ActualHistoryExecution (runInputs6 a t) (acquisitionInitialRun a t i.1)
      (acquisitionExecutionPrefix a t i) (actualSnapshot a t i)

theorem execution_implies_actual_snapshots (m : RawLaneModel) (h : AcquisitionExecutionPass m) :
    ActualSnapshots m := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck at h
  split at h
  · contradiction
  · rename_i a ha
    refine ⟨a,ha,?_⟩
    intro t ht i hi
    exact checked_snapshot_actual a t i (List.all_eq_true.mp (List.all_eq_true.mp h t ht) i hi)

/-- The G1c frozen certificate is about these ACTUALLY executed snapshots.
The future equality below holds for every run and every finite action word,
including every actual positive-support branch, not only the audited paths. -/
theorem frozen_bridge_actual_execution (m : RawLaneModel) (h : AcquisitionBridgePass m) :
    ActualSnapshots m ∧
    (∃ ha : BridgeAdmissible (assignmentRawBridge m),
      ∃ hl : BridgePrimitiveLaws (assignmentRawBridge m),
        ∃ hd : SnapshotAuditCheck (assignmentRawBridge m) (bridgeSnapshotAudit (assignmentRawBridge m)),
          ∀ i : Audited (assignmentRawBridge m).auditFrontier,
            FrozenBridgeSnapshotResult (assignmentRawBridge m) ha hl hd i) ∧
    (∀ t : Tag, FullFutureSufficient (actualFuture6 (image m.assignment) t) ∧
      ∀ x word trace, fullFuture (actualFuture6 (image m.assignment) t) x word trace =
        fullFuture (future6 (image m.assignment) t) x word trace) := by
  have hp := acquisition_bridge_checked_parts m h
  refine ⟨execution_implies_actual_snapshots m hp.2.1,acquisition_bridge_frozen m h,?_⟩
  intro t
  exact ⟨accepted_actual_all_words6 (hp.2.2.2.2.2.2.2.2.2.2 t),
    actual_word_law6 _ t (hp.2.2.2.2.2.2.2.2.2.2 t).2.1⟩

/-- Direct negative of the actual-snapshot readout, rather than denial of a
conclusion solely because a sufficient corridor check failed. -/
theorem missing_atomic_no_actual_snapshots (m : RawLaneModel) :
    ¬ ActualSnapshots {m with assignment := put m.assignment .eventTable none} := by
  rintro ⟨a,ha,_⟩
  have he := acquisition_missing_dependency m .eventTable
    (by decide : Cell.eventTable ∈ acquisitionDependencies)
  change checkedAcquisition {m with assignment := put m.assignment .eventTable none} = none at he
  rw [he] at ha
  contradiction

theorem positive_actual_snapshots : ActualSnapshots baseline :=
  execution_implies_actual_snapshots baseline baseline_acquisition_execution

theorem package_control_actual_snapshots : ActualSnapshots packageDeletion :=
  execution_implies_actual_snapshots packageDeletion package_deletion_acquisition_execution

theorem lineage_control_actual_snapshots : ActualSnapshots lineageDeletion :=
  execution_implies_actual_snapshots lineageDeletion lineage_deletion_acquisition_execution

theorem withdrawal_control_actual_snapshots : ActualSnapshots withdrawalDeletion :=
  execution_implies_actual_snapshots withdrawalDeletion withdrawal_deletion_acquisition_execution

theorem reversal_actual_snapshots : ActualSnapshots reversedHistories :=
  execution_implies_actual_snapshots reversedHistories reversed_histories_acquisition_execution

end CSTTT.TargetTheory.GenericHandoff.POS04BridgeExecution
