import CSTTT.Targets.GenericHandoff.PublicRuntime
import CSTTT.Targets.GenericHandoff.POS04RuntimeLineage
import CSTTT.Targets.GenericHandoff.POS04RuntimeExecutionGuards

/-! Exact POS-04 public target/resource/frame equations, for arbitrary partial
assignments. The target-only historical interpreter is NOT replaced by the
dual-tag actual acquisition interpreter. In particular source ticks/funding
are not added to operational autonomy's dependencies. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04PublicRuntime
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04ResourceRuntime
open POS04RegisterDynamics POS04RouteExecution
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def raw (p : Protocol) : PublicRuntime.Raw Cell Cell Value Value Unit Register Register
    FrameValue RegisterValue RegisterValue LaneDisturbance Action Ambient
    CSTTT.POS04.PredictiveNow CSTTT.POS04.PredictiveNow KState KState KState Resource
    (List KState × List EventId) Bool (Tag × Ambient) CSTTT.POS04.Stage EventId RouteId RouteId where
  package := POS04DispatchedStage.raw
  lineage := POS04RuntimeLineage.raw p
  historicalExecution := POS04HistoricalRuntime.execution
  historical := POS04HistoricalRuntime.historical
  runCells := POS04ResourceRuntime.runCells p

theorem autonomy_eq (p : Protocol) : PublicRuntime.autonomy (raw p) = POS04HistoricalRuntime.model p := rfl

theorem target_eq (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    PublicRuntime.target (raw p) a = image a := POS04DispatchedStage.global_eq_image a

theorem lineage_target_eq (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    PublicRuntime.lineageAssignment (raw p) a = image a := target_eq p a

theorem historical_link_eq (p : Protocol) :
    PublicRuntime.historicalLink (raw p) = POS04RuntimeExecutionLink.historicalRaw := rfl

theorem package_iff (m : RawLaneModel) :
    HistoricalPackageRuntime.IntegratedTargetRealization (PublicRuntime.autonomy (raw (protocol m))) m.assignment ↔
      PackageLane m.assignment := POS04HistoricalRuntime.package_readout_iff m

theorem lineage_iff (m : RawLaneModel) :
    RuntimeLineage.StrictTemporalLineage (raw (protocol m)).lineage
      (PublicRuntime.lineageAssignment (raw (protocol m)) m.assignment) ↔
      POS04CompleteLineage.StrictTemporalLineage m := by
  rw [lineage_target_eq]
  exact POS04RuntimeLineage.generic_complete_iff m

/-- The frozen nominal protocol is independently computed, not a supplied game
verdict. Both versions read the exact SAME constructed target. -/
def FullAutonomy (m : RawLaneModel) : Prop :=
  (POS04HistoricalRuntimeProtocol.check m).read (PublicRuntime.target (raw (protocol m)) m.assignment) = some true ∧
    HistoricalPackageRuntime.SparseFullAutonomy (PublicRuntime.autonomy (raw (protocol m))) m.assignment

def OperationalAutonomy (m : RawLaneModel) : Prop :=
  (POS04HistoricalRuntimeProtocol.check m).read (PublicRuntime.target (raw (protocol m)) m.assignment) = some true ∧
    HistoricalPackageRuntime.SparseOperationalAutonomy (PublicRuntime.autonomy (raw (protocol m))) m.assignment

theorem full_iff_af (m : RawLaneModel) : FullAutonomy m ↔ AF m := by
  unfold FullAutonomy
  rw [target_eq,autonomy_eq]
  exact POS04HistoricalSparseEquivalence.full_iff_af m

theorem operational_iff_ao (m : RawLaneModel) : OperationalAutonomy m ↔ AO m := by
  unfold OperationalAutonomy
  rw [target_eq,autonomy_eq]
  exact POS04HistoricalSparseEquivalence.operational_iff_ao m

/-- Shared lineage resources and historical-game resources are IDENTICAL
instructions, with separate execution selection. The target-mode link follows
from lineage's computed completeness, not a supplied coherence flag. -/
theorem coherent_of_lineage (m : RawLaneModel)
    (h : POS04CompleteLineage.StrictTemporalLineage m) :
    PublicRuntime.TargetExecutionCoherent (raw (protocol m)) m.assignment := by
  rw [PublicRuntime.TargetExecutionCoherent,target_eq]
  have hs := (POS04SharedRuntimeLineage.whole_iff m).mpr h
  exact ⟨(POS04SharedRuntimeLineage.actual_runtime_links m hs).2,
    POS04SharedRuntimeLineage.historical_runtime_link m hs⟩

theorem canonical_coherent : PublicRuntime.TargetExecutionCoherent (raw (protocol baseline)) canonical := by
  have h := coherent_of_lineage baseline POS04CompleteLineage.positive
  simpa only [baseline,image_canonical] using h

/-- Named independently defined readouts on the public constructed target. -/
def Package (m : RawLaneModel) : Prop :=
  HistoricalPackageRuntime.IntegratedTargetRealization (PublicRuntime.autonomy (raw (protocol m))) m.assignment

def Lineage (m : RawLaneModel) : Prop :=
  RuntimeLineage.StrictTemporalLineage (raw (protocol m)).lineage
    (PublicRuntime.lineageAssignment (raw (protocol m)) m.assignment)

theorem package_named_iff (m : RawLaneModel) : Package m ↔ IntegratedTargetRealization m := by
  apply (package_iff m).trans
  constructor
  · exact derive_package_lane m
  · intro h
    apply (package_lane_iff m.assignment).mpr
    refine ⟨?_,?_⟩
    · intro k _
      obtain ⟨arrow,_,he,hpresent,_⟩ := h.1 .c1 (swapCell k) (primitive_cells_complete _)
      rw [he,swap_cell_involution] at hpresent
      exact hpresent
    · rw [image_eq_assembled]
      exact h.2.2.2.2

theorem lineage_named_iff (m : RawLaneModel) : Lineage m ↔ POS04CompleteLineage.StrictTemporalLineage m := lineage_iff m

theorem full_named_iff (m : RawLaneModel) : FullAutonomy m ↔ POS04HistoricalSparseEquivalence.FullAutonomy m := by
  unfold FullAutonomy POS04HistoricalSparseEquivalence.FullAutonomy
  rw [target_eq,autonomy_eq]

theorem operational_named_iff (m : RawLaneModel) : OperationalAutonomy m ↔ POS04HistoricalSparseEquivalence.OperationalAutonomy m := by
  unfold OperationalAutonomy POS04HistoricalSparseEquivalence.OperationalAutonomy
  rw [target_eq,autonomy_eq]

/-- AF ⇒ P is disclosed; the package proof in eventual soundness still has its
own independent raw package subcheck. -/
theorem full_implies_package (m : RawLaneModel) (h : FullAutonomy m) : Package m :=
  HistoricalPackageRuntime.sparse_full_implies_package _ _ h.2

theorem O_control_vectors :
    (¬ Package packageDeletion ∧ Lineage packageDeletion ∧ OperationalAutonomy packageDeletion) ∧
    (Package lineageDeletion ∧ ¬ Lineage lineageDeletion ∧ OperationalAutonomy lineageDeletion) ∧
    (Package withdrawalDeletion ∧ Lineage withdrawalDeletion ∧ ¬ OperationalAutonomy withdrawalDeletion) := by
  simp only [package_named_iff,lineage_named_iff,operational_named_iff]
  exact POS04HistoricalSparseFIACH.O_control_vectors

theorem F_control_vectors :
    (¬ Package packageDeletion ∧ Lineage packageDeletion ∧ ¬ FullAutonomy packageDeletion) ∧
    (Package lineageDeletion ∧ ¬ Lineage lineageDeletion ∧ FullAutonomy lineageDeletion) ∧
    (Package withdrawalDeletion ∧ Lineage withdrawalDeletion ∧ ¬ FullAutonomy withdrawalDeletion) := by
  simp only [package_named_iff,lineage_named_iff,full_named_iff]
  exact POS04HistoricalSparseFIACH.F_control_vectors

theorem operational_named_separation :
    (∃ m, ¬ Package m ∧ Lineage m ∧ OperationalAutonomy m) ∧
    (∃ m, Package m ∧ ¬ Lineage m ∧ OperationalAutonomy m) ∧
    (∃ m, Package m ∧ Lineage m ∧ ¬ OperationalAutonomy m) :=
  ⟨⟨packageDeletion,O_control_vectors.1⟩,⟨lineageDeletion,O_control_vectors.2.1⟩,
    ⟨withdrawalDeletion,O_control_vectors.2.2⟩⟩

theorem relabel_vector : Package POS04LineageFutureBoundary.proposal ∧
    ¬ Lineage POS04LineageFutureBoundary.proposal ∧ FullAutonomy POS04LineageFutureBoundary.proposal ∧
    OperationalAutonomy POS04LineageFutureBoundary.proposal := by
  simp only [package_named_iff,lineage_named_iff,full_named_iff,operational_named_iff]
  exact POS04HistoricalSparseFIACH.relabel_vectors

theorem source_recharge_vector : Package POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    ¬ Lineage POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    FullAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    OperationalAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable := by
  simp only [package_named_iff,lineage_named_iff,full_named_iff,operational_named_iff]
  exact POS04HistoricalSparseFIACH.source_recharge_diagnostic

/-- Joint satisfiability on the actual positive assignment; the target span
and game transports are not merely conditional equations with empty domains. -/
theorem positive_readouts : Package baseline ∧ Lineage baseline ∧
    FullAutonomy baseline ∧ OperationalAutonomy baseline := by
  refine ⟨(package_iff baseline).mpr package_lane_positive,
    (lineage_named_iff baseline).mpr POS04CompleteLineage.positive,
    (full_iff_af baseline).mpr baseline_AF,(operational_iff_ao baseline).mpr baseline_AO⟩

theorem protocol_failure_cases (m : RawLaneModel)
    (bad : (POS04HistoricalRuntimeProtocol.check m).read
      (PublicRuntime.target (raw (protocol m)) m.assignment) ≠ some true) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m :=
  ⟨fun h => bad h.1,fun h => bad h.1⟩

/-- A deliberately broken raw execution row is ready but fails the span.
Only the historical row instruction changes; no zero-weight placeholder or
class-representative choice stands in for an actual branch. -/
def emptyHistoricalRows := {raw (protocol baseline) with historicalExecution :=
  {POS04HistoricalRuntime.execution with row := .literal []}}

theorem empty_rows_ready : ExecutionLink.Ready (PublicRuntime.historicalLink emptyHistoricalRows) canonical := by
  have h := POS04RuntimeExecutionLink.historical_ready canonical (canonical_complete _)
  refine ⟨h.1,⟨?_,h.2.1.2⟩,h.2.2⟩
  intro k hk; simp [PublicRuntime.historicalLink,emptyHistoricalRows,Expr.dependencies] at hk

theorem empty_rows_rejected : ¬ PublicRuntime.TargetExecutionCoherent emptyHistoricalRows canonical := by
  apply PublicRuntime.mismatched_historical_rows_rejected emptyHistoricalRows canonical
    (by simpa only [PublicRuntime.target,emptyHistoricalRows,raw,POS04DispatchedStage.global_eq_image,image_canonical] using empty_rows_ready)
    (encode POS04RuntimeExecutionGuards.witness) .nominal .cw
  change [] ≠ ExecutionLink.rows (POS04RuntimeExecutionLink.execution .target) canonical _ _ _
  rw [POS04RuntimeExecutionLink.source_rows canonical (canonical_complete _) .target]
  decide +kernel

/-- Only the historical successor program is replaced. Input dependencies of
its unchanged row remain required; the changed program is separately ready. -/
def identityHistorical := {raw (protocol baseline) with historicalExecution :=
  {POS04HistoricalRuntime.execution with program := fun k => .register k}}

theorem identity_ready : ExecutionLink.Ready (PublicRuntime.historicalLink identityHistorical) canonical := by
  have h := POS04RuntimeExecutionLink.historical_ready canonical (canonical_complete _)
  refine ⟨h.1,⟨h.2.1.1,?_⟩,h.2.2⟩
  intro r k hk; simp [PublicRuntime.historicalLink,identityHistorical,Expr.dependencies] at hk

theorem identity_embedding (x : Registers Register RegisterValue) :
    ExecutionLink.embed (PublicRuntime.historicalLink identityHistorical) canonical identity_ready x =
      frame .target (decodeRun x) := by
  funext k
  exact Option.some.inj (ExecutionLink.embed_equation _ _ identity_ready x k).symm

theorem identity_update (x : Registers Unit FrameValue)
    (d : LaneDisturbance) (act : Action) (o : Ambient) :
    ExecutionLink.update identityHistorical.historicalExecution canonical identity_ready.2.1 x d act o = x := by
  funext k
  exact Option.some.inj (checked_execute_eq identityHistorical.historicalExecution.program canonical
    identity_ready.2.1.2 x (d,act,o) k).symm

theorem identity_successor_rejected : ¬ PublicRuntime.TargetExecutionCoherent identityHistorical canonical := by
  have bad : ¬ ExecutionLink.Pass (PublicRuntime.historicalLink identityHistorical) canonical := by
    apply ExecutionLink.successor_mismatch_rejected _ canonical identity_ready
      (encode POS04RuntimeExecutionGuards.witness) .nominal (by decide) .cw (by decide) (.inK .p2w1) (by decide)
    change ExecutionLink.embed (PublicRuntime.historicalLink identityHistorical) canonical identity_ready
      (ExecutionLink.update (POS04RuntimeExecutionLink.execution .target) canonical identity_ready.1 _ _ _ _) ≠ _
    rw [identity_embedding,POS04RuntimeExecutionLink.source_update canonical (canonical_complete _) .target,
      decode_encode,identity_embedding,decode_encode]
    change frame .target _ ≠ ExecutionLink.update identityHistorical.historicalExecution canonical identity_ready.2.1 _ _ _ _
    rw [identity_update]
    intro eq
    have count := congrArg (fun x : Registers Unit FrameValue => (x ()).2.counter) eq
    change (1 : Nat) = 0 at count
    contradiction
  intro h
  apply bad
  simpa only [PublicRuntime.target,identityHistorical,raw,POS04DispatchedStage.global_eq_image,image_canonical] using h.2

end CSTTT.TargetTheory.GenericHandoff.POS04PublicRuntime
