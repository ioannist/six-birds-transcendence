import CSTTT.Targets.GenericHandoff.RawHandoff
import CSTTT.Targets.GenericHandoff.POS04PresentationCoherence

/-! Owning POS-04 specialization. Decoder and named lane adapters quantify over
ALL partial assignments, not canonical truth alone. Historical game adapters
are explicitly qualified by the frozen, independently computed nominal protocol;
that protocol is not silently supplied as a generic acceptance flag. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RawHandoff
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04ResourceRuntime
open POS04RegisterDynamics POS04RouteExecution
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

abbrev Model := OwningHandoff.RawHandoff Cell Cell Value Value Unit Register Register
  FrameValue RegisterValue RegisterValue KState Action Ambient RouteId HistoryId RouteId
  CSTTT.POS04.Stage EventId Tag LaneDisturbance CSTTT.POS04.PredictiveNow CSTTT.POS04.PredictiveNow
  KState Resource (Tag × Ambient)

def raw (p : Protocol) : Model where
  sourceClauses := POS04Dispatcher.package .source
  package := POS04DispatchedStage.raw
  frames := POS04PresentationCoherence.frames
  schema := cfg
  runtime := runtime p
  sourceEmbedding := POS04RuntimeExecutionLink.embedding .source
  targetEmbedding := POS04RuntimeExecutionLink.embedding .target
  translation := POS04ExecutionBridge.raw.translation
  maps := POS04ExecutionBridge.raw.maps
  names := POS04ExecutedCorridor.raw.names
  seeds := POS04ExecutedCorridor.raw.seeds
  predictiveCoordinate := POS04ExecutedCorridor.raw.predictiveCoordinate
  historyCoordinate := POS04ExecutedCorridor.raw.historyCoordinate
  routeCoordinate := POS04ExecutedCorridor.raw.routeCoordinate
  route := POS04RuntimeRoute.instructions
  historicalExecution := POS04HistoricalRuntime.execution
  historical := POS04HistoricalRuntime.historical
  runCells := POS04ResourceRuntime.runCells p

theorem target_eq (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    OwningHandoff.target (raw p) a = image a := POS04DispatchedStage.global_eq_image a

theorem autonomy_eq (p : Protocol) :
    OwningHandoff.autonomy (raw p) = POS04HistoricalRuntime.model p := rfl

theorem factor_decoder (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    ((OwningHandoff.factor (raw p)).instructions.source.read a =
      POS04FactorTransport.binding.source.read a) ∧
    ((OwningHandoff.factor (raw p)).instructions.target.read a =
      POS04FactorTransport.binding.target.read a) :=
  ⟨POS04PresentationCoherence.factor_decoder a .source,
    POS04PresentationCoherence.factor_decoder a .target⟩

theorem factor_iff (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    RuntimeLineage.FactorReadout (OwningHandoff.factor (raw p)) a ↔
      RuntimeLineage.FactorReadout POS04RuntimeLineage.factor a := by
  change (∃ ds dt maps, _ ∧ _ ∧ _ ∧ _) ↔ (∃ ds dt maps, _ ∧ _ ∧ _ ∧ _)
  simp only [(factor_decoder p a).1,(factor_decoder p a).2]
  rfl

/-- Derived endpoint extraction is exactly the declared raw endpoint interface. -/
theorem endpoint_eq (p : Protocol) :
    OwningHandoff.endpoint (raw p) = POS04AcquisitionEndpoint.interface := rfl

/-- Hypothesis-free whole semantic adapter. The factor decoder equality is
used explicitly; no fixed positive factor/corridor is conjoined. -/
theorem lineage_readout_iff (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    RuntimeLineage.StrictTemporalLineage (OwningHandoff.lineage (raw p)) a ↔
      RuntimeLineage.StrictTemporalLineage (POS04RuntimeLineage.raw p) a := by
  unfold RuntimeLineage.StrictTemporalLineage RuntimeLineage.CoreReadout
  rw [show (OwningHandoff.lineage (raw p)).factor = OwningHandoff.factor (raw p) from rfl,
    factor_iff p a]
  rfl

theorem lineage_pass_iff (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    RuntimeLineage.CompletePass (OwningHandoff.lineage (raw p)) a ↔
      RuntimeLineage.CompletePass (POS04RuntimeLineage.raw p) a := by
  unfold RuntimeLineage.CompletePass RuntimeLineage.Pass
  rw [show (OwningHandoff.lineage (raw p)).factor = OwningHandoff.factor (raw p) from rfl,
    factor_iff p a]
  rfl

theorem lineage_iff (m : RawLaneModel) :
    OwningHandoff.StrictTemporalLineage (raw (protocol m)) m.assignment ↔
      POS04CompleteLineage.StrictTemporalLineage m := by
  unfold OwningHandoff.StrictTemporalLineage
  rw [target_eq,lineage_readout_iff]
  exact POS04RuntimeLineage.generic_complete_iff m

theorem package_iff (m : RawLaneModel) :
    OwningHandoff.IntegratedTargetRealization (raw (protocol m)) m.assignment ↔
      IntegratedTargetRealization m := POS04PublicRuntime.package_named_iff m

/-- Exact nominal-protocol qualified autonomy, on every partial assignment. -/
def FullAutonomy (m : RawLaneModel) : Prop :=
  (POS04HistoricalRuntimeProtocol.check m).read (OwningHandoff.target (raw (protocol m)) m.assignment) = some true ∧
    OwningHandoff.PostWithdrawalFullAutonomy (raw (protocol m)) m.assignment

def OperationalAutonomy (m : RawLaneModel) : Prop :=
  (POS04HistoricalRuntimeProtocol.check m).read (OwningHandoff.target (raw (protocol m)) m.assignment) = some true ∧
    OwningHandoff.PostWithdrawalOperationalAutonomy (raw (protocol m)) m.assignment

theorem full_iff_af (m : RawLaneModel) : FullAutonomy m ↔ AF m := by
  unfold FullAutonomy
  rw [target_eq]
  exact POS04HistoricalSparseEquivalence.full_iff_af m

theorem operational_iff_ao (m : RawLaneModel) : OperationalAutonomy m ↔ AO m := by
  unfold OperationalAutonomy
  rw [target_eq]
  exact POS04HistoricalSparseEquivalence.operational_iff_ao m

theorem ownership : OwningHandoff.OwnershipCheck (raw (protocol baseline)) := by
  refine ⟨?_,?_,rfl,rfl⟩
  · intro s t h
    cases s <;> cases t <;> first | rfl | (cases h)
  · change tagCarrierId .source ≠ tagCarrierId .target
    decide

theorem ownership_every_protocol (p : Protocol) : OwningHandoff.OwnershipCheck (raw p) := ownership

theorem coherence_of_lineage (m : RawLaneModel) (h : POS04CompleteLineage.StrictTemporalLineage m) :
    OwningHandoff.Coherence (raw (protocol m)) m.assignment := by
  refine ⟨ownership_every_protocol _,POS04PresentationCoherence.frame_schema_checked,rfl,?_,?_⟩
  · rw [target_eq]
    exact POS04PresentationCoherence.checked_of_lineage m h
  · exact POS04PublicRuntime.coherent_of_lineage m h

/-- Positive semantic readouts are jointly inhabited. The nominal protocol
remains explicitly present in the exact family autonomy equivalences. -/
theorem positive_readouts :
    OwningHandoff.IntegratedTargetRealization (raw (protocol baseline)) canonical ∧
    OwningHandoff.StrictTemporalLineage (raw (protocol baseline)) canonical ∧
    FullAutonomy baseline ∧ OperationalAutonomy baseline := by
  exact ⟨(package_iff baseline).mpr (derive_package_lane baseline package_lane_positive),
    (lineage_iff baseline).mpr POS04CompleteLineage.positive,
    (full_iff_af baseline).mpr baseline_AF,(operational_iff_ao baseline).mpr baseline_AO⟩

/-- Direct semantic deletion, not a failure inferred from a sufficient gate. -/
theorem endpoint_deletion_no_lineage (m : RawLaneModel) :
    ¬ OwningHandoff.StrictTemporalLineage (raw (protocol m)) (put m.assignment .eventTable none) := by
  unfold OwningHandoff.StrictTemporalLineage
  rw [target_eq,lineage_readout_iff]
  exact POS04RuntimeLineage.endpoint_deletion_no_lineage m

theorem relabel_no_lineage :
    ¬ OwningHandoff.StrictTemporalLineage (raw (protocol POS04LineageFutureBoundary.proposal))
      POS04LineageFutureBoundary.proposal.assignment :=
  fun h => POS04HistoricalSparseFIACH.relabel_vectors.2.1 ((lineage_iff _).mp h)

abbrev Package (m : RawLaneModel) := OwningHandoff.IntegratedTargetRealization (raw (protocol m)) m.assignment
abbrev Lineage (m : RawLaneModel) := OwningHandoff.StrictTemporalLineage (raw (protocol m)) m.assignment
abbrev FullGame (m : RawLaneModel) := OwningHandoff.PostWithdrawalFullAutonomy (raw (protocol m)) m.assignment
abbrev OperationalGame (m : RawLaneModel) := OwningHandoff.PostWithdrawalOperationalAutonomy (raw (protocol m)) m.assignment

/-- Semantic autonomy negatives do NOT follow merely from nominal protocol
failure. This direct control fails resource closure at EVERY run. -/
theorem withdrawal_no_games : ¬ FullGame withdrawalDeletion ∧ ¬ OperationalGame withdrawalDeletion := by
  have bad := POS04HistoricalRuntime.withdrawal_no_games withdrawalDeletion rfl
  exact ⟨fun h => bad.1 (HistoricalPackageRuntime.sparse_full_implies_support_only _ _ h),
    fun h => bad.2 (HistoricalPackageRuntime.sparse_operational_implies_support_only _ _ h)⟩

theorem O_control_vectors :
    (¬ Package packageDeletion ∧ Lineage packageDeletion ∧ OperationalGame packageDeletion) ∧
    (Package lineageDeletion ∧ ¬ Lineage lineageDeletion ∧ OperationalGame lineageDeletion) ∧
    (Package withdrawalDeletion ∧ Lineage withdrawalDeletion ∧ ¬ OperationalGame withdrawalDeletion) := by
  have h := POS04PublicRuntime.O_control_vectors
  exact ⟨⟨h.1.1,(lineage_iff _).mpr ((POS04PublicRuntime.lineage_named_iff _).mp h.1.2.1),h.1.2.2.2⟩,
    ⟨h.2.1.1,fun hl => h.2.1.2.1 ((POS04PublicRuntime.lineage_named_iff _).mpr ((lineage_iff _).mp hl)),h.2.1.2.2.2⟩,
    ⟨h.2.2.1,(lineage_iff _).mpr ((POS04PublicRuntime.lineage_named_iff _).mp h.2.2.2.1),withdrawal_no_games.2⟩⟩

theorem F_control_vectors :
    (¬ Package packageDeletion ∧ Lineage packageDeletion ∧ ¬ FullGame packageDeletion) ∧
    (Package lineageDeletion ∧ ¬ Lineage lineageDeletion ∧ FullGame lineageDeletion) ∧
    (Package withdrawalDeletion ∧ Lineage withdrawalDeletion ∧ ¬ FullGame withdrawalDeletion) := by
  have h := POS04PublicRuntime.F_control_vectors
  exact ⟨⟨h.1.1,(lineage_iff _).mpr ((POS04PublicRuntime.lineage_named_iff _).mp h.1.2.1),
      fun hg => h.1.1 (OwningHandoff.full_autonomy_implies_package _ _ hg)⟩,
    ⟨h.2.1.1,fun hl => h.2.1.2.1 ((POS04PublicRuntime.lineage_named_iff _).mpr ((lineage_iff _).mp hl)),h.2.1.2.2.2⟩,
    ⟨h.2.2.1,(lineage_iff _).mpr ((POS04PublicRuntime.lineage_named_iff _).mp h.2.2.2.1),withdrawal_no_games.1⟩⟩

/-- Three logically independent controls on the GENERIC named readouts,
including direct game rejection for withdrawal (no gate-negation inference). -/
theorem temporalFIACH_three_lane_separation :
    (∃ m : Model, ∃ a, ¬ OwningHandoff.IntegratedTargetRealization m a ∧
      OwningHandoff.StrictTemporalLineage m a ∧ OwningHandoff.PostWithdrawalOperationalAutonomy m a) ∧
    (∃ m : Model, ∃ a, OwningHandoff.IntegratedTargetRealization m a ∧
      ¬ OwningHandoff.StrictTemporalLineage m a ∧ OwningHandoff.PostWithdrawalOperationalAutonomy m a) ∧
    (∃ m : Model, ∃ a, OwningHandoff.IntegratedTargetRealization m a ∧
      OwningHandoff.StrictTemporalLineage m a ∧ ¬ OwningHandoff.PostWithdrawalOperationalAutonomy m a) :=
  ⟨⟨raw (protocol packageDeletion),packageDeletion.assignment,O_control_vectors.1⟩,
    ⟨raw (protocol lineageDeletion),lineageDeletion.assignment,O_control_vectors.2.1⟩,
    ⟨raw (protocol withdrawalDeletion),withdrawalDeletion.assignment,O_control_vectors.2.2⟩⟩

theorem positive_F : OwningHandoff.HandoffPass_F (raw (protocol baseline)) canonical := by
  refine ⟨(POS04Dispatcher.package_accept_iff canonical .source).mpr
    (canonical_assigned_package .source),coherence_of_lineage baseline POS04CompleteLineage.positive,
    POS04DispatchedStage.positive,?_,?_⟩
  · rw [target_eq,image_canonical]
    exact (lineage_pass_iff _ _).mpr POS04RuntimeLineage.positive_complete_pass
  · exact (OwningHandoff.full_subcheck_iff _ _).mpr positive_readouts.2.2.1.2

theorem positive_O : OwningHandoff.HandoffPass_O (raw (protocol baseline)) canonical := by
  refine ⟨(POS04Dispatcher.package_accept_iff canonical .source).mpr
    (canonical_assigned_package .source),coherence_of_lineage baseline POS04CompleteLineage.positive,
    POS04DispatchedStage.positive,?_,?_⟩
  · rw [target_eq,image_canonical]
    exact (lineage_pass_iff _ _).mpr POS04RuntimeLineage.positive_complete_pass
  · exact (OwningHandoff.operational_subcheck_iff _ _).mpr positive_readouts.2.2.2.2

/-- Unqualified generic games also preserve the two acquisition diagnostics:
source-past solvency/ticks are NOT autonomy's historical support dependency. -/
theorem source_recharge_vector : Package POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    ¬ Lineage POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    FullGame POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    OperationalGame POS04ReceiverResetProjection.sourceRechargeUnavailable := by
  have h := POS04PublicRuntime.source_recharge_vector
  exact ⟨h.1,fun hl => h.2.1 ((POS04PublicRuntime.lineage_named_iff _).mpr ((lineage_iff _).mp hl)),h.2.2.1.2,h.2.2.2.2⟩

theorem relabel_vector : Package POS04LineageFutureBoundary.proposal ∧
    ¬ Lineage POS04LineageFutureBoundary.proposal ∧
    FullGame POS04LineageFutureBoundary.proposal ∧ OperationalGame POS04LineageFutureBoundary.proposal := by
  have h := POS04PublicRuntime.relabel_vector
  exact ⟨h.1,relabel_no_lineage,h.2.2.1.2,h.2.2.2.2⟩

theorem missing_past_ticks_operational : OperationalGame POS04RuntimeEquivalenceBoundary.missingPastTicks :=
  POS04HistoricalSparseFIACH.missing_past_ticks_diagnostic.2.2

theorem duplicate_event_operational : OperationalGame POS04HistoricalDuplicateEvents.diagnostic :=
  ((operational_iff_ao _).mpr POS04HistoricalDuplicateEvents.legacy_ao_accepts).2

theorem missing_past_ticks_full_rejected : ¬ FullGame POS04RuntimeEquivalenceBoundary.missingPastTicks := by
  intro hg
  have hp : (POS04HistoricalRuntimeProtocol.check POS04RuntimeEquivalenceBoundary.missingPastTicks).read
      (OwningHandoff.target (raw (protocol POS04RuntimeEquivalenceBoundary.missingPastTicks))
        POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment) = some true := by
    rw [target_eq]
    exact POS04HistoricalRuntimeProtocol.missing_past_ticks_protocol
  exact POS04HistoricalSparseFIACH.missing_past_ticks_diagnostic.1 ⟨hp,hg⟩

/-- Protocol failure is matched by the exact family wrappers, never confused
with failure of a bare game readout. -/
theorem protocol_failure_cases (m : RawLaneModel)
    (bad : (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) ≠ some true) :
    (¬ FullAutonomy m ∧ ¬ AF m) ∧ (¬ OperationalAutonomy m ∧ ¬ AO m) := by
  have h := POS04HistoricalSparseEquivalence.protocol_failure m bad
  simpa only [FullAutonomy,OperationalAutonomy,target_eq,
    POS04HistoricalSparseEquivalence.FullAutonomy,POS04HistoricalSparseEquivalence.OperationalAutonomy,
    POS04HistoricalEntryEquivalence.model,autonomy_eq] using h

/-- One raw owner change, with the remaining recipe/cell/frame fields intact. -/
def wrongOwner : Model :=
  {raw (protocol baseline) with schema := {cfg with target := tagCarrierId .source}}

theorem wrong_owner_rejected : ¬ OwningHandoff.HandoffPass_F wrongOwner canonical ∧
    ¬ OwningHandoff.HandoffPass_O wrongOwner canonical :=
  OwningHandoff.wrong_target_owner_no_pass _ _ (by change tagCarrierId .source ≠ tagCarrierId .target; decide)

end CSTTT.TargetTheory.GenericHandoff.POS04RawHandoff
