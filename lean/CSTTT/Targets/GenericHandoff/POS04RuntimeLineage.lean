import CSTTT.Targets.GenericHandoff.RuntimeLineage
import CSTTT.Targets.GenericHandoff.POS04AcquisitionEndpoint
import CSTTT.Targets.GenericHandoff.POS04SharedRuntimeLineage

/-! Exact POS-04 specialization of the polymorphic runtime lineage core.
All partial assignments are covered. The typed acquisition endpoint remains
an explicit separate obligation; it is never inferred from runtime linkage,
route retention, or the weaker legacy lineage predicate. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RuntimeLineage
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04ResourceRuntime
open CSTTT.RecordTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def factor : RuntimeLineage.FactorRaw Cell Value where
  Source := KState
  Target := KState
  SourceAction := Action
  TargetAction := Action
  SourceOutcome := Ambient
  TargetOutcome := Ambient
  History := HistoryId
  Route := RouteId
  Stage := CSTTT.POS04.Stage
  Id := EventId
  Owner := Tag
  sourceEq := inferInstance
  targetEq := inferInstance
  ownerEq := inferInstance
  source := POS04TemporalFactor.schema .source
  target := POS04TemporalFactor.schema .target
  instructions := POS04FactorTransport.binding

def raw (p : Protocol) : RuntimeLineage.Raw Cell Value Unit
    POS04RegisterDynamics.Register POS04RegisterDynamics.Register POS04RouteExecution.FrameValue
    POS04RegisterDynamics.RegisterValue POS04RegisterDynamics.RegisterValue
    LaneDisturbance Action Ambient CSTTT.POS04.PredictiveNow CSTTT.POS04.PredictiveNow
    KState Resource (List KState × List EventId) Bool (Tag × Ambient)
    CSTTT.POS04.Stage EventId RouteId RouteId where
  schema := cfg
  runtime := runtime p
  source := POS04ExecutionFrontier.raw
  target := POS04ReceiverFrontier.raw
  sourceEmbedding := POS04RuntimeExecutionLink.embedding .source
  targetEmbedding := POS04RuntimeExecutionLink.embedding .target
  translation := POS04ExecutionBridge.raw.translation
  maps := POS04ExecutionBridge.raw.maps
  names := POS04ExecutedCorridor.raw.names
  seeds := POS04ExecutedCorridor.raw.seeds
  predictiveCoordinate := POS04ExecutedCorridor.raw.predictiveCoordinate
  historyCoordinate := POS04ExecutedCorridor.raw.historyCoordinate
  routeCoordinate := POS04ExecutedCorridor.raw.routeCoordinate
  endpoint := POS04AcquisitionEndpoint.interface
  factor := factor
  recordSchema := POS04RecordComponent.cfg
  record := POS04RecordComponent.view
  route := POS04RuntimeRoute.instructions

theorem bridge_eq (p : Protocol) : RuntimeLineage.bridge (raw p) = POS04ExecutionBridge.raw := rfl

theorem executed_eq (p : Protocol) : RuntimeLineage.executed (raw p) = POS04ExecutedCorridor.raw := rfl

theorem corridor_eq (p : Protocol) : RuntimeLineage.corridor (raw p) = POS04AcquisitionCorridor.raw := rfl

theorem source_link_eq (p : Protocol) :
    RuntimeLineage.sourceLink (raw p) = POS04RuntimeExecutionLink.raw .source := rfl

theorem target_link_eq (p : Protocol) :
    RuntimeLineage.targetLink (raw p) = POS04RuntimeExecutionLink.raw .target := rfl

theorem factor_iff (m : RawLaneModel) :
    RuntimeLineage.FactorReadout factor (image m.assignment) ↔ POS04CompleteLineage.FactorReadout m :=
  POS04FactorTransport.pass_iff m

/-- Decode presence, then compute arrows: defaults never enter the proof. -/
theorem record_iff (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    RuntimeLineage.RecordReadout (raw p) a ↔ POS04CompleteLineage.RecordReadout a := by
  constructor
  · rintro ⟨d,hd,arrows⟩
    have hc : Complete POS04RecordComponent.view.dependencies a := by
      intro k hk
      cases hm : a k with
      | some v => rfl
      | none =>
        rw [show (raw p).record = POS04RecordComponent.view from rfl,
          POS04RecordComponent.view.missing a k hk hm] at hd
        contradiction
    have he : d = POS04RecordComponent.data a :=
      Option.some.inj (hd.symm.trans (POS04RecordComponent.read_equation a hc))
    subst d
    refine ⟨hc,?_⟩
    simpa only [raw,POS04RecordComponent.transport_equation] using arrows
  · rintro ⟨hc,arrows⟩
    refine ⟨POS04RecordComponent.data a,POS04RecordComponent.read_equation a hc,?_⟩
    simpa only [raw,POS04RecordComponent.transport_equation] using arrows

/-- These extra representation equations are consequences of the complete
route inputs on EVERY partial assignment, not fixed positive adapters. -/
theorem shared_from_route (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (h : RuntimeComponents.RetainedRouteReadout cfg (runtime p) POS04RuntimeRoute.instructions a) :
    RuntimeLineage.SharedExecution (raw p) a := by
  have hc := ((POS04RuntimeRoute.semantic_iff p a).mp h).1
  exact ⟨rfl,rfl,POS04RuntimeExecutionLink.checked a hc .source,
    POS04RuntimeExecutionLink.checked a hc .target⟩

/-- A precise core adapter; the endpoint is not silently erased. -/
theorem core_iff (m : RawLaneModel) : RuntimeLineage.CoreReadout (raw (protocol m)) (image m.assignment) ↔
    POS04CompleteLineage.CorridorReadout (image m.assignment) ∧
    POS04CompleteLineage.SeedReadout (image m.assignment) ∧ POS04CompleteLineage.FactorReadout m ∧
    POS04CompleteLineage.RecordReadout (image m.assignment) ∧
    RuntimeComponents.RetainedRouteReadout cfg (runtime (protocol m)) POS04RuntimeRoute.instructions (image m.assignment) ∧
    ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw (image m.assignment) := by
  constructor
  · rintro ⟨hc,hs,hf,hr,hrt,hx,_⟩
    exact ⟨hc,hs,(factor_iff m).mp hf,(record_iff _ _).mp hr,hrt,hx⟩
  · rintro ⟨hc,hs,hf,hr,hrt,hx⟩
    exact ⟨hc,hs,(factor_iff m).mpr hf,(record_iff _ _).mpr hr,hrt,hx,shared_from_route _ _ hrt⟩

/-- Exact WHOLE readout equivalence, with the still family-specific typed
endpoint explicitly visible. This is not yet a polymorphic endpoint theorem. -/
theorem whole_iff (m : RawLaneModel) :
    (RuntimeLineage.CoreReadout (raw (protocol m)) (image m.assignment) ∧ TypedAcquisitionEndpointPass m) ↔
      POS04SharedRuntimeLineage.StrictTemporalLineage m := by
  rw [core_iff]
  constructor
  · rintro ⟨⟨hc,hs,hf,hr,hrt,hx⟩,he⟩
    exact ⟨hc,hs,hf,hr,he,hrt,hx⟩
  · rintro ⟨hc,hs,hf,hr,he,hrt,hx⟩
    exact ⟨⟨hc,hs,hf,hr,hrt,hx⟩,he⟩

theorem complete_iff (m : RawLaneModel) :
    (RuntimeLineage.CoreReadout (raw (protocol m)) (image m.assignment) ∧ TypedAcquisitionEndpointPass m) ↔
      POS04CompleteLineage.StrictTemporalLineage m :=
  (whole_iff m).trans (POS04SharedRuntimeLineage.whole_iff m)

theorem positive_core : RuntimeLineage.CoreReadout (raw (protocol baseline)) canonical := by
  have h := (whole_iff baseline).mpr POS04SharedRuntimeLineage.positive
  simpa only [show baseline.assignment = canonical from rfl,image_canonical] using h.1

theorem positive_pass : RuntimeLineage.Pass (raw (protocol baseline)) canonical := by
  have hr : RuntimeComponents.RetainedRouteReadout cfg (runtime (protocol baseline))
      POS04RuntimeRoute.instructions canonical := POS04RuntimeRoute.positive _
  refine ⟨POS04AcquisitionCorridor.positive,POS04CompleteLineage.baseline_seed,?_,?_,hr,
    POS04ExecutionBridge.positive,shared_from_route _ _ hr⟩
  · exact POS04FactorTransport.positive
  · exact (record_iff _ _).mpr POS04CompleteLineage.baseline_record

theorem relabel_no_core : ¬ RuntimeLineage.CoreReadout
    (raw (protocol POS04LineageFutureBoundary.proposal)) (image POS04LineageFutureBoundary.proposal.assignment) := by
  intro h
  exact POS04LineageFutureBoundary.no_complete_execution_readout ((core_iff _).mp h).2.2.2.2.2

/-- Missing actual atomic input rejects the semantic core directly. -/
theorem missing_atomic_no_core (m : RawLaneModel) : ¬ RuntimeLineage.CoreReadout
    (raw (protocol m)) (image (put m.assignment .eventTable none)) := by
  apply RuntimeLineage.missing_atomic_no_readout
  have hm : image (put m.assignment .eventTable none) .eventTable = none := by
    simpa only [swapCell] using image_delete_cell m.assignment .eventTable
  simp [raw,POS04ExecutionFrontier.raw,POS04ExecutionFrontier.acquisition,
    POS04ExecutionFrontier.eventView,CellView.read,hm]


/-- The complete family result still exposes its endpoint obligation. -/
def CompleteReadout (m : RawLaneModel) : Prop :=
  RuntimeLineage.CoreReadout (raw (protocol m)) (image m.assignment) ∧ TypedAcquisitionEndpointPass m

theorem complete_named_iff (m : RawLaneModel) : CompleteReadout m ↔
    POS04SharedRuntimeLineage.StrictTemporalLineage m := whole_iff m

theorem O_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ CompleteReadout packageDeletion ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ CompleteReadout lineageDeletion ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ CompleteReadout withdrawalDeletion ∧
      ¬ POS04HistoricalSparseEquivalence.OperationalAutonomy withdrawalDeletion) := by
  have h := POS04SharedRuntimeLineage.O_control_vectors
  exact ⟨⟨h.1.1,(whole_iff _).mpr h.1.2.1,h.1.2.2⟩,
    ⟨h.2.1.1,fun hl => h.2.1.2.1 ((whole_iff _).mp hl),h.2.1.2.2⟩,
    ⟨h.2.2.1,(whole_iff _).mpr h.2.2.2.1,h.2.2.2.2⟩⟩

theorem F_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ CompleteReadout packageDeletion ∧
      ¬ POS04HistoricalSparseEquivalence.FullAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ CompleteReadout lineageDeletion ∧
      POS04HistoricalSparseEquivalence.FullAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ CompleteReadout withdrawalDeletion ∧
      ¬ POS04HistoricalSparseEquivalence.FullAutonomy withdrawalDeletion) := by
  have h := POS04SharedRuntimeLineage.F_control_vectors
  exact ⟨⟨h.1.1,(whole_iff _).mpr h.1.2.1,h.1.2.2⟩,
    ⟨h.2.1.1,fun hl => h.2.1.2.1 ((whole_iff _).mp hl),h.2.1.2.2⟩,
    ⟨h.2.2.1,(whole_iff _).mpr h.2.2.2.1,h.2.2.2.2⟩⟩

theorem operational_named_separation :
    (∃ m, ¬ IntegratedTargetRealization m ∧ CompleteReadout m ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ ¬ CompleteReadout m ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ CompleteReadout m ∧
      ¬ POS04HistoricalSparseEquivalence.OperationalAutonomy m) :=
  ⟨⟨packageDeletion,O_control_vectors.1⟩,⟨lineageDeletion,O_control_vectors.2.1⟩,
    ⟨withdrawalDeletion,O_control_vectors.2.2⟩⟩

theorem relabel_vector : IntegratedTargetRealization POS04LineageFutureBoundary.proposal ∧
    ¬ CompleteReadout POS04LineageFutureBoundary.proposal ∧
    POS04HistoricalSparseEquivalence.FullAutonomy POS04LineageFutureBoundary.proposal ∧
    POS04HistoricalSparseEquivalence.OperationalAutonomy POS04LineageFutureBoundary.proposal := by
  have h := POS04SharedRuntimeLineage.relabel_vector
  exact ⟨h.1,fun hl => h.2.1 ((whole_iff _).mp hl),h.2.2⟩

/-- The endpoint is now a raw component of the generic runtime interface. -/
theorem generic_complete_iff (m : RawLaneModel) :
    RuntimeLineage.StrictTemporalLineage (raw (protocol m)) (image m.assignment) ↔
      POS04CompleteLineage.StrictTemporalLineage m := by
  unfold RuntimeLineage.StrictTemporalLineage
  rw [show (raw (protocol m)).endpoint = POS04AcquisitionEndpoint.interface from rfl,
    POS04AcquisitionEndpoint.readout_iff]
  exact complete_iff m

theorem positive_complete_pass : RuntimeLineage.CompletePass (raw (protocol baseline)) canonical :=
  ⟨positive_pass,POS04AcquisitionEndpoint.positive⟩

theorem endpoint_deletion_no_lineage (m : RawLaneModel) :
    ¬ RuntimeLineage.StrictTemporalLineage (raw (protocol m))
      (image (put m.assignment .eventTable none)) := by
  apply RuntimeLineage.missing_endpoint_no_lineage _ _ .eventTable
  · exact (POS04AcquisitionEndpoint.scope_iff .eventTable).mpr
      (by simp [acquisitionDependencies,phase2Dependencies])
  · simpa only [swapCell] using image_delete_cell m.assignment .eventTable

theorem relabel_no_lineage : ¬ RuntimeLineage.StrictTemporalLineage
    (raw (protocol POS04LineageFutureBoundary.proposal))
      (image POS04LineageFutureBoundary.proposal.assignment) :=
  fun h => relabel_no_core h.1

theorem exit_deleted_no_lineage : ¬ RuntimeLineage.StrictTemporalLineage
    (raw (protocol baseline)) POS04AcquisitionEndpoint.deleteExit :=
  fun h => POS04AcquisitionEndpoint.exit_deleted_no_endpoint h.2

theorem generic_named_iff (m : RawLaneModel) :
    RuntimeLineage.StrictTemporalLineage (raw (protocol m)) (image m.assignment) ↔ CompleteReadout m := by
  unfold RuntimeLineage.StrictTemporalLineage CompleteReadout
  rw [show (raw (protocol m)).endpoint = POS04AcquisitionEndpoint.interface from rfl,
    POS04AcquisitionEndpoint.readout_iff]

theorem generic_O_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧
      RuntimeLineage.StrictTemporalLineage (raw (protocol packageDeletion)) (image packageDeletion.assignment) ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧
      ¬ RuntimeLineage.StrictTemporalLineage (raw (protocol lineageDeletion)) (image lineageDeletion.assignment) ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧
      RuntimeLineage.StrictTemporalLineage (raw (protocol withdrawalDeletion)) (image withdrawalDeletion.assignment) ∧
      ¬ POS04HistoricalSparseEquivalence.OperationalAutonomy withdrawalDeletion) := by
  simp only [generic_named_iff]
  exact O_control_vectors

theorem generic_F_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧
      RuntimeLineage.StrictTemporalLineage (raw (protocol packageDeletion)) (image packageDeletion.assignment) ∧
      ¬ POS04HistoricalSparseEquivalence.FullAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧
      ¬ RuntimeLineage.StrictTemporalLineage (raw (protocol lineageDeletion)) (image lineageDeletion.assignment) ∧
      POS04HistoricalSparseEquivalence.FullAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧
      RuntimeLineage.StrictTemporalLineage (raw (protocol withdrawalDeletion)) (image withdrawalDeletion.assignment) ∧
      ¬ POS04HistoricalSparseEquivalence.FullAutonomy withdrawalDeletion) := by
  simp only [generic_named_iff]
  exact F_control_vectors

end CSTTT.TargetTheory.GenericHandoff.POS04RuntimeLineage
