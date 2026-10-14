import CSTTT.Targets.GenericHandoff.FramePresentation
import CSTTT.Targets.GenericHandoff.POS04PublicRuntime
import CSTTT.Targets.GenericHandoff.POS04TemporalCoherence

/-! TTH-06 public presentation receipts on arbitrary partial POS-04 assignments.
The canonical factor projection uses the SAME typed primitive views as the
closed C6 rule and endpoint decoder. Rows, complete updates and all observed
fields are linked at every run by POS04TemporalCoherence.laws. Event structural
fields use priority lookup on all assignments, including duplicate IDs.
Unit record increments agree with the stage clock only on certified strict
events; no unregistered protocol restriction is imposed. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04PresentationCoherence
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04ResourceRuntime
open POS04RegisterDynamics
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem factor_projection (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    PresentationCoherence.factor (POS04TemporalFactor.raw (runInputs6 a tag) tag) =
      POS04FactorTransport.data a tag := rfl

/-- The minimal factor decoder retains its exact seven-cell dependency scope;
missing unrelated temporal inputs do not silently add a protocol condition. -/
theorem factor_decoder (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    (PresentationCoherence.factorView (POS04TemporalFactor.bindings tag)).read a =
      (POS04FactorTransport.view tag).read a := by
  simp [PresentationCoherence.factorView,POS04TemporalFactor.bindings,POS04FactorTransport.view,
    StaticView.read,StaticView.ofCell,Expr.eval]
  cases a (Cell.rows tag) <;> simp_all
  cases a Cell.positions <;> simp_all
  cases a Cell.hazards <;> simp_all
  cases a Cell.policy <;> simp_all
  cases a (Cell.ticks tag) <;> simp_all
  cases a (Cell.resources tag) <;> simp_all
  cases a Cell.maintenance <;> simp_all

theorem endpoint_source_primitives : POS04AcquisitionEndpoint.bindings.source =
    (POS04TemporalCoherence.raw .source).bindings := rfl

theorem endpoint_target_primitives : POS04AcquisitionEndpoint.bindings.target =
    (POS04TemporalCoherence.raw .target).bindings := rfl

theorem package_target_primitives :
    POS04DispatchedStage.raw.clauses.rule .c6 = TemporalRuntimeCoherence.rule (POS04TemporalCoherence.raw .target) := rfl

theorem package_source_primitives :
    (POS04Dispatcher.package .source).rule .c6 = TemporalRuntimeCoherence.rule (POS04TemporalCoherence.raw .source) := rfl

/-- Exact frame programs/rows, independent of acceptance and at all contexts. -/
theorem source_program (p : Protocol) : (POS04TemporalCoherence.raw .source).runtime.program =
    (POS04PublicRuntime.raw p).lineage.source.acquisition.execution.program := rfl

theorem target_program (p : Protocol) : (POS04TemporalCoherence.raw .target).runtime.program =
    (POS04PublicRuntime.raw p).lineage.target.acquisition.execution.program := rfl

theorem source_rows (p : Protocol) : (POS04TemporalCoherence.raw .source).runtime.row =
    (POS04PublicRuntime.raw p).lineage.source.acquisition.execution.row := rfl

theorem target_rows (p : Protocol) : (POS04TemporalCoherence.raw .target).runtime.row =
    (POS04PublicRuntime.raw p).lineage.target.acquisition.execution.row := rfl

/-- Decode first. This is an interface equation on EVERY partial assignment,
not an assertion that all partial assignments contain an endpoint. -/
theorem endpoint_factor (a : CSTTT.POS04.Assigned.Assignment)
    (d : AcquisitionEndpoint.Data KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag)
    (hd : AcquisitionEndpoint.decoded POS04AcquisitionEndpoint.bindings a = some d) :
    (POS04FactorTransport.view .source).read a = some (PresentationCoherence.factor d.source) ∧
    (POS04FactorTransport.view .target).read a = some (PresentationCoherence.factor d.target) := by
  unfold AcquisitionEndpoint.decoded at hd
  cases hs : TemporalFactorCells.decoded POS04AcquisitionEndpoint.bindings.source a <;> simp_all
  cases ht : TemporalFactorCells.decoded POS04AcquisitionEndpoint.bindings.target a <;> simp_all
  cases he : POS04AcquisitionEndpoint.bindings.events.read a <;> simp_all
  cases hr : POS04AcquisitionEndpoint.bindings.receiver.read a <;> simp_all
  cases hd
  constructor
  · rw [← factor_decoder]
    exact PresentationCoherence.factor_decoded _ _ _ hs
  · rw [← factor_decoder]
    exact PresentationCoherence.factor_decoded _ _ _ ht

/-- ALL-run simulation: actual rows, every ambient successor, observer,
absolute ticks, writer, and every factor root. No source funding premise is
introduced into the historical autonomy decoder. -/
theorem runtime_laws (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : TemporalRuntimeCoherence.Ready (POS04TemporalCoherence.raw tag) a) :
    TemporalRuntimeCoherence.Laws (POS04TemporalCoherence.raw tag) a h :=
  POS04TemporalCoherence.laws a tag h

theorem record_laws (a : CSTTT.POS04.Assigned.Assignment) :
    PresentationCoherence.RecordLaws (POS04AcquisitionEndpoint.data a)
      (POS04RecordComponent.data a) stages.idxOf := by
  refine ⟨?_,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · intro i
    simp only [POS04RecordComponent.data,AcquisitionEndpoint.event,POS04AcquisitionEndpoint.data,
      List.find?_map,Function.comp_def,POS04AcquisitionEndpoint.eventMap,Option.map_map]
    rfl
  · simp only [POS04AcquisitionEndpoint.data,POS04TemporalFactor.raw,List.map_map]
    rfl
  · simp only [POS04AcquisitionEndpoint.data,POS04TemporalFactor.raw,List.map_map]
    rfl

theorem record_increment (a : CSTTT.POS04.Assigned.Assignment) (i : EventId)
    (e : AcquisitionExecution.Event CSTTT.POS04.Stage)
    (_he : (POS04RecordComponent.data a).events i = some e)
    (hs : RecordComponent.strict (POS04RecordComponent.data a) e = true) :
    e.orderAdvance > 0 ∧ stages.idxOf e.toStage = stages.idxOf e.fromStage + e.orderAdvance :=
  PresentationCoherence.record_increment _ e hs

/-- The receiver frame is exactly the temporal run projection. All coordinates
are preserved, not just M-class or endpoint equality. -/
theorem frame_projection (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : TemporalRuntimeCoherence.Ready (POS04TemporalCoherence.raw tag) a)
    (x : Registers Register RegisterValue) :
    TemporalRuntimeCoherence.project (POS04TemporalCoherence.raw tag) a h x =
      POS04TemporalFactor.encodeRun (decodeRun x) := POS04TemporalCoherence.project_eq a tag h x

/-- Raw probability, policy, tick, resource/owner and hazard primitives read
by factor transport are the endpoint and C6 primitives, not independent copies. -/
theorem endpoint_factor_predictive (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (s : KState) :
    FactorTransport.classOf (POS04TemporalFactor.schema tag) (POS04FactorTransport.data a tag) s =
      ProfileRules.predictive (TemporalFactorRules.profile (POS04TemporalFactor.schema tag)
        (POS04TemporalFactor.raw (runInputs6 a tag) tag)) s := rfl


def raw : PresentationCoherence.Raw Cell Value Register Register RegisterValue RegisterValue
    KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag LaneDisturbance where
  source := POS04TemporalCoherence.raw .source
  target := POS04TemporalCoherence.raw .target
  events := POS04AcquisitionEndpoint.bindings.events
  receiver := POS04AcquisitionEndpoint.bindings.receiver
  entry := .sourceLive
  exit := .targetExit
  exitEvent := .exit
  fallback := .p0w0
  rowScale := 4
  transfer := id
  clock := stages.idxOf
  factorMaps := POS04FactorTransport.binding.maps
  record := POS04RecordComponent.view

theorem endpoint_schema : PresentationCoherence.endpointSchema raw = POS04AcquisitionEndpoint.cfg := rfl
theorem endpoint_bindings : PresentationCoherence.endpointBindings raw = POS04AcquisitionEndpoint.bindings := rfl

theorem endpoint_complete (a : CSTTT.POS04.Assigned.Assignment)
    (hd : ∃ d, AcquisitionEndpoint.decoded POS04AcquisitionEndpoint.bindings a = some d) :
    Complete acquisitionDependencies a := by
  obtain ⟨d,hd⟩ := hd
  intro k hk
  cases hm : a k with
  | some v => rfl
  | none =>
    rw [AcquisitionEndpoint.missing_input _ a k ((POS04AcquisitionEndpoint.scope_iff k).mpr hk) hm] at hd
    contradiction

/-- Every partial assignment which contains the endpoint and record inputs
has coherent presentations. Clause acceptance is NOT needed to prove these
raw interpretation equations. -/
theorem checked (a : CSTTT.POS04.Assigned.Assignment)
    (he : ∃ d, AcquisitionEndpoint.decoded POS04AcquisitionEndpoint.bindings a = some d)
    (hr : Complete POS04RecordComponent.view.dependencies a) :
    PresentationCoherence.Pass raw a := by
  have hc := endpoint_complete a he
  have hs : Complete (clauseScope .source .c6) a :=
    fun k hk => hc k (List.mem_append_left _ (List.mem_append_right _ hk))
  have ht : Complete (clauseScope .target .c6) a :=
    fun k hk => hc k (List.mem_append_right _ hk)
  let sr := POS04TemporalCoherence.ready a .source hs
  let tr := POS04TemporalCoherence.ready a .target ht
  exact ⟨⟨sr,POS04TemporalCoherence.laws a .source sr⟩,
    ⟨tr,POS04TemporalCoherence.laws a .target tr⟩,
    POS04AcquisitionEndpoint.data a,POS04RecordComponent.data a,
    POS04AcquisitionEndpoint.decoded_eq a hc,
    POS04RecordComponent.read_equation a hr,record_laws a,rfl,rfl⟩

theorem checked_of_lineage (m : RawLaneModel)
    (h : POS04CompleteLineage.StrictTemporalLineage m) :
    PresentationCoherence.Pass raw (image m.assignment) := by
  have ep := (POS04AcquisitionEndpoint.pass_iff m).mpr h.2.2.2.2.1
  exact checked _ ⟨ep.choose,ep.choose_spec.1⟩ h.2.2.2.1.1

theorem canonical_checked : PresentationCoherence.Pass raw canonical := by
  simpa only [baseline,image_canonical] using checked_of_lineage baseline POS04CompleteLineage.positive

/-- Concrete guards alter only the displayed presentation, leaving its raw
assigned primitive source fixed. -/
theorem factor_tick_guard :
    {(POS04FactorTransport.data canonical .target) with ticks := fun _ _ => 0} ≠
      PresentationCoherence.factor (POS04TemporalFactor.raw (runInputs6 canonical .target) .target) := by
  intro h
  have ht := congrArg (fun d : POS04FactorTransport.Data => d.ticks .p1w0 (canonicalAction .p1w0)) h
  change (0 : Nat) = 1 at ht
  contradiction

theorem record_writer_guard : ¬ PresentationCoherence.RecordLaws (POS04AcquisitionEndpoint.data canonical)
    {(POS04RecordComponent.data canonical) with targetWriter := fun _ => false} stages.idxOf :=
  PresentationCoherence.record_writer_guard _ _ _ .a (by decide)

theorem record_clock_guard : ¬ PresentationCoherence.RecordLaws (POS04AcquisitionEndpoint.data canonical)
    {(POS04RecordComponent.data canonical) with clock := fun _ => 0} stages.idxOf :=
  PresentationCoherence.record_clock_guard _ _ _ .targetExit (by decide)

theorem record_realized_guard : ¬ PresentationCoherence.RecordLaws (POS04AcquisitionEndpoint.data canonical)
    {(POS04RecordComponent.data canonical) with realized := []} stages.idxOf :=
  PresentationCoherence.record_realization_guard _ _ _ (by decide)

theorem missing_endpoint (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ acquisitionDependencies) (hm : a k = none) : ¬ PresentationCoherence.Pass raw a :=
  PresentationCoherence.missing_endpoint_rejected raw a k ((POS04AcquisitionEndpoint.scope_iff k).mpr hk) hm

theorem missing_record (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ POS04RecordComponent.view.dependencies) (hm : a k = none) : ¬ PresentationCoherence.Pass raw a :=
  PresentationCoherence.missing_record_rejected raw a k hk hm

/-- All five typed frame coordinates decode back to the same raw run. This
links endpoint/factor coordinates to the shared historical/actual target frame,
not merely to a second presentation with equal carrier labels. -/
theorem shared_frame (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : TemporalRuntimeCoherence.Ready (POS04TemporalCoherence.raw tag) a)
    (he : ExecutionLink.Ready (POS04RuntimeExecutionLink.raw tag) a)
    (x : Registers Register RegisterValue) :
    ExecutionLink.embed (POS04RuntimeExecutionLink.raw tag) a he x () =
      (tag,POS04TemporalFactor.decodeRun
        (TemporalRuntimeCoherence.project (POS04TemporalCoherence.raw tag) a h x)) := by
  rw [POS04RuntimeExecutionLink.embed_eq,frame_projection,POS04TemporalFactor.decode_encode]
  rfl

/-- The record audit's unit increment is the actual event-clock increment
where a strict event is certified. Malformed/non-strict records are not
silently equated to unit advancing execution events. -/
theorem event_increment (a : CSTTT.POS04.Assigned.Assignment) (e : CSTTT.POS04.Event)
    (hs : strictEvent6 (runInputs6 a .target) e = true) :
    (POS04RecordComponent.eventMap e).orderAdvance =
      stages.idxOf e.toStage - stages.idxOf e.fromStage := by
  simp only [strictEvent6,Bool.and_eq_true,decide_eq_true_eq] at hs
  change (1 : Nat) = _
  omega

theorem record_event_guard : ¬ PresentationCoherence.RecordLaws (POS04AcquisitionEndpoint.data canonical)
    {(POS04RecordComponent.data canonical) with events := fun _ => none} stages.idxOf :=
  PresentationCoherence.record_event_guard _ _ _ .mix1 (by decide)

/-- Reuse the existing actual-runtime counter/ledger/readout controls. Their
raw clause primitives and temporal presentation remain present; only the
indicated interpreter field changes. -/
theorem erased_row_guard (tag : Tag) :
    ¬ TemporalRuntimeCoherence.Valid (POS04TemporalCoherence.proposal tag (POS04TemporalCoherence.emptyRows tag)) canonical :=
  POS04TemporalCoherence.empty_rows_rejected tag

theorem stationary_update_guard (tag : Tag) :
    ¬ TemporalRuntimeCoherence.Valid (POS04TemporalCoherence.proposal tag (POS04TemporalCoherence.stationary tag)) canonical :=
  POS04TemporalCoherence.stationary_rejected tag

theorem capped_progress_guard (tag : Tag) :
    ¬ TemporalRuntimeCoherence.Valid (POS04TemporalCoherence.proposal tag (POS04TemporalCoherence.cappedProgress tag)) canonical :=
  POS04TemporalCoherence.capped_progress_rejected tag

/-- The raw owning frame interface is the SAME source/receiver frame family
used by PublicRuntime. Neither probability tables nor observers are repeated. -/
def frames : FramePresentation.Raw Cell Value Register Register RegisterValue RegisterValue
    KState Action Ambient RouteId HistoryId RouteId CSTTT.POS04.Stage EventId Tag LaneDisturbance
    CSTTT.POS04.PredictiveNow CSTTT.POS04.PredictiveNow where
  sourceFrame := POS04ExecutionFrontier.raw
  targetFrame := POS04ReceiverFrontier.raw
  sourceSchema := POS04TemporalFactor.schema .source
  targetSchema := POS04TemporalFactor.schema .target
  sourceCells := POS04TemporalFactor.bindings .source
  targetCells := POS04TemporalFactor.bindings .target
  sourcePredictive := POS04TemporalFactor.predictionImage
  targetPredictive := POS04TemporalFactor.predictionImage
  sourceProjection := POS04TemporalCoherence.projection
  targetProjection := POS04TemporalCoherence.projection
  owner := tagCarrierId
  events := POS04AcquisitionEndpoint.bindings.events
  receiver := POS04AcquisitionEndpoint.bindings.receiver
  entry := .sourceLive
  exit := .targetExit
  exitEvent := .exit
  fallback := .p0w0
  rowScale := 4
  transfer := id
  clock := stages.idxOf
  factorMaps := POS04FactorTransport.binding.maps
  record := POS04RecordComponent.view

theorem constructed_presentation : FramePresentation.presentation frames = raw := rfl

theorem public_source_frame (p : Protocol) : frames.sourceFrame = (POS04PublicRuntime.raw p).lineage.source := rfl
theorem public_target_frame (p : Protocol) : frames.targetFrame = (POS04PublicRuntime.raw p).lineage.target := rfl

/-- These raw schema identities hold without any assignment-completeness or
acceptance hypothesis. Runtime events and the finite C6/record presentation
therefore use exactly the same declared stage clock and carrier interface. -/
theorem frame_schema_checked : FramePresentation.SchemaCheck frames :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem frame_clock_guard : ¬ FramePresentation.SchemaCheck
    {frames with sourceFrame := {frames.sourceFrame with schema := {frames.sourceFrame.schema with clock := fun _ => 0}}} :=
  FramePresentation.source_clock_guard _ .targetExit (by decide)

theorem frame_owner_guard : ¬ FramePresentation.SchemaCheck
    {frames with targetFrame := {frames.targetFrame with schema := {frames.targetFrame.schema with target := tagCarrierId .source}}} :=
  FramePresentation.target_owner_guard _ (by decide)

theorem public_coherence (m : RawLaneModel) (h : POS04CompleteLineage.StrictTemporalLineage m) :
    FramePresentation.SchemaCheck frames ∧
      PresentationCoherence.Pass (FramePresentation.presentation frames)
        (PublicRuntime.target (POS04PublicRuntime.raw (protocol m)) m.assignment) := by
  rw [constructed_presentation,POS04PublicRuntime.target_eq]
  exact ⟨frame_schema_checked,checked_of_lineage m h⟩

end CSTTT.TargetTheory.GenericHandoff.POS04PresentationCoherence
