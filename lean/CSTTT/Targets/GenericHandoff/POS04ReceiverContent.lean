import CSTTT.Targets.GenericHandoff.ReceiverContent
import CSTTT.Targets.GenericHandoff.POS04RawHandoff

/-! POS-04 all-input receiver reset square, on every partial assignment with
the actually consumed inputs present. This does not strengthen AF/AO or infer
funded source execution from historical support. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ReceiverContent
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter RegisterInitialization
open POS04RegisterDynamics POS04ResourceRuntime
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

def instructions : ReceiverContent.Instructions Cell Register KState Ambient RouteId EventId RouteId Value RegisterValue :=
  ⟨POS04HistoricalAcquisition.raw.reset,Ambient.inK⟩

theorem ready (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete acquisitionDependencies a) :
    RegisterInitialization.Ready instructions.resetProgram a := by
  intro reg k hk
  cases reg <;> simp [instructions,POS04HistoricalAcquisition.raw,Expr.dependencies] at hk
  subst k
  exact hc .receiverInput (by simp [acquisitionDependencies,phase2Dependencies])

theorem register_ready (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete acquisitionDependencies a) :
    HistoricalAcquisition.Ready POS04HistoricalAcquisition.raw a :=
  POS04HistoricalAcquisition.ready a (fun k hk => hc k ((by decide :
    POS04HistoricalAcquisition.scope ⊆ acquisitionDependencies) hk))

/-- Every partial assignment, with explicit interpreter readiness. The raw
equations hold independently of package/lineage/autonomy acceptance. -/
theorem checked (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete acquisitionDependencies a)
    (hh : HistoricalAcquisition.Ready (ReceiverContent.acquisition (POS04RawHandoff.raw p)) a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target a)
    (he : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime (POS04RawHandoff.raw p))) a) :
    ReceiverContent.Laws (POS04RawHandoff.raw p) instructions a (ready a hc) hh ht he
      (POS04AcquisitionEndpoint.data a) POS04FactorTransport.maps := by
  have hreceiver := cell_value (hc .receiverInput (by simp [acquisitionDependencies,phase2Dependencies]))
  have hevents := cell_value (hc .eventTable (by simp [acquisitionDependencies,phase2Dependencies]))
  have hrealized := cell_value (hc .realized (by simp [acquisitionDependencies,phase2Dependencies]))
  have hhistories := cell_value (hc .histories (by simp [acquisitionDependencies,phase2Dependencies]))
  have hroutes := cell_value (hc .routeTable (by simp [acquisitionDependencies,phase2Dependencies]))
  have histories_read : (POS04RawHandoff.raw p).historical.histories.read a = some
      (POS04ExecutionFrontier.historyPath (runInputs6 a .source).base.histories (runInputs6 a .source).base.routes) := by
    change POS04HistoricalAcquisition.raw.histories.read a = _
    change ((a Cell.histories).bind (fun histories => (a Cell.routeTable).bind
      (fun routes => some (histories,routes)))).map (fun v => POS04ExecutionFrontier.historyPath v.1 v.2) = _
    rw [hhistories,hroutes]
    rfl
  have routes_read : (POS04RawHandoff.raw p).historical.routes.read a = some
      (POS04ExecutionFrontier.routeView.project (runInputs6 a .source).base.routes) := by
    change (a Cell.routeTable).map POS04ExecutionFrontier.routeView.project = _
    rw [hroutes]
    rfl
  refine ⟨POS04AcquisitionEndpoint.decoded_eq a hc,rfl,rfl,rfl,?_,?_,rfl,?_,?_,?_,?_,?_,?_⟩
  · intro rid route rs hs hroute hrs hhs
    have ers := Option.some.inj (hrs.symm.trans routes_read)
    have ehs := Option.some.inj (hhs.symm.trans histories_read)
    subst rs; subst hs
    change TemporalFactorRules.route (POS04TemporalFactor.raw (runInputs6 a .source) .source) rid = some route at hroute
    rw [POS04TemporalFactor.route_eq] at hroute
    cases hfind : (runInputs6 a .source).base.routes.find? (fun v => v.id == rid) with
    | none => simp [hfind] at hroute
    | some found =>
      have er : POS04TemporalFactor.routeMap found = route := by simpa [hfind] using hroute
      subst route
      simp [POS04ExecutionFrontier.historyPath,POS04ExecutionFrontier.routeView,hfind,
        POS04TemporalFactor.routeMap,POS04AcquisitionEndpoint.data,POS04TemporalFactor.raw]
  · intro rid route rs hroute hrs
    have ers := Option.some.inj (hrs.symm.trans routes_read)
    subst rs
    change TemporalFactorRules.route (POS04TemporalFactor.raw (runInputs6 a .source) .source) rid = some route at hroute
    rw [POS04TemporalFactor.route_eq] at hroute
    cases hfind : (runInputs6 a .source).base.routes.find? (fun v => v.id == rid) with
    | none => simp [hfind] at hroute
    | some found =>
      have er : POS04TemporalFactor.routeMap found = route := by simpa [hfind] using hroute
      subst route
      simp [POS04ExecutionFrontier.routeView,hfind,POS04TemporalFactor.routeMap]
  · change (a Cell.receiverInput).map POS04ExecutionFrontier.receiverView.project = _
    rw [hreceiver]
    rfl
  · change (a Cell.realized).map id = _
    rw [hrealized]
    rfl
  · intro records hrecords
    have hscan : (POS04RawHandoff.raw p).historical.activationEvents.read a = some
        (POS04HistoricalAcquisition.activationRecords (runInputs6 a .target).base.events) := by
      change (a Cell.eventTable).map POS04HistoricalAcquisition.activationRecords = _
      rw [hevents]
      rfl
    have er := Option.some.inj (hrecords.symm.trans hscan)
    subst records
    rw [show (OwningHandoff.endpoint (POS04RawHandoff.raw p)).schema = POS04AcquisitionEndpoint.cfg from rfl,
      POS04AcquisitionEndpoint.active_eq]
    exact POS04HistoricalAcquisition.activation_iff_active7 (runInputs6 a .target).base
  · intro s; rfl
  · intro input
    change ExecutionLink.embed POS04RuntimeExecutionLink.historicalRaw a he _ =
      HistoricalAcquisition.reset (POS04HistoricalRuntime.acquisitionRaw p) a hh input
    rw [POS04RuntimeExecutionLink.historical_embed]
    rw [POS04HistoricalRuntime.reset_link p a hh (register_ready a hc) input]
    rfl
  · intro input
    change TemporalRuntimeCoherence.project (POS04TemporalCoherence.raw .target) a ht _ = _
    rw [POS04TemporalCoherence.project_eq]
    have er : RegisterInitialization.initial instructions.resetProgram a (ready a hc) input =
        HistoricalAcquisition.reset POS04HistoricalAcquisition.raw a (register_ready a hc) input := rfl
    rw [er,POS04HistoricalAcquisition.reset_computed a (register_ready a hc) input _ hreceiver,decode_encode]
    rfl

theorem historical_ready (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete acquisitionDependencies a) :
    HistoricalAcquisition.Ready (ReceiverContent.acquisition (POS04RawHandoff.raw p)) a :=
  POS04HistoricalRuntime.acquisition_ready p a (fun k hk => hc k
    (List.mem_append_left _ (List.mem_append_left _ (POS04HistoricalRuntime.scope_subset p hk))))

theorem target_ready (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete acquisitionDependencies a) :
    TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target a :=
  POS04TemporalCoherence.ready a .target (fun k hk => hc k (List.mem_append_right _ hk))

theorem embedding_ready (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete acquisitionDependencies a) :
    ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime (POS04RawHandoff.raw p))) a :=
  POS04RuntimeExecutionLink.historical_ready a (fun k hk => hc k ((by decide :
    POS04RuntimeExecutionLink.targetDependencies ⊆ acquisitionDependencies) hk))

/-- Populated from raw input completeness only, on ALL partial assignments. -/
theorem checked_from_inputs (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete acquisitionDependencies a) :
    ReceiverContent.Laws (POS04RawHandoff.raw p) instructions a (ready a hc)
      (historical_ready p a hc) (target_ready p a hc) (embedding_ready p a hc)
      (POS04AcquisitionEndpoint.data a) POS04FactorTransport.maps :=
  checked p a hc _ _ _

theorem positive (p : Protocol) :
    ReceiverContent.Laws (POS04RawHandoff.raw p) instructions canonical (ready canonical (canonical_complete _))
      (historical_ready p canonical (canonical_complete _)) (target_ready p canonical (canonical_complete _))
      (embedding_ready p canonical (canonical_complete _)) (POS04AcquisitionEndpoint.data canonical)
      POS04FactorTransport.maps := checked_from_inputs p canonical (canonical_complete _)

def inputA : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId :=
  (.p0w0,[.p0w0],[.mix1],.a,.a)
def inputB : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId :=
  (.p1w0,[.p1w0],[.mix1],.a,.a)

/-- All-input reset tests, not new registered realized-route fixtures. -/
theorem source_classes_distinct :
    FactorTransport.classOf (POS04TemporalFactor.schema .source) (POS04FactorTransport.data canonical .source) inputA.1 ≠
      FactorTransport.classOf (POS04TemporalFactor.schema .source) (POS04FactorTransport.data canonical .source) inputB.1 := by
  decide +kernel

theorem positive_content (p : Protocol) :
    ReceiverContent.receivedClass (POS04RawHandoff.raw p) instructions canonical (ready canonical (canonical_complete _))
      (target_ready p canonical (canonical_complete _)) inputA ≠
    ReceiverContent.receivedClass (POS04RawHandoff.raw p) instructions canonical (ready canonical (canonical_complete _))
      (target_ready p canonical (canonical_complete _)) inputB := by
  apply ReceiverContent.distinct_source_classes_from_factor (positive p)
  · exact (POS04RawHandoff.factor_iff p canonical).mpr POS04FactorTransport.positive
  · change AcquisitionEndpoint.active POS04AcquisitionEndpoint.cfg (POS04AcquisitionEndpoint.data canonical) = true
    decide +kernel
  · exact source_classes_distinct

theorem positive_content_faithful (p : Protocol) :
    ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) instructions canonical
      (ready canonical (canonical_complete _)) (target_ready p canonical (canonical_complete _)) := by
  apply ReceiverContent.content_faithful (positive p)
  · exact (POS04RawHandoff.factor_iff p canonical).mpr POS04FactorTransport.positive
  · change AcquisitionEndpoint.active POS04AcquisitionEndpoint.cfg (POS04AcquisitionEndpoint.data canonical) = true
    decide +kernel
  · exact ⟨inputA,inputB,source_classes_distinct⟩

/-- Only the raw factor reset instruction changes. All other register
initializers and assigned endpoint/activation primitives are retained. -/
def constant : ReceiverContent.Instructions Cell Register KState Ambient RouteId EventId RouteId Value RegisterValue :=
  {instructions with resetProgram := fun reg => match reg with
    | .factor => .literal (Ambient.inK .p0w0)
    | .counter => instructions.resetProgram .counter
    | .ticks => instructions.resetProgram .ticks
    | .residue => instructions.resetProgram .residue
    | .funded => instructions.resetProgram .funded}

theorem constant_ready (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete acquisitionDependencies a) :
    RegisterInitialization.Ready constant.resetProgram a := by
  intro reg k hk
  cases reg <;> simp [constant,instructions,POS04HistoricalAcquisition.raw,Expr.dependencies] at hk
  subst k
  exact hc .receiverInput (by simp [acquisitionDependencies,phase2Dependencies])

theorem constant_reset (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete acquisitionDependencies a)
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    RegisterInitialization.initial constant.resetProgram a (constant_ready a hc) input =
      encode ⟨.inK .p0w0,0,0,(input.2.1,input.2.2.1),(runInputs6 a .target).base.receiver.funded⟩ := by
  have hreceiver := cell_value (hc .receiverInput (by simp [acquisitionDependencies,phase2Dependencies]))
  funext reg
  apply Option.some.inj
  have eq := RegisterInitialization.initial_eq constant.resetProgram a (constant_ready a hc) input reg
  have evaluated : RegisterInitialization.evaluate constant.resetProgram a input reg =
      some (encode ⟨.inK .p0w0,0,0,(input.2.1,input.2.2.1),(runInputs6 a .target).base.receiver.funded⟩ reg) := by
    cases reg
    · rfl
    · rfl
    · rfl
    · rfl
    · change (a Cell.receiverInput).map Receiver.funded = _
      rw [hreceiver]
      rfl
  exact eq.symm.trans evaluated

/-- Direct evaluation of the actual returned class; no failed sufficient
certificate is used to infer loss of content. -/
theorem constant_class (p : Protocol) (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverContent.receivedClass (POS04RawHandoff.raw p) constant canonical
      (constant_ready canonical (canonical_complete _)) (target_ready p canonical (canonical_complete _)) input =
    some (FactorTransport.classOf (POS04TemporalFactor.schema .target) (POS04FactorTransport.data canonical .target) .p0w0) := by
  have decoded : AcquisitionEndpoint.decoded (OwningHandoff.endpoint (POS04RawHandoff.raw p)).bindings canonical =
      some (POS04AcquisitionEndpoint.data canonical) := POS04AcquisitionEndpoint.decoded_eq _ (canonical_complete _)
  have run : ReceiverContent.receivedRun (POS04RawHandoff.raw p) constant canonical
      (constant_ready canonical (canonical_complete _)) (target_ready p canonical (canonical_complete _)) input =
      POS04TemporalFactor.encodeRun ⟨.inK .p0w0,0,0,(input.2.1,input.2.2.1),true⟩ := by
    change TemporalRuntimeCoherence.project (POS04TemporalCoherence.raw .target) canonical _ _ = _
    rw [POS04TemporalCoherence.project_eq,constant_reset canonical (canonical_complete _) input,decode_encode]
    rfl
  simp only [ReceiverContent.receivedClass,ReceiverContent.receive,decoded,
    show (OwningHandoff.endpoint (POS04RawHandoff.raw p)).schema = POS04AcquisitionEndpoint.cfg from rfl,run]
  rfl

theorem constant_content_counterexample (p : Protocol) :
    FactorTransport.classOf (POS04TemporalFactor.schema .source) (POS04FactorTransport.data canonical .source) inputA.1 ≠
      FactorTransport.classOf (POS04TemporalFactor.schema .source) (POS04FactorTransport.data canonical .source) inputB.1 ∧
    ReceiverContent.receivedClass (POS04RawHandoff.raw p) constant canonical (constant_ready canonical (canonical_complete _))
      (target_ready p canonical (canonical_complete _)) inputA =
    ReceiverContent.receivedClass (POS04RawHandoff.raw p) constant canonical (constant_ready canonical (canonical_complete _))
      (target_ready p canonical (canonical_complete _)) inputB :=
  ⟨source_classes_distinct,(constant_class p inputA).trans (constant_class p inputB).symm⟩

theorem constant_not_faithful (p : Protocol) :
    ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) constant canonical
      (constant_ready canonical (canonical_complete _)) (target_ready p canonical (canonical_complete _)) := by
  rintro ⟨data,hdata,_,_,faithful⟩
  have decoded : AcquisitionEndpoint.decoded (OwningHandoff.endpoint (POS04RawHandoff.raw p)).bindings canonical =
      some (POS04AcquisitionEndpoint.data canonical) := POS04AcquisitionEndpoint.decoded_eq _ (canonical_complete _)
  have same := Option.some.inj (hdata.symm.trans decoded)
  subst data
  exact faithful inputA inputB source_classes_distinct (constant_content_counterexample p).2

def sourceAbsent : CSTTT.POS04.Assigned.Assignment :=
  Assigned.put canonical .receiverInput (some {receiver with sourcePresent := false})

theorem source_absent_complete : Complete acquisitionDependencies sourceAbsent := by
  intro k _
  by_cases h : k = .receiverInput
  · subst k; rfl
  · rw [show sourceAbsent k = canonical k from Assigned.put_other _ _ _ _ h]
    rfl

/-- Source is absent while target frame initialization remains genuinely
ready. Both returned run and actual returned class reject directly. -/
theorem source_absent_no_reception (p : Protocol)
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverContent.receive (POS04RawHandoff.raw p) instructions sourceAbsent (ready sourceAbsent source_absent_complete)
      (target_ready p sourceAbsent source_absent_complete) input = none ∧
    ReceiverContent.receivedClass (POS04RawHandoff.raw p) instructions sourceAbsent (ready sourceAbsent source_absent_complete)
      (target_ready p sourceAbsent source_absent_complete) input = none := by
  have decoded : AcquisitionEndpoint.decoded (OwningHandoff.endpoint (POS04RawHandoff.raw p)).bindings sourceAbsent =
      some (POS04AcquisitionEndpoint.data sourceAbsent) :=
    POS04AcquisitionEndpoint.decoded_eq _ source_absent_complete
  have absent : (POS04AcquisitionEndpoint.data sourceAbsent).receiver.sourcePresent = false := rfl
  exact ⟨ReceiverContent.source_absent decoded absent input,ReceiverContent.source_absent_class decoded absent input⟩

theorem source_absent_not_faithful (p : Protocol) :
    ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) instructions sourceAbsent
      (ready sourceAbsent source_absent_complete) (target_ready p sourceAbsent source_absent_complete) :=
  ReceiverContent.source_absent_not_faithful (POS04AcquisitionEndpoint.decoded_eq _ source_absent_complete) rfl

def missingSourceTicks : CSTTT.POS04.Assigned.Assignment := Assigned.put canonical (.ticks .source) none

theorem missing_ticks_initial_ready : RegisterInitialization.Ready instructions.resetProgram missingSourceTicks := by
  intro reg k hk
  cases reg <;> simp [instructions,POS04HistoricalAcquisition.raw,Expr.dependencies] at hk
  subst k
  rfl

theorem missing_ticks_target_ready (p : Protocol) :
    TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target missingSourceTicks := by
  apply POS04TemporalCoherence.ready missingSourceTicks .target
  intro k hk
  have other : k ≠ .ticks .source := by
    intro e
    subst k
    exact (by decide : Cell.ticks .source ∉ clauseScope .target .c6) hk
  rw [show missingSourceTicks k = canonical k from Assigned.put_other _ _ _ _ other]
  rfl

/-- A missing source-only endpoint input is compatible with actual target
initialization readiness. The readout rejects, with no contradictory readiness
premise and no defaulted endpoint data. -/
theorem missing_ticks_no_reception (p : Protocol)
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverContent.receive (POS04RawHandoff.raw p) instructions missingSourceTicks missing_ticks_initial_ready
      (missing_ticks_target_ready p) input = none ∧
    ReceiverContent.receivedClass (POS04RawHandoff.raw p) instructions missingSourceTicks missing_ticks_initial_ready
      (missing_ticks_target_ready p) input = none :=
  ReceiverContent.missing_endpoint_cell (.ticks .source)
    ((POS04AcquisitionEndpoint.scope_iff _).mpr (by simp [acquisitionDependencies,clauseScope,commonScope]))
    (Assigned.put_same _ _ _) input

theorem missing_ticks_not_faithful (p : Protocol) :
    ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) instructions missingSourceTicks
      missing_ticks_initial_ready (missing_ticks_target_ready p) :=
  ReceiverContent.missing_endpoint_not_faithful (AcquisitionEndpoint.missing_input _ _ (.ticks .source)
    ((POS04AcquisitionEndpoint.scope_iff _).mpr (by simp [acquisitionDependencies,clauseScope,commonScope]))
    (Assigned.put_same _ _ _))

end CSTTT.TargetTheory.GenericHandoff.POS04ReceiverContent
