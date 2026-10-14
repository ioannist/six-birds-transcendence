import CSTTT.Targets.GenericHandoff.ReceiverSequence
import CSTTT.Targets.GenericHandoff.POS04ReceiverContent
import CSTTT.Targets.GenericHandoff.POS04ReceiverIntervention

/-! Common-coordinate two-receiver operation witness. These are actual reset
programs and returned classes, not a three-carrier two-hop Temporal-FIACH
instance. Physical middle interfaces and supported acquisition remain separate.
The shared stage/cover globals are proved for every partial assignment. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ReceiverSequence
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit CSTTT.TargetTheory.ComputedFIACH
open RegisterInterpreter POS04ResourceRuntime POS04RegisterDynamics
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def middleMaps : FactorTransport.Maps KState KState Action Action Tag :=
  {POS04FactorTransport.maps with owner := CSTTT.POS04.Assigned.swapTag}
def transport : ReceiverSequence.Delivery Cell Value KState Action Tag RouteId EventId RouteId :=
  ⟨⟨.literal middleMaps⟩,id,id,id⟩

theorem left_cells (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    ReceiverSequence.leftCells (POS04RawHandoff.raw p) a = image a := POS04RawHandoff.target_eq p a
theorem right_cells (p q : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    ReceiverSequence.rightCells (POS04RawHandoff.raw p) (POS04RawHandoff.raw q) a = a := by
  rw [ReceiverSequence.rightCells,left_cells,POS04RawHandoff.target_eq]
  exact exchange_assignment_involution a

theorem bridge_equations : FactorTransport.Equations
    (POS04TemporalFactor.schema .target) (POS04TemporalFactor.schema .source)
    (POS04FactorTransport.data canonical .target) (POS04FactorTransport.data canonical .source) middleMaps := by
  constructor
  · rfl
  · intro s; rfl
  · intro s; rfl
  · intro s; rfl
  · intro s act u
    rw [POS04FactorTransport.weight_equation,POS04FactorTransport.weight_equation]
    rfl
  · intro s; rfl
  · rfl
  · rfl
  · intro s u h; exact h
  · rfl

theorem active :
    AcquisitionEndpoint.active POS04AcquisitionEndpoint.cfg (POS04AcquisitionEndpoint.data canonical) = true := by
  decide +kernel

abbrev initialReady := POS04ReceiverContent.ready canonical (canonical_complete _)
abbrev targetReady (p : Protocol) := POS04ReceiverContent.target_ready p canonical (canonical_complete _)

theorem checked (p q : Protocol) : ReceiverSequence.Checked
    (POS04RawHandoff.raw p) (POS04RawHandoff.raw q) POS04ReceiverContent.instructions POS04ReceiverContent.instructions
    transport canonical canonical initialReady (targetReady p) initialReady (targetReady q) := by
  refine ⟨POS04ReceiverContent.historical_ready p canonical (canonical_complete _),
    POS04ReceiverContent.embedding_ready p canonical (canonical_complete _),
    POS04ReceiverContent.historical_ready q canonical (canonical_complete _),
    POS04ReceiverContent.embedding_ready q canonical (canonical_complete _),
    POS04AcquisitionEndpoint.data canonical,POS04AcquisitionEndpoint.data canonical,
    POS04FactorTransport.maps,POS04FactorTransport.maps,middleMaps,
    POS04ReceiverContent.positive p,POS04ReceiverContent.positive q,?_,?_,rfl,bridge_equations,?_,?_,?_⟩
  · exact (POS04RawHandoff.factor_iff p canonical).mpr POS04FactorTransport.positive
  · exact (POS04RawHandoff.factor_iff q canonical).mpr POS04FactorTransport.positive
  · change AcquisitionEndpoint.active POS04AcquisitionEndpoint.cfg (POS04AcquisitionEndpoint.data canonical) = true
    decide +kernel
  · change AcquisitionEndpoint.active POS04AcquisitionEndpoint.cfg (POS04AcquisitionEndpoint.data canonical) = true
    decide +kernel
  · exact ⟨POS04ReceiverContent.inputA,POS04ReceiverContent.inputB,POS04ReceiverContent.source_classes_distinct⟩

theorem content_faithful (p q : Protocol) : ReceiverSequence.ContentFaithful
    (POS04RawHandoff.raw p) (POS04RawHandoff.raw q) POS04ReceiverContent.instructions POS04ReceiverContent.instructions
    transport canonical canonical initialReady (targetReady p) initialReady (targetReady q) :=
  ReceiverSequence.content_soundness _ _ _ _ _ _ _ _ _ _ _ (checked p q)

theorem operation_class (p q : Protocol)
    (delivery : ReceiverSequence.Delivery Cell Value KState Action Tag RouteId EventId RouteId)
    (maps : FactorTransport.Maps KState KState Action Action Tag)
    (hm : delivery.maps.read canonical = some maps)
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverSequence.classAt (POS04RawHandoff.raw p) (POS04RawHandoff.raw q)
      POS04ReceiverContent.instructions POS04ReceiverContent.instructions delivery canonical canonical
      initialReady (targetReady p) initialReady (targetReady q) input =
    some (FactorTransport.classOf (POS04TemporalFactor.schema .target) (POS04FactorTransport.data canonical .target) (maps.state input.1)) :=
  ReceiverSequence.actual_class (POS04RawHandoff.raw p) (POS04RawHandoff.raw q)
    POS04ReceiverContent.instructions POS04ReceiverContent.instructions delivery canonical canonical
    initialReady (targetReady p) initialReady (targetReady q)
    (POS04ReceiverContent.historical_ready p canonical (canonical_complete _))
    (POS04ReceiverContent.embedding_ready p canonical (canonical_complete _))
    (POS04ReceiverContent.historical_ready q canonical (canonical_complete _))
    (POS04ReceiverContent.embedding_ready q canonical (canonical_complete _))
    (POS04AcquisitionEndpoint.data canonical) (POS04AcquisitionEndpoint.data canonical)
    POS04FactorTransport.maps POS04FactorTransport.maps maps
    (POS04ReceiverContent.positive p) (POS04ReceiverContent.positive q) hm active active input

theorem actual_class (p q : Protocol)
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverSequence.classAt (POS04RawHandoff.raw p) (POS04RawHandoff.raw q)
      POS04ReceiverContent.instructions POS04ReceiverContent.instructions transport canonical canonical
      initialReady (targetReady p) initialReady (targetReady q) input =
    some (FactorTransport.classOf (POS04TemporalFactor.schema .target) (POS04FactorTransport.data canonical .target) input.1) :=
  operation_class p q transport middleMaps rfl input

theorem public_content (p q : Protocol) : ReceiverSequence.ContentReadout
    (POS04RawHandoff.raw p) (POS04RawHandoff.raw q) POS04ReceiverContent.instructions POS04ReceiverContent.instructions
    transport canonical := by
  unfold ReceiverSequence.ContentReadout
  rw [left_cells,right_cells,image_canonical]
  exact ⟨initialReady,targetReady p,initialReady,targetReady q,content_faithful p q⟩

def constantMaps : FactorTransport.Maps KState KState Action Action Tag :=
  {middleMaps with state := fun _ => .p0w0}
def constantTransport : ReceiverSequence.Delivery Cell Value KState Action Tag RouteId EventId RouteId :=
  {transport with maps := ⟨.literal constantMaps⟩}

theorem constant_other_fields : constantTransport.event = transport.event ∧
    constantTransport.history = transport.history ∧ constantTransport.route = transport.route ∧
    constantMaps.action = middleMaps.action ∧ constantMaps.coordinate = middleMaps.coordinate ∧
    constantMaps.predictive = middleMaps.predictive ∧ constantMaps.owner = middleMaps.owner ∧
    constantMaps.maintenance = middleMaps.maintenance := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem constant_class (p q : Protocol)
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverSequence.classAt (POS04RawHandoff.raw p) (POS04RawHandoff.raw q)
      POS04ReceiverContent.instructions POS04ReceiverContent.instructions constantTransport canonical canonical
      initialReady (targetReady p) initialReady (targetReady q) input =
    some (FactorTransport.classOf (POS04TemporalFactor.schema .target) (POS04FactorTransport.data canonical .target) .p0w0) :=
  operation_class p q constantTransport constantMaps rfl input

theorem constant_not_faithful (p q : Protocol) : ¬ ReceiverSequence.ContentFaithful
    (POS04RawHandoff.raw p) (POS04RawHandoff.raw q) POS04ReceiverContent.instructions POS04ReceiverContent.instructions
    constantTransport canonical canonical initialReady (targetReady p) initialReady (targetReady q) := by
  rintro ⟨data,decoded,⟨x,y,distinct⟩,total,faithful⟩
  apply faithful x y distinct
  rw [constant_class,constant_class]

abbrev cutInitial := (POS04ReceiverIntervention.initial_ready_iff canonical).mpr initialReady
abbrev cutTarget (p : Protocol) := (POS04ReceiverIntervention.target_ready_iff p canonical).mpr (targetReady p)

theorem source_cut (p q : Protocol) (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverSequence.receiveAt (POS04RawHandoff.raw p) (POS04RawHandoff.raw q)
      POS04ReceiverContent.instructions POS04ReceiverContent.instructions transport
      (POS04ReceiverIntervention.withoutSource canonical) canonical cutInitial (cutTarget p) initialReady (targetReady q) input = none ∧
    ReceiverSequence.classAt (POS04RawHandoff.raw p) (POS04RawHandoff.raw q)
      POS04ReceiverContent.instructions POS04ReceiverContent.instructions transport
      (POS04ReceiverIntervention.withoutSource canonical) canonical cutInitial (cutTarget p) initialReady (targetReady q) input = none :=
  ReceiverSequence.source_erasure (POS04RawHandoff.raw p) (POS04RawHandoff.raw q)
    POS04ReceiverContent.instructions POS04ReceiverContent.instructions transport canonical canonical
    initialReady (targetReady q) POS04ReceiverIntervention.erase POS04ReceiverIntervention.erasure_law
    cutInitial (cutTarget p) input

theorem source_cut_not_faithful (p q : Protocol) : ¬ ReceiverSequence.ContentFaithful
    (POS04RawHandoff.raw p) (POS04RawHandoff.raw q) POS04ReceiverContent.instructions POS04ReceiverContent.instructions
    transport (POS04ReceiverIntervention.withoutSource canonical) canonical cutInitial (cutTarget p) initialReady (targetReady q) := by
  apply ReceiverSequence.none_classes_not_faithful
  intro input
  exact (source_cut p q input).2

theorem cut_latent_factors (tag : Tag) :
    TemporalFactorCells.decoded (POS04TemporalFactor.bindings tag) (POS04ReceiverIntervention.withoutSource canonical) =
      TemporalFactorCells.decoded (POS04TemporalFactor.bindings tag) canonical :=
  POS04ReceiverIntervention.latent_factor canonical tag

end CSTTT.TargetTheory.GenericHandoff.POS04ReceiverSequence
