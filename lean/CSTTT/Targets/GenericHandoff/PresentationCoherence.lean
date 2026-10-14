import CSTTT.Targets.GenericHandoff.FactorTransport
import CSTTT.Targets.GenericHandoff.AcquisitionEndpoint
import CSTTT.Targets.GenericHandoff.RecordComponent
import CSTTT.Targets.GenericHandoff.TemporalRuntimeCoherence

/-! TTH-06 presentation equations. Finite factor data is a DEFINED projection
of temporal primitives. Endpoint and record event presentations are compared
on raw structural fields; a record increment is checked against the raw clock
on strict events. There is no candidate class, arrow, endpoint or future.
The temporal/run simulation is the existing all-context checked interpreter.
This module does not assemble the enclosing RawHandoff. -/
namespace CSTTT.TargetTheory.GenericHandoff.PresentationCoherence
open RegisterInterpreter RegisterInitialization
variable {Cell S A O H Route Stage Id Owner : Type} {Value : Cell → Type}

def factor (d : TemporalFactorRules.Raw S A O H Route Stage Id Owner) :
    FactorTransport.Data S A O Owner :=
  ⟨d.rows,d.positions,d.hazards,d.policy,d.ticks,d.resource,d.ledger⟩

def factorView (v : TemporalFactorCells.Bindings Cell Value S A O H Route Stage Id Owner) :
    StaticView Cell Value (FactorTransport.Data S A O Owner) :=
  ⟨.map (fun p => ⟨p.1.1,p.1.2,p.2.1.1,p.2.1.2,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩)
    (.pair (.pair (StaticView.ofCell v.rows).instruction (StaticView.ofCell v.positions).instruction)
      (.pair (.pair (StaticView.ofCell v.hazards).instruction (StaticView.ofCell v.policy).instruction)
        (.pair (StaticView.ofCell v.ticks).instruction
          (.pair (StaticView.ofCell v.resource).instruction (StaticView.ofCell v.ledger).instruction))))⟩

theorem factor_dependencies (v : TemporalFactorCells.Bindings Cell Value S A O H Route Stage Id Owner) :
    (factorView v).dependencies =
      [v.rows.cell,v.positions.cell,v.hazards.cell,v.policy.cell,v.ticks.cell,v.resource.cell,v.ledger.cell] := rfl

theorem decoded_fields (v : TemporalFactorCells.Bindings Cell Value S A O H Route Stage Id Owner)
    (a : Assignment Cell Value) (d : TemporalFactorRules.Raw S A O H Route Stage Id Owner)
    (hd : TemporalFactorCells.decoded v a = some d) :
    v.rows.read a = some d.rows ∧
    v.positions.read a = some d.positions ∧
    v.hazards.read a = some d.hazards ∧
    v.policy.read a = some d.policy ∧
    v.classes.read a = some d.classes ∧
    v.publishedP.read a = some d.publishedP ∧
    v.ticks.read a = some d.ticks ∧
    v.resource.read a = some d.resource ∧
    v.ledger.read a = some d.ledger ∧
    v.interface.read a = some d.interface ∧
    v.histories.read a = some d.histories ∧
    v.events.read a = some d.events ∧
    v.realized.read a = some d.realized ∧
    v.receiverFunded.read a = some d.receiverFunded ∧
    v.routes.read a = some d.routes ∧
    v.writers.read a = some d.writers := by
  unfold TemporalFactorCells.decoded at hd
  cases h_rows : v.rows.read a <;> simp_all
  cases h_positions : v.positions.read a <;> simp_all
  cases h_hazards : v.hazards.read a <;> simp_all
  cases h_policy : v.policy.read a <;> simp_all
  cases h_classes : v.classes.read a <;> simp_all
  cases h_publishedP : v.publishedP.read a <;> simp_all
  cases h_ticks : v.ticks.read a <;> simp_all
  cases h_resource : v.resource.read a <;> simp_all
  cases h_ledger : v.ledger.read a <;> simp_all
  cases h_interface : v.interface.read a <;> simp_all
  cases h_histories : v.histories.read a <;> simp_all
  cases h_events : v.events.read a <;> simp_all
  cases h_realized : v.realized.read a <;> simp_all
  cases h_receiverFunded : v.receiverFunded.read a <;> simp_all
  cases h_routes : v.routes.read a <;> simp_all
  cases h_writers : v.writers.read a <;> simp_all
  cases hd
  simp

theorem factor_decoded (v : TemporalFactorCells.Bindings Cell Value S A O H Route Stage Id Owner)
    (a : Assignment Cell Value) (d : TemporalFactorRules.Raw S A O H Route Stage Id Owner)
    (hd : TemporalFactorCells.decoded v a = some d) :
    (factorView v).read a = some (factor d) := by
  obtain ⟨hr,hp,hh,hpol,_,_,ht,hres,hl,_⟩ := decoded_fields v a d hd
  change (a v.rows.cell).map v.rows.project = _ at hr
  change (a v.positions.cell).map v.positions.project = _ at hp
  change (a v.hazards.cell).map v.hazards.project = _ at hh
  change (a v.policy.cell).map v.policy.project = _ at hpol
  change (a v.ticks.cell).map v.ticks.project = _ at ht
  change (a v.resource.cell).map v.resource.project = _ at hres
  change (a v.ledger.cell).map v.ledger.project = _ at hl
  simp only [factorView,StaticView.read,StaticView.ofCell,Expr.eval,hr,hp,hh,hpol,ht,hres,hl,factor]
  rfl

/-- Missing factor input rejects its own interpreter, with no requirement
that the larger temporal decoder was ready beforehand. -/
theorem missing_factor (v : TemporalFactorCells.Bindings Cell Value S A O H Route Stage Id Owner)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ (factorView v).dependencies)
    (hm : a k = none) : (factorView v).read a = none := (factorView v).missing a k hk hm

theorem factor_predictive (cfg : TemporalFactorRules.Schema S A O H Route Stage Id Owner)
    (d : TemporalFactorRules.Raw S A O H Route Stage Id Owner) (s : S) :
    FactorTransport.classOf cfg (factor d) s = ProfileRules.predictive (TemporalFactorRules.profile cfg d) s := rfl

theorem factor_action [DecidableEq S] (cfg : TemporalFactorRules.Schema S A O H Route Stage Id Owner)
    (d : TemporalFactorRules.Raw S A O H Route Stage Id Owner) (s u : S) (act : A) :
    FactorTransport.actionWeight cfg (factor d) s act u =
      ((d.rows s act).map fun e => if cfg.base.destination e.1 = some u then e.2 else 0).sum := rfl

/-- The structural event identity does not silently equate different increment
conventions. The separate increment equation below applies where strictness
is actually certified. -/
def eventShape (e : AcquisitionExecution.Event Stage) : AcquisitionEndpoint.SupportedEvent Stage Id → Prop :=
  fun v => e.fromStage = v.fromStage ∧ e.toStage = v.toStage ∧
    e.sourceSupport = v.sourceSupport ∧ e.targetSupport = v.targetSupport ∧
    e.strictStep = v.strictStep ∧ e.atomic = v.atomic

def executionShape (e : AcquisitionExecution.Event Stage) :=
  (e.fromStage,e.toStage,e.sourceSupport,e.targetSupport,e.strictStep,e.atomic)
def endpointShape (e : AcquisitionEndpoint.SupportedEvent Stage Id) :=
  (e.fromStage,e.toStage,e.sourceSupport,e.targetSupport,e.strictStep,e.atomic)

def temporalEvent (e : AcquisitionEndpoint.SupportedEvent Stage Id) : TemporalFactorRules.Event Stage Id :=
  ⟨e.id,e.fromStage,e.toStage,e.atomic,e.strictStep⟩

variable [DecidableEq Id]
structure RecordLaws (d : AcquisitionEndpoint.Data S A O H Route Stage Id Owner)
    (r : RecordComponent.Data Stage Id Route) (clock : Stage → Nat) : Prop where
  events : ∀ i, (r.events i).map executionShape =
    (AcquisitionEndpoint.event d i).map endpointShape
  sourceEvents : d.source.events = d.events.map temporalEvent
  targetEvents : d.target.events = d.events.map temporalEvent
  sourceRealized : d.source.realized = d.target.realized
  realized : r.realized = d.target.realized
  sourceWriter : r.sourceWriter = d.source.writers
  targetWriter : r.targetWriter = d.target.writers
  clock : r.clock = clock

omit [DecidableEq Id] in
theorem record_increment [DecidableEq Stage] (r : RecordComponent.Data Stage Id Route)
    (e : AcquisitionExecution.Event Stage) (hs : RecordComponent.strict r e = true) :
    e.orderAdvance > 0 ∧ r.clock e.toStage = r.clock e.fromStage + e.orderAdvance := by
  simp only [RecordComponent.strict,Bool.and_eq_true,decide_eq_true_eq] at hs
  exact hs.2

theorem record_writer_guard (d : AcquisitionEndpoint.Data S A O H Route Stage Id Owner)
    (r : RecordComponent.Data Stage Id Route) (clock : Stage → Nat) (route : Route)
    (bad : r.targetWriter route ≠ d.target.writers route) : ¬ RecordLaws d r clock :=
  fun h => bad (congrFun h.targetWriter route)

theorem record_clock_guard (d : AcquisitionEndpoint.Data S A O H Route Stage Id Owner)
    (r : RecordComponent.Data Stage Id Route) (clock : Stage → Nat) (s : Stage)
    (bad : r.clock s ≠ clock s) : ¬ RecordLaws d r clock :=
  fun h => bad (congrFun h.clock s)

theorem record_realization_guard (d : AcquisitionEndpoint.Data S A O H Route Stage Id Owner)
    (r : RecordComponent.Data Stage Id Route) (clock : Stage → Nat)
    (bad : r.realized ≠ d.target.realized) : ¬ RecordLaws d r clock := fun h => bad h.realized

theorem record_event_guard (d : AcquisitionEndpoint.Data S A O H Route Stage Id Owner)
    (r : RecordComponent.Data Stage Id Route) (clock : Stage → Nat) (i : Id)
    (bad : (r.events i).map executionShape ≠ (AcquisitionEndpoint.event d i).map endpointShape) :
    ¬ RecordLaws d r clock := fun h => bad (h.events i)

omit [DecidableEq Id] in
theorem factor_field_guard {X : Type} (d : TemporalFactorRules.Raw S A O H Route Stage Id Owner)
    (proposal : FactorTransport.Data S A O Owner) (field : FactorTransport.Data S A O Owner → X)
    (bad : field proposal ≠ field (factor d)) : proposal ≠ factor d :=
  fun h => bad (congrArg field h)

/-- Raw presentation instructions and schema operations. The common finite
coordinate alphabet does NOT identify the separately typed source/receiver
register frames. Factor and endpoint objects are derived below. -/
structure Raw (Cell : Type) (Value : Cell → Type) (SR TR : Type)
    (SRV : SR → Type) (TRV : TR → Type) (S A O H Route Stage Id Owner D : Type) where
  source : TemporalRuntimeCoherence.Raw Cell Value SR SRV S A O H Route Stage Id Owner D
  target : TemporalRuntimeCoherence.Raw Cell Value TR TRV S A O H Route Stage Id Owner D
  events : CellView Cell Value (List (AcquisitionEndpoint.SupportedEvent Stage Id))
  receiver : CellView Cell Value AcquisitionExecution.Receiver
  entry : Stage
  exit : Stage
  exitEvent : Id
  fallback : S
  rowScale : Nat
  transfer : S → S
  clock : Stage → Nat
  factorMaps : StaticView Cell Value (FactorTransport.Maps S S A A Owner)
  record : StaticView Cell Value (RecordComponent.Data Stage Id Route)

variable {SR TR D : Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => Raw Cell Value SR TR SRV TRV S A O H Route Stage Id Owner D

def endpointSchema (m : Model) : AcquisitionEndpoint.Schema S A O H Route Stage Id Owner :=
  ⟨m.source.schema,m.target.schema,m.entry,m.exit,m.exitEvent,m.fallback,m.rowScale,m.transfer⟩
def endpointBindings (m : Model) : AcquisitionEndpoint.Bindings Cell Value S A O H Route Stage Id Owner :=
  ⟨m.source.bindings,m.target.bindings,m.events,m.receiver⟩
def factorBindings (m : Model) : FactorTransport.Binding Cell Value S S A A O O H Route Stage Id Owner :=
  ⟨factorView m.source.bindings,factorView m.target.bindings,m.factorMaps⟩

omit [DecidableEq Id] in
/-- These are literal interface equations, not passed Boolean flags. -/
theorem endpoint_source (m : Model) : (endpointBindings m).source = m.source.bindings := rfl
omit [DecidableEq Id] in
theorem endpoint_target (m : Model) : (endpointBindings m).target = m.target.bindings := rfl
omit [DecidableEq Id] in
theorem factor_source (m : Model) : (factorBindings m).source = factorView m.source.bindings := rfl
omit [DecidableEq Id] in
theorem factor_target (m : Model) : (factorBindings m).target = factorView m.target.bindings := rfl

variable [DecidableEq S] [DecidableEq Route] [DecidableEq Stage]
/-- This is a coherence check, not a package, lineage or autonomy verdict.
ALL run contexts are covered by the temporal simulation laws. Decode absence
rejects endpoint and record use before any fallback can be observed. -/
def Pass (m : Model) (a : Assignment Cell Value) : Prop :=
  (∃ hs : TemporalRuntimeCoherence.Ready m.source a, TemporalRuntimeCoherence.Laws m.source a hs) ∧
  (∃ ht : TemporalRuntimeCoherence.Ready m.target a, TemporalRuntimeCoherence.Laws m.target a ht) ∧
  ∃ d r, AcquisitionEndpoint.decoded (endpointBindings m) a = some d ∧
    m.record.read a = some r ∧ RecordLaws d r m.clock ∧
      m.clock = m.source.schema.stages.idxOf ∧ m.clock = m.target.schema.stages.idxOf

omit [DecidableEq Id] [DecidableEq S] [DecidableEq Route] [DecidableEq Stage] in
/-- Both factor decoders are extracted from one checked endpoint primitive
record. They cannot contain a separately chosen action table or M alphabet. -/
theorem endpoint_factor_decoded (m : Model) (a : Assignment Cell Value)
    (d : AcquisitionEndpoint.Data S A O H Route Stage Id Owner)
    (hd : AcquisitionEndpoint.decoded (endpointBindings m) a = some d) :
    (factorBindings m).source.read a = some (factor d.source) ∧
      (factorBindings m).target.read a = some (factor d.target) := by
  unfold AcquisitionEndpoint.decoded at hd
  cases hs : TemporalFactorCells.decoded (endpointBindings m).source a <;> simp_all
  cases ht : TemporalFactorCells.decoded (endpointBindings m).target a <;> simp_all
  cases he : (endpointBindings m).events.read a <;> simp_all
  cases hr : (endpointBindings m).receiver.read a <;> simp_all
  cases hd
  exact ⟨factor_decoded _ _ _ hs,factor_decoded _ _ _ ht⟩

theorem missing_endpoint_rejected (m : Model) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ (endpointBindings m).scope) (hm : a k = none) : ¬ Pass m a := by
  rintro ⟨_,_,d,_,hd,_⟩
  rw [AcquisitionEndpoint.missing_input _ a k hk hm] at hd
  contradiction

theorem missing_record_rejected (m : Model) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ m.record.dependencies) (hm : a k = none) : ¬ Pass m a := by
  rintro ⟨_,_,_,r,_,hr,_⟩
  rw [m.record.missing a k hk hm] at hr
  contradiction

/-- All-context guards reject coherent interpretation itself; they do not
infer a semantic failure merely from failure of clause acceptance. -/
theorem source_row_guard (m : Model) (a : Assignment Cell Value)
    (h : TemporalRuntimeCoherence.Ready m.source a)
    (x : Registers SR SRV) (da : D × A)
    (bad : RegisterFuture.row m.source.runtime a h.2.1 x da ≠
      TemporalFactorRules.actualRows m.source.schema (TemporalRuntimeCoherence.data m.source a h)
        (TemporalRuntimeCoherence.project m.source a h x) da.2) : ¬ Pass m a :=
  fun hp => bad (hp.1.choose_spec.rows x da)

theorem target_row_guard (m : Model) (a : Assignment Cell Value)
    (h : TemporalRuntimeCoherence.Ready m.target a)
    (x : Registers TR TRV) (da : D × A)
    (bad : RegisterFuture.row m.target.runtime a h.2.1 x da ≠
      TemporalFactorRules.actualRows m.target.schema (TemporalRuntimeCoherence.data m.target a h)
        (TemporalRuntimeCoherence.project m.target a h x) da.2) : ¬ Pass m a :=
  fun hp => bad (hp.2.1.choose_spec.rows x da)

theorem source_update_guard (m : Model) (a : Assignment Cell Value)
    (h : TemporalRuntimeCoherence.Ready m.source a)
    (x : Registers SR SRV) (da : D × A) (o : O)
    (bad : TemporalRuntimeCoherence.project m.source a h
        (RegisterFuture.next m.source.runtime a h.2.1 x da o) ≠
      TemporalFactorRules.update m.source.schema (TemporalRuntimeCoherence.data m.source a h)
        (TemporalRuntimeCoherence.project m.source a h x) da.2 o) : ¬ Pass m a :=
  fun hp => bad (hp.1.choose_spec.successor x da o)

theorem source_readout_guard {X : Type} (m : Model) (a : Assignment Cell Value)
    (h : TemporalRuntimeCoherence.Ready m.source a) (x : Registers SR SRV)
    (field : CSTTT.TransportTheory.TemporalSnapshotReadout (TemporalFactorRules.Predictive O) (List S × List Id) Bool → X)
    (bad : field (RegisterFuture.observation m.source.runtime a h.2.1 x) ≠
      field (TemporalRuntimeCoherence.observationImage m.source.owner
        (TemporalFactorRules.observe m.source.schema (TemporalRuntimeCoherence.data m.source a h)
          m.source.runtime.tickPeriod (TemporalRuntimeCoherence.project m.source a h x)))) : ¬ Pass m a :=
  fun hp => bad (congrArg field (hp.1.choose_spec.observation x))

end CSTTT.TargetTheory.GenericHandoff.PresentationCoherence
