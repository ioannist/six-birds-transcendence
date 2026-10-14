import CSTTT.Targets.GenericHandoff.AcquisitionEndpoint
import CSTTT.Targets.GenericHandoff.RuntimeRoute
import CSTTT.Targets.GenericHandoff.ExecutedAcquisitionCorridor
import CSTTT.Targets.GenericHandoff.SemanticExecutionBridge
import CSTTT.Targets.GenericHandoff.ExecutionLink
import CSTTT.Targets.GenericHandoff.FactorTransport
import CSTTT.Targets.GenericHandoff.RecordComponent

/-! Polymorphic shared-runtime lineage core, TTH-06.
The source/receiver presentations are raw register instruction frames. Their
execution links to the shared runtime are constructed and checked, with actual
positive-support coverage. The bridge, corridor, snapshots, futures, factor
word probes, record arrows and Indexed/Retained route status are defined from
these instructions and one immutable assignment. No verdict or candidate
semantic object is an argument.
The complete readout now includes the independently computed typed acquisition
endpoint rule. Public cross-component coordinate/owner coherence and final
RawHandoff assembly remain enclosing obligations. -/
namespace CSTTT.TargetTheory.GenericHandoff.RuntimeLineage
open RegisterInterpreter CSTTT.TransportTheory CSTTT.RecordTheory

/-- Separately typed raw factor interfaces and instruction decoders. -/
structure FactorRaw (Cell : Type) (Value : Cell → Type) where
  Source : Type
  Target : Type
  SourceAction : Type
  TargetAction : Type
  SourceOutcome : Type
  TargetOutcome : Type
  History : Type
  Route : Type
  Stage : Type
  Id : Type
  Owner : Type
  sourceEq : DecidableEq Source
  targetEq : DecidableEq Target
  ownerEq : DecidableEq Owner
  source : TemporalFactorRules.Schema Source SourceAction SourceOutcome History Route Stage Id Owner
  target : TemporalFactorRules.Schema Target TargetAction TargetOutcome History Route Stage Id Owner
  instructions : FactorTransport.Binding Cell Value Source Target SourceAction TargetAction
    SourceOutcome TargetOutcome History Route Stage Id Owner

variable {Cell : Type} {Value : Cell → Type}

def FactorReadout (raw : FactorRaw Cell Value) (a : Assignment Cell Value) : Prop :=
  letI := raw.sourceEq
  letI := raw.targetEq
  letI := raw.ownerEq
  FactorTransport.Pass raw.source raw.target raw.instructions a

/-- Actual computed equations derive the all-word factor consequence. -/
theorem factor_words (raw : FactorRaw Cell Value) (a : Assignment Cell Value)
    (h : FactorReadout raw a) :
    letI := raw.sourceEq
    letI := raw.targetEq
    letI := raw.ownerEq
    ∃ ds dt maps, raw.instructions.source.read a = some ds ∧
      raw.instructions.target.read a = some dt ∧ raw.instructions.maps.read a = some maps ∧
      ∀ w s u, FactorTransport.word raw.target dt (maps.state s) (w.map maps.action) (maps.state u) =
        FactorTransport.word raw.source ds s w u := by
  letI := raw.sourceEq
  letI := raw.targetEq
  letI := raw.ownerEq
  obtain ⟨ds,dt,maps,hs,ht,hm,he⟩ := h
  exact ⟨ds,dt,maps,hs,ht,hm,FactorTransport.word_transport _ _ _ _ _ he⟩

theorem missing_factor_rejected (raw : FactorRaw Cell Value) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ raw.instructions.scope) (hm : a k = none) : ¬ FactorReadout raw a := by
  letI := raw.sourceEq
  letI := raw.targetEq
  letI := raw.ownerEq
  exact FactorTransport.missing_rejected _ _ _ _ k hk hm

structure Raw (Cell : Type) (Value : Cell → Type)
    (R S T : Type) (RV : R → Type) (SV : S → Type) (TV : T → Type)
    (D A O P Q Factor Resource Residue Maintenance Endpoint Stage Id History RouteId : Type) where
  schema : RuntimeComponents.Schema Factor Resource Stage Id History RouteId
  runtime : RuntimeComponents.Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId
  source : ExecutionFrontier.Raw Cell Value S SV D A O P Residue Maintenance Stage Id History RouteId
  target : ExecutionFrontier.Raw Cell Value T TV D A O Q Residue Maintenance Stage Id History RouteId
  sourceEmbedding : (k : R) → Expr Cell Value S SV Unit (RV k)
  targetEmbedding : (k : R) → Expr Cell Value T TV Unit (RV k)
  translation : (k : T) → Expr Cell Value S SV Unit (TV k)
  maps : SnapshotRawMaps P Q Residue Maintenance
  names : AcquisitionCorridor.Names Id
  seeds : StaticView Cell Value (AcquisitionCorridor.Seeds History)
  predictiveCoordinate : StaticView Cell Value (P → Nat)
  historyCoordinate : Residue → List String
  routeCoordinate : Residue → List String
  factor : FactorRaw Cell Value
  recordSchema : RecordComponent.Schema Id RouteId
  record : StaticView Cell Value (RecordComponent.Data Stage Id RouteId)
  endpoint : AcquisitionEndpoint.Interface Cell Value
  route : RuntimeComponents.RouteInstructions Cell Value R RV D A O Id History Residue Endpoint

variable {R S T D A O P Q Factor Resource Residue Maintenance Endpoint Stage Id History RouteId : Type}
  {RV : R → Type} {SV : S → Type} {TV : T → Type}
local notation "Model" => Raw Cell Value R S T RV SV TV D A O P Q Factor Resource Residue Maintenance Endpoint Stage Id History RouteId

def bridge (raw : Model) := ExecutionBridge.Raw.mk raw.source raw.target raw.translation raw.maps

def executed (raw : Model) := ExecutedAcquisitionCorridor.Raw.mk raw.source raw.names raw.seeds
  raw.predictiveCoordinate raw.historyCoordinate raw.routeCoordinate

def corridor (raw : Model) := ExecutedAcquisitionCorridor.corridor (executed raw)

def sourceLink (raw : Model) := ExecutionLink.Raw.mk raw.source.acquisition.execution
  raw.runtime.execution raw.sourceEmbedding

def targetLink (raw : Model) := ExecutionLink.Raw.mk raw.target.acquisition.execution
  raw.runtime.execution raw.targetEmbedding

/-- Exact probabilities and actual updates at all contexts, including support
coverage. Shared stage/carrier/domain interfaces are checked raw equations. -/
def SharedExecution (raw : Model) (a : Assignment Cell Value) : Prop :=
  raw.source.schema = RuntimeComponents.acquisitionSchema raw.schema ∧
  raw.target.schema = RuntimeComponents.acquisitionSchema raw.schema ∧
  ExecutionLink.Pass (sourceLink raw) a ∧ ExecutionLink.Pass (targetLink raw) a

variable [DecidableEq O] [DecidableEq Stage] [DecidableEq P] [DecidableEq Q]
  [DecidableEq Residue] [DecidableEq Maintenance]

def CorridorReadout (raw : Model) (a : Assignment Cell Value) : Prop :=
  ∀ r ∈ raw.source.schema.routes, AcquisitionCorridor.Readout (corridor raw) a r

def SeedReadout (raw : Model) (a : Assignment Cell Value) : Prop :=
  ∃ h : ExecutionFrontier.Ready raw.source a, ∀ v,
    AcquisitionCorridor.read (corridor raw) a = some v →
      ExecutedAcquisitionCorridor.SeedCoherence (executed raw) a h v

/-- Arrow preservation, decoded without defaults. Nonempty arrows are an
optional stronger certifier; full run advancement is separately semantic. -/
def RecordReadout (raw : Model) (a : Assignment Cell Value) : Prop :=
  ∃ d, raw.record.read a = some d ∧
    ∀ i j, SourceArrow (RecordComponent.transport raw.recordSchema d) i j →
      TargetArrow (RecordComponent.transport raw.recordSchema d) i j

def CoreReadout (raw : Model) (a : Assignment Cell Value) : Prop :=
  CorridorReadout raw a ∧ SeedReadout raw a ∧ FactorReadout raw.factor a ∧
    RecordReadout raw a ∧
    RuntimeComponents.RetainedRouteReadout raw.schema raw.runtime raw.route a ∧
    ExecutionBridge.SemanticReadout (bridge raw) a ∧ SharedExecution raw a

/-- Component certification differs from its semantic readout: complete
all-word sufficiency is derived, not an input verdict. -/
def Pass (raw : Model) (a : Assignment Cell Value) : Prop :=
  AcquisitionCorridor.Pass (corridor raw) a ∧ SeedReadout raw a ∧
    FactorReadout raw.factor a ∧ RecordReadout raw a ∧
    RuntimeComponents.RetainedRouteReadout raw.schema raw.runtime raw.route a ∧
    ExecutionBridge.Valid (bridge raw) a ∧ SharedExecution raw a

theorem soundness (raw : Model) (a : Assignment Cell Value) (h : Pass raw a) : CoreReadout raw a :=
  ⟨fun r hr => AcquisitionCorridor.constructs _ _ h.1 r hr,h.2.1,h.2.2.1,h.2.2.2.1,
    h.2.2.2.2.1,ExecutionBridge.semantic_soundness _ _ h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

theorem route_status (raw : Model) (a : Assignment Cell Value) (h : CoreReadout raw a) :
    RuntimeComponents.retainedRouteStatus raw.schema raw.runtime raw.route a = .routeIndexed :=
  (RuntimeComponents.retained_route_status_iff _ _ _ _).mpr h.2.2.2.2.1

/-- All eight frozen fields and full-interface unbounded futures. -/
theorem frozen_transport (raw : Model) (a : Assignment Cell Value) (h : CoreReadout raw a) :
    ∃ hs : ExecutionFrontier.Ready raw.source a, ∃ ht : ExecutionFrontier.Ready raw.target a,
      ∃ _hm : ExecutionBridge.TranslationReady (bridge raw) a,
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.source) a hs.2) ∧
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.target) a ht.2) ∧
      ∃ hc : SnapshotMapCheck raw.source.audit (ExecutionFrontier.observation raw.source a hs)
          (ExecutionFrontier.observation raw.target a ht) raw.maps,
        ∀ i : Audited raw.source.audit,
          transportFrozenSnapshot raw.source.audit (ExecutionFrontier.observation raw.source a hs)
            (ExecutionFrontier.observation raw.target a ht) raw.maps hc
            (ExecutionFrontier.frozen raw.source a hs i) =
          frozenSnapshot (RegisterFuture.future (ExecutionFrontier.temporal raw.target) a ht.2)
            raw.source.audit (ExecutionFrontier.observation raw.target a ht) i :=
  ExecutionBridge.semantic_frozen_transport (bridge raw) a h.2.2.2.2.2.1

/-- No actual positive branch escapes the shared updater equation. -/
theorem source_positive_branch (raw : Model) (a : Assignment Cell Value)
    (h : CoreReadout raw a) (ready : ExecutionLink.Ready (sourceLink raw) a)
    (x : Registers S SV) (d : D) (hd : d ∈ raw.source.acquisition.execution.disturbances)
    (act : A) (ha : act ∈ raw.source.acquisition.execution.actions) (o : O)
    (ho : StrategyGame.PositiveSupport (ExecutionLink.rows raw.source.acquisition.execution a) x d act o) :
    ExecutionLink.embed (sourceLink raw) a ready
        (ExecutionLink.update raw.source.acquisition.execution a ready.1 x d act o) =
      ExecutionLink.update raw.runtime.execution a ready.2.1
        (ExecutionLink.embed (sourceLink raw) a ready x) d act o := by
  obtain ⟨other,laws⟩ := h.2.2.2.2.2.2.2.2.1
  exact ExecutionLink.positive_successor (sourceLink raw) a ready laws x d hd act ha o ho

/-- Direct semantic rejection, with no contradictory readiness premise. -/
theorem missing_atomic_no_readout (raw : Model) (a : Assignment Cell Value)
    (hm : raw.source.acquisition.events.read a = none) : ¬ CoreReadout raw a :=
  fun h => ExecutionBridge.missing_atomic_no_semantic_readout (bridge raw) a hm h.2.2.2.2.2.1

theorem missing_record_no_readout (raw : Model) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ raw.record.dependencies) (hm : a k = none) : ¬ CoreReadout raw a := by
  rintro ⟨_,_,_,⟨d,hd,_⟩,_⟩
  rw [raw.record.missing a k hk hm] at hd
  contradiction

theorem missing_factor_no_readout (raw : Model) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ raw.factor.instructions.scope) (hm : a k = none) : ¬ CoreReadout raw a :=
  fun h => missing_factor_rejected _ _ k hk hm h.2.2.1


omit [DecidableEq O] [DecidableEq P] [DecidableEq Q] [DecidableEq Residue] [DecidableEq Maintenance] in
/-- Stronger record audit implies the independently defined arrow readout. -/
theorem record_soundness (raw : Model) (a : Assignment Cell Value)
    (h : RecordComponent.Pass raw.recordSchema raw.record a) : RecordReadout raw a := by
  obtain ⟨d,hd,hc⟩ := h
  exact ⟨d,hd,RecordComponent.sound raw.recordSchema d hc⟩

theorem schema_mismatch_no_readout (raw : Model) (a : Assignment Cell Value)
    (bad : raw.source.schema ≠ RuntimeComponents.acquisitionSchema raw.schema ∨
      raw.target.schema ≠ RuntimeComponents.acquisitionSchema raw.schema) : ¬ CoreReadout raw a := by
  intro h
  rcases bad with bad | bad
  · exact bad h.2.2.2.2.2.2.1
  · exact bad h.2.2.2.2.2.2.2.1

/-- A real raw-row/program mismatch precludes the semantic representation
link. This is not a negative inferred from a sufficient future certifier. -/
theorem source_link_no_readout (raw : Model) (a : Assignment Cell Value)
    (bad : ¬ ExecutionLink.Pass (sourceLink raw) a) : ¬ CoreReadout raw a :=
  fun h => bad h.2.2.2.2.2.2.2.2.1

theorem target_link_no_readout (raw : Model) (a : Assignment Cell Value)
    (bad : ¬ ExecutionLink.Pass (targetLink raw) a) : ¬ CoreReadout raw a :=
  fun h => bad h.2.2.2.2.2.2.2.2.2

theorem empty_route_domain_no_readout (raw : Model) (a : Assignment Cell Value)
    (bad : raw.schema.routes = []) : ¬ CoreReadout raw a :=
  fun h => RuntimeComponents.empty_domain_no_retained_routes _ _ _ _ bad h.2.2.2.2.1

theorem constant_residue_no_readout (raw : Model) (a : Assignment Cell Value) (c : Residue)
    (bad : ∀ x, raw.runtime.resource.residue.eval a x () = some c) : ¬ CoreReadout raw a :=
  fun h => RuntimeComponents.constant_register_no_retained_routes _ _ _ _ c bad h.2.2.2.2.1

/-- Complete runtime lineage, including the extracted typed endpoint rule.
CoreReadout is retained as the old, explicitly endpoint-free result. -/
def StrictTemporalLineage (raw : Model) (a : Assignment Cell Value) : Prop :=
  CoreReadout raw a ∧ AcquisitionEndpoint.Readout raw.endpoint a

def CompletePass (raw : Model) (a : Assignment Cell Value) : Prop :=
  Pass raw a ∧ AcquisitionEndpoint.Readout raw.endpoint a

theorem complete_soundness (raw : Model) (a : Assignment Cell Value)
    (h : CompletePass raw a) : StrictTemporalLineage raw a :=
  ⟨soundness raw a h.1,h.2⟩

theorem missing_endpoint_no_lineage (raw : Model) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ raw.endpoint.bindings.scope) (hm : a k = none) :
    ¬ StrictTemporalLineage raw a :=
  fun h => AcquisitionEndpoint.missing_no_readout _ _ k hk hm h.2

end CSTTT.TargetTheory.GenericHandoff.RuntimeLineage
