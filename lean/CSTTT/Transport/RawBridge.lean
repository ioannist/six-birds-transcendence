import CSTTT.Transport.FiniteTemporalTransport
import CSTTT.Transport.RawRecordArrow
import CSTTT.Transport.FutureDynamics
import CSTTT.Transport.SnapshotImages

/-! TTH-03 raw bridge. The old bundled theorem remains a schema interface.
Every field below is raw data. The premises are equations on that data; the
history/signature and representative conclusions are derived from them. -/
namespace CSTTT.TransportTheory

open CSTTT.RecordTheory

structure RawBridge
    (History SourceState TargetState Event Route SourceClass TargetClass
      Residue Maintenance : Type) where
  frontier : List History
  sourceHistory : History → List SourceState
  targetHistory : History → List TargetState
  mapState : SourceState → TargetState
  sourceCoord : SourceState → Nat
  targetCoord : TargetState → Nat
  mapCoord : Nat → Nat
  sourceClass : SourceState → SourceClass
  targetClass : TargetState → TargetClass
  mapClass : SourceClass → TargetClass
  sourceStates : List SourceState
  targetStates : List TargetState
  sourceClassDecEq : DecidableEq SourceClass
  targetClassDecEq : DecidableEq TargetClass
  sourceActionStep : SourceState → Nat → SourceState → Nat
  targetActionStep : TargetState → Nat → TargetState → Nat
  sourceStep : SourceState → SourceState → Nat
  targetStep : TargetState → TargetState → Nat
  sourceOrder : History → List Nat
  targetOrder : History → List Nat
  sourceTick : SourceState → Nat
  targetTick : TargetState → Nat
  sourceProgress : History → Nat
  targetProgress : History → Nat
  sourceProgressAt : History → Nat → Nat
  targetProgressAt : History → Nat → Nat
  record : RawRecordTransport Event Event
  routeIds : List Route
  routeHistory : Route → History
  sourceRoute : Route → List Event
  targetRoute : Route → List Event
  sourceResidue : Route → Residue
  targetResidue : Route → Residue
  sourceReadout : Route → Option Nat
  targetReadout : Route → Option Nat
  targetRouteSteps : Route → List (Residue × Nat)
  sourceMaintenance : SourceState → Maintenance
  targetMaintenance : TargetState → Maintenance
  mapMaintenance : Maintenance → Maintenance
  sourceOwner : SourceState → CarrierId
  targetOwner : TargetState → CarrierId
  targetId : CarrierId

  /-- Full run-level raw dynamics, including ambient exits and counters.
  These are bridge data, not a candidate future-model argument. The check
  below ties their in-carrier rows and counters to the factor bridge. -/
  RunState : Type
  RunAction : Type
  RunOutcome : Type
  runOutcomeDecEq : DecidableEq RunOutcome
  runOutcomes : List RunOutcome
  runDenominator : Nat
  runNumerator : RunState → RunAction → RunOutcome → Nat
  runUpdate : RunState → RunAction → RunOutcome → RunState
  runSourceFactor : RunState → Option SourceState
  runTargetFactor : RunState → Option TargetState
  runSourceOutcome : SourceState → RunOutcome
  runTargetOutcome : TargetState → RunOutcome
  runActionIndex : RunAction → Nat
  runEnabled : RunState → Bool
  runCounter : RunState → Nat
  runTicks : RunState → Nat

  /-- Individual carrier readouts. There is no stored observation or code. -/
  RunPredictive : Type
  runPredictiveDecEq : DecidableEq RunPredictive
  residueDecEq : DecidableEq Residue
  maintenanceDecEq : DecidableEq Maintenance
  runPredictive : RunState → RunPredictive
  sourcePredictiveMap : SourceClass → RunPredictive
  targetPredictiveMap : TargetClass → RunPredictive
  runProgress : RunState → Nat
  runRecordWriter : RunState → Bool
  runResidue : RunState → Residue
  runMaintenance : RunState → Maintenance
  runOwner : RunState → CarrierId
  runRecord : RunState → Nat
  /-- Raw component update recipes, independent of the aggregate observer.
  These are numerical/table functions, never propositions or proof fields. -/
  runSourceFactorUpdate : RunState → RunAction → RunOutcome → Option SourceState
  runTargetFactorUpdate : RunState → RunAction → RunOutcome → Option TargetState
  runPredictiveUpdate : RunState → RunAction → RunOutcome → RunPredictive
  runTickAdvance : RunState → RunAction → RunOutcome → Nat
  runProgressAdvance : RunState → RunAction → RunOutcome → Nat
  runWriterRule : Residue → CarrierId → Bool
  runResidueUpdate : Residue → RunAction → RunOutcome → Residue
  runMaintenanceUpdate : Maintenance → RunAction → RunOutcome → Maintenance
  runOwnerUpdate : CarrierId → RunAction → RunOutcome → CarrierId
  runEnabledRule : Maintenance → CarrierId → Bool
  runTickPeriod : Nat
  /-- Raw finite audit selectors and typed carrier constructors. Snapshot
  contexts and run embeddings are constructed from these, never supplied. -/
  AuditIndex : Type
  auditFrontier : List AuditIndex
  auditHistory : AuditIndex → History
  auditState : AuditIndex → SourceState
  auditOccurrence : AuditIndex → Nat
  auditEvent : AuditIndex → Event
  auditRoute : AuditIndex → Route
  makeSourceRun : SourceState → Nat → Nat → Residue → Maintenance → RunState
  makeTargetRun : TargetState → Nat → Nat → Residue → Maintenance → RunState

variable {H S T E R SC TC RR M : Type}

/-- The only reference dynamics used by frozen certification. -/
def bridgeRunDynamics (b : RawBridge H S T E R SC TC RR M) :
    RawFutureDynamics b.RunState b.RunAction b.RunOutcome where
  outcomes := b.runOutcomes
  actionRow := fun x a o => (b.runNumerator x a o : Rat) / (b.runDenominator : Rat)
  update := b.runUpdate

/-- Fixed six-component code, including route, maintenance and owner.
Progress and record are observed too; their predictive sufficiency is checked
by the one-step bisimulation of the defined functions. -/
structure TemporalRunCode (P R M : Type) where
  predictive : P
  order : Nat
  tickPhase : Nat
  residue : R
  maintenance : M
  owner : CarrierId
  deriving DecidableEq

abbrev BridgeRunObservation (b : RawBridge H S T E R SC TC RR M) :=
  TemporalSnapshotReadout b.RunPredictive RR M
abbrev BridgeRunCode (b : RawBridge H S T E R SC TC RR M) :=
  TemporalRunCode b.RunPredictive RR M

def bridgeRunObservationDecEq (b : RawBridge H S T E R SC TC RR M) :
    DecidableEq (BridgeRunObservation b) := by
  letI := b.runPredictiveDecEq
  letI := b.residueDecEq
  letI := b.maintenanceDecEq
  exact inferInstance

/-- All eight fields are read from the actual run. In particular event order
is the raw counter, with no cap, audit truncation, or supplied display rule. -/
def bridgeRunObservation (b : RawBridge H S T E R SC TC RR M)
    (x : b.RunState) : BridgeRunObservation b :=
  ⟨b.runPredictive x, b.runCounter x, b.runTicks x % b.runTickPeriod,
    b.runProgress x, b.runRecord x,
    b.runResidue x, b.runMaintenance x, b.runOwner x⟩

def bridgeCodeOfObservation {P R M : Type} (v : TemporalSnapshotReadout P R M) :
    TemporalRunCode P R M :=
  ⟨v.predictive, v.order, v.tickPhase, v.residue, v.maintenance, v.owner⟩

def bridgeRunCode (b : RawBridge H S T E R SC TC RR M) (x : b.RunState) :
    BridgeRunCode b := bridgeCodeOfObservation (bridgeRunObservation b x)

/-- No candidate components: observation, code, weights and successors are
all defined from bridge-owned data. -/
def bridgeFutureModel (b : RawBridge H S T E R SC TC RR M) :
    FullFutureModel b.RunState b.RunAction b.RunOutcome (BridgeRunCode b) (BridgeRunObservation b) where
  outcomes := b.runOutcomes
  code := bridgeRunCode b
  observe := bridgeRunObservation b
  weight := (bridgeRunDynamics b).actionRow
  next := (bridgeRunDynamics b).update

def BridgeFutureBisim (b : RawBridge H S T E R SC TC RR M) : Prop :=
  FullOneStepBisim (bridgeFutureModel b)

def BridgeFutureSufficient (b : RawBridge H S T E R SC TC RR M) : Prop :=
  letI := bridgeRunObservationDecEq b
  FullFutureSufficient (bridgeFutureModel b)

def bridgeFuture (b : RawBridge H S T E R SC TC RR M) (x : b.RunState)
    (word : List b.RunAction) (trace : List (BridgeRunObservation b)) : Rat :=
  letI := bridgeRunObservationDecEq b
  fullFuture (bridgeFutureModel b) x word trace

theorem bridge_defined_future_sufficient (b : RawBridge H S T E R SC TC RR M)
    (h : BridgeFutureBisim b) : BridgeFutureSufficient b := by
  letI := bridgeRunObservationDecEq b
  exact full_future_sufficient_of_bisim (bridgeFutureModel b) h

/-- Raw coherence equations, not a future-sufficiency premise. Core outcome
mass is the pushforward of the bridge's existing action numerators. Ambient
exit rows are additional full-run data owned by this same bridge. Updates
advance the run counter and use the bridge's own factor tick law. -/
def BridgeRunCoherence (b : RawBridge H S T E R SC TC RR M) : Prop :=
  letI := b.runOutcomeDecEq
  0 < b.runDenominator ∧
  (∀ s ∈ b.sourceStates, b.runSourceOutcome s ∈ b.runOutcomes) ∧
  (∀ t ∈ b.targetStates, b.runTargetOutcome t ∈ b.runOutcomes) ∧
  (∀ x a o, 0 < b.runNumerator x a o → o ∈ b.runOutcomes) ∧
  ∀ x a o,
    (∀ s, b.runSourceFactor x = some s → b.runEnabled x = true →
      (∃ t ∈ b.sourceStates, b.runSourceOutcome t = o) →
      b.runNumerator x a o = (b.sourceStates.map fun t =>
        if b.runSourceOutcome t = o then
          b.sourceActionStep s (b.runActionIndex a) t else 0).sum) ∧
    (∀ t, b.runTargetFactor x = some t → b.runEnabled x = true →
      (∃ u ∈ b.targetStates, b.runTargetOutcome u = o) →
      b.runNumerator x a o = (b.targetStates.map fun u =>
        if b.runTargetOutcome u = o then
          b.targetActionStep t (b.runActionIndex a) u else 0).sum) ∧
    b.runCounter (b.runUpdate x a o) = b.runCounter x + 1 ∧
    (∀ s, b.runSourceFactor x = some s →
      b.runTicks (b.runUpdate x a o) = b.runTicks x + b.sourceTick s) ∧
    (∀ t, b.runTargetFactor x = some t →
      b.runTicks (b.runUpdate x a o) = b.runTicks x + b.targetTick t) ∧
    (∀ s, b.runSourceFactor x = some s →
      (∃ t ∈ b.sourceStates, b.runSourceOutcome t = o) →
      ∃ t ∈ b.sourceStates, b.runSourceFactor (b.runUpdate x a o) = some t ∧
        b.runSourceOutcome t = o) ∧
    (∀ t, b.runTargetFactor x = some t →
      (∃ u ∈ b.targetStates, b.runTargetOutcome u = o) →
      ∃ u ∈ b.targetStates, b.runTargetFactor (b.runUpdate x a o) = some u ∧
        b.runTargetOutcome u = o)

/-- Every readout has an explicit step equation. Supported steps also
require genuinely positive progress/tick increments. Unsupported enumerated
simulator steps follow their declared increments (POS-04 still advances its
attempt counter); they are not asserted to be realized funded events.
Writer, funding availability and record are checked both now and after the
update, so a corrupted derived readout cannot hide behind bisimulation. -/
structure BridgeReadoutUpdateAt (b : RawBridge H S T E R SC TC RR M)
    (x : b.RunState) (a : b.RunAction) (o : b.RunOutcome) : Prop where
  sourceFactor : b.runSourceFactor (b.runUpdate x a o) = b.runSourceFactorUpdate x a o
  targetFactor : b.runTargetFactor (b.runUpdate x a o) = b.runTargetFactorUpdate x a o
  predictive : b.runPredictive (b.runUpdate x a o) = b.runPredictiveUpdate x a o
  sourcePredictive : ∀ s, b.runSourceFactor x = some s →
    b.runPredictive x = b.sourcePredictiveMap (b.sourceClass s)
  targetPredictive : ∀ t, b.runTargetFactor x = some t →
    b.runPredictive x = b.targetPredictiveMap (b.targetClass t)
  counter : b.runCounter (b.runUpdate x a o) = b.runCounter x + 1
  ticks : b.runTicks (b.runUpdate x a o) = b.runTicks x + b.runTickAdvance x a o
  progress : b.runProgress (b.runUpdate x a o) = b.runProgress x + b.runProgressAdvance x a o
  supportedAdvances : 0 < b.runNumerator x a o →
    0 < b.runTickAdvance x a o ∧ 0 < b.runProgressAdvance x a o
  residue : b.runResidue (b.runUpdate x a o) = b.runResidueUpdate (b.runResidue x) a o
  maintenance : b.runMaintenance (b.runUpdate x a o) =
    b.runMaintenanceUpdate (b.runMaintenance x) a o
  ownerPreserved : b.runOwnerUpdate (b.runOwner x) a o = b.runOwner x
  owner : b.runOwner (b.runUpdate x a o) = b.runOwnerUpdate (b.runOwner x) a o
  sourceOwner : ∀ s, b.runSourceFactor x = some s → b.runOwner x = b.sourceOwner s
  targetOwner : ∀ t, b.runTargetFactor x = some t → b.runOwner x = b.targetOwner t
  writerNow : b.runRecordWriter x = b.runWriterRule (b.runResidue x) (b.runOwner x)
  writerNext : b.runRecordWriter (b.runUpdate x a o) =
    b.runWriterRule (b.runResidueUpdate (b.runResidue x) a o)
      (b.runOwnerUpdate (b.runOwner x) a o)
  enabledNow : b.runEnabled x = b.runEnabledRule (b.runMaintenance x) (b.runOwner x)
  enabledNext : b.runEnabled (b.runUpdate x a o) =
    b.runEnabledRule (b.runMaintenanceUpdate (b.runMaintenance x) a o)
      (b.runOwnerUpdate (b.runOwner x) a o)
  recordNow : b.runRecord x = if b.runEnabledRule (b.runMaintenance x) (b.runOwner x) &&
    b.runWriterRule (b.runResidue x) (b.runOwner x) then b.runCounter x else 0
  recordNext : b.runRecord (b.runUpdate x a o) =
    if b.runEnabledRule (b.runMaintenanceUpdate (b.runMaintenance x) a o)
        (b.runOwnerUpdate (b.runOwner x) a o) &&
      b.runWriterRule (b.runResidueUpdate (b.runResidue x) a o)
        (b.runOwnerUpdate (b.runOwner x) a o)
    then b.runCounter x + 1 else 0


inductive RunReadoutField where
  | predictive | counter | ticks | tickPhase | progress | writer | record
  | residue | maintenance | owner | enabled | sourceFactor | targetFactor
  deriving DecidableEq, Repr

def RunReadoutValue (b : RawBridge H S T E R SC TC RR M) : RunReadoutField → Type
  | .predictive => b.RunPredictive
  | .counter | .ticks | .tickPhase | .progress | .record => Nat
  | .writer | .enabled => Bool
  | .residue => RR
  | .maintenance => M
  | .owner => CarrierId
  | .sourceFactor => Option S
  | .targetFactor => Option T

def runReadout (b : RawBridge H S T E R SC TC RR M)
    (f : RunReadoutField) (x : b.RunState) : RunReadoutValue b f :=
  match f with
  | .predictive => b.runPredictive x
  | .counter => b.runCounter x
  | .ticks => b.runTicks x
  | .tickPhase => b.runTicks x % b.runTickPeriod
  | .progress => b.runProgress x
  | .writer => b.runRecordWriter x
  | .record => b.runRecord x
  | .residue => b.runResidue x
  | .maintenance => b.runMaintenance x
  | .owner => b.runOwner x
  | .enabled => b.runEnabled x
  | .sourceFactor => b.runSourceFactor x
  | .targetFactor => b.runTargetFactor x

def expectedNextReadout (b : RawBridge H S T E R SC TC RR M)
    (f : RunReadoutField) (x : b.RunState) (a : b.RunAction) (o : b.RunOutcome) :
    RunReadoutValue b f :=
  match f with
  | .predictive => b.runPredictiveUpdate x a o
  | .counter => b.runCounter x + 1
  | .ticks => b.runTicks x + b.runTickAdvance x a o
  | .tickPhase => (b.runTicks x + b.runTickAdvance x a o) % b.runTickPeriod
  | .progress => b.runProgress x + b.runProgressAdvance x a o
  | .writer => b.runWriterRule (b.runResidueUpdate (b.runResidue x) a o)
      (b.runOwnerUpdate (b.runOwner x) a o)
  | .record => if b.runEnabledRule (b.runMaintenanceUpdate (b.runMaintenance x) a o)
      (b.runOwnerUpdate (b.runOwner x) a o) &&
      b.runWriterRule (b.runResidueUpdate (b.runResidue x) a o)
        (b.runOwnerUpdate (b.runOwner x) a o) then b.runCounter x + 1 else (0 : Nat)
  | .residue => b.runResidueUpdate (b.runResidue x) a o
  | .maintenance => b.runMaintenanceUpdate (b.runMaintenance x) a o
  | .owner => b.runOwnerUpdate (b.runOwner x) a o
  | .enabled => b.runEnabledRule (b.runMaintenanceUpdate (b.runMaintenance x) a o)
      (b.runOwnerUpdate (b.runOwner x) a o)
  | .sourceFactor => b.runSourceFactorUpdate x a o
  | .targetFactor => b.runTargetFactorUpdate x a o

theorem bridge_readout_update_field (b : RawBridge H S T E R SC TC RR M)
    (f : RunReadoutField) (x : b.RunState) (a : b.RunAction) (o : b.RunOutcome)
    (h : BridgeReadoutUpdateAt b x a o) :
    runReadout b f (b.runUpdate x a o) = expectedNextReadout b f x a o := by
  cases f with
  | predictive => exact h.predictive
  | counter => exact h.counter
  | ticks => exact h.ticks
  | tickPhase => exact congrArg (· % b.runTickPeriod) h.ticks
  | progress => exact h.progress
  | writer => exact h.writerNext
  | record => exact h.recordNext
  | residue => exact h.residue
  | maintenance => exact h.maintenance
  | owner => exact h.owner
  | enabled => exact h.enabledNext
  | sourceFactor => exact h.sourceFactor
  | targetFactor => exact h.targetFactor

/-- A proposed raw run extension must agree with the fixed bridge throughout
its own computed closure. Changing both proposal and candidate cannot change
this independent reference. -/
def BridgeDynamicsCheck (b : RawBridge H S T E R SC TC RR M)
    (raw : RawFutureDynamics b.RunState b.RunAction b.RunOutcome)
    (roots : List b.RunState) : Prop :=
  raw.outcomes = b.runOutcomes ∧ ∀ x,
    FutureClosure (bridgeRunDynamics b) roots x → ∀ a o,
      raw.actionRow x a o = (bridgeRunDynamics b).actionRow x a o ∧
      raw.update x a o = b.runUpdate x a o

theorem bridge_dynamics_check_self (b : RawBridge H S T E R SC TC RR M)
    (roots : List b.RunState) : BridgeDynamicsCheck b (bridgeRunDynamics b) roots :=
  ⟨rfl, fun _ _ _ _ => ⟨rfl, rfl⟩⟩

theorem bridge_dynamics_weight_mismatch (b : RawBridge H S T E R SC TC RR M)
    (raw : RawFutureDynamics b.RunState b.RunAction b.RunOutcome)
    (roots : List b.RunState) (x : b.RunState)
    (hx : FutureClosure (bridgeRunDynamics b) roots x)
    (a : b.RunAction) (o : b.RunOutcome)
    (hne : raw.actionRow x a o ≠ (bridgeRunDynamics b).actionRow x a o) :
    ¬ BridgeDynamicsCheck b raw roots := fun h => hne (h.2 x hx a o).1

theorem bridge_dynamics_successor_mismatch (b : RawBridge H S T E R SC TC RR M)
    (raw : RawFutureDynamics b.RunState b.RunAction b.RunOutcome)
    (roots : List b.RunState) (x : b.RunState)
    (hx : FutureClosure (bridgeRunDynamics b) roots x)
    (a : b.RunAction) (o : b.RunOutcome)
    (hne : raw.update x a o ≠ b.runUpdate x a o) :
    ¬ BridgeDynamicsCheck b raw roots := fun h => hne (h.2 x hx a o).2

theorem bridge_closure_in_proposed_dynamics (b : RawBridge H S T E R SC TC RR M)
    (raw : RawFutureDynamics b.RunState b.RunAction b.RunOutcome)
    (roots : List b.RunState) (h : BridgeDynamicsCheck b raw roots)
    (x : b.RunState) (hx : FutureClosure (bridgeRunDynamics b) roots x) :
    FutureClosure raw roots x := by
  induction hx with
  | root x hm => exact FutureClosure.root x hm
  | step hx a o ho ih =>
      have hu := (h.2 _ hx a o).2
      change FutureClosure raw roots (b.runUpdate _ a o)
      rw [← hu]
      exact FutureClosure.step ih a o (by simpa [h.1, bridgeRunDynamics] using ho)

theorem bridge_candidate_dynamics_check
    (b : RawBridge H S T E R SC TC RR M)
    (model : FullFutureModel b.RunState b.RunAction b.RunOutcome C V)
    (raw : RawFutureDynamics b.RunState b.RunAction b.RunOutcome)
    (roots : List b.RunState) (hr : BridgeDynamicsCheck b raw roots)
    (hm : FutureDynamicsCheck model raw roots) :
    FutureDynamicsCheck model (bridgeRunDynamics b) roots := by
  refine ⟨hm.1.trans hr.1, ?_⟩
  intro x hx a o
  have he := hm.2 x (bridge_closure_in_proposed_dynamics b raw roots hr x hx) a o
  have hr' := hr.2 x hx a o
  exact ⟨he.1.trans hr'.1, he.2.trans hr'.2⟩

def Reachable (b : RawBridge H S T E R SC TC RR M) (h : H) : Prop :=
  h ∈ b.frontier

def SourceHistoryClass (b : RawBridge H S T E R SC TC RR M)
    (h : H) : Option SC :=
  (b.sourceHistory h).getLast?.map b.sourceClass

def TargetHistoryClass (b : RawBridge H S T E R SC TC RR M)
    (h : H) : Option TC :=
  (b.targetHistory h).getLast?.map b.targetClass

/-- Action-word numerator for an M-class observation. The two transition
tables and finite enumerations, rather than supplied future values, determine
the entire function. Any mass leaving the enumeration is outside this probe. -/
def sourceWord (b : RawBridge H S T E R SC TC RR M) (s : S) :
    List Nat → S → Nat
  | [], destination =>
      letI := b.sourceClassDecEq
      if b.sourceClass s = b.sourceClass destination then 1 else 0
  | a :: rest, destination =>
      (b.sourceStates.map fun u =>
        b.sourceActionStep s a u * sourceWord b u rest destination).sum

def targetWord (b : RawBridge H S T E R SC TC RR M) (t : T) :
    List Nat → T → Nat
  | [], destination =>
      letI := b.targetClassDecEq
      if b.targetClass t = b.targetClass destination then 1 else 0
  | a :: rest, destination =>
      (b.targetStates.map fun u =>
        b.targetActionStep t a u * targetWord b u rest destination).sum

def sourceFuture (b : RawBridge H S T E R SC TC RR M) (s : S) :
    List Nat → Nat
  | [] => 0
  | destination :: word =>
      match b.sourceStates[destination]? with
      | none => 0
      | some d => sourceWord b s word d

def targetFuture (b : RawBridge H S T E R SC TC RR M) (t : T) :
    List Nat → Nat
  | [] => 0
  | destination :: word =>
      match b.targetStates[destination]? with
      | none => 0
      | some d => targetWord b t word d

/-- Future sufficiency is a predicate of the raw class code and all finite
future queries, rather than a stored proposition in `PredictiveNow`. -/
def SourceFutureSufficient (b : RawBridge H S T E R SC TC RR M) : Prop :=
  ∀ s t, b.sourceClass s = b.sourceClass t →
    ∀ w, sourceFuture b s w = sourceFuture b t w

def TargetFutureSufficientOnImage
    (b : RawBridge H S T E R SC TC RR M) : Prop :=
  ∀ s t, b.targetClass (b.mapState s) = b.targetClass (b.mapState t) →
    ∀ w, targetFuture b (b.mapState s) w =
      targetFuture b (b.mapState t) w

/-- Coverage and one actual strict reachable source edge, all computed from
finite path and transition data. -/
def BridgeAdmissible (b : RawBridge H S T E R SC TC RR M) : Prop :=
  b.frontier ≠ [] ∧
  (∀ h ∈ b.frontier, (b.sourceHistory h).length ≥ 2 ∧
    b.targetHistory h = (b.sourceHistory h).map b.mapState) ∧
  (∃ h ∈ b.frontier, ∃ x y,
    (x,y) ∈ (b.sourceHistory h).zip ((b.sourceHistory h).drop 1) ∧
    x ≠ y ∧ 0 < b.sourceStep x y) ∧
  (∀ h ∈ b.frontier, ∀ x y,
    (x,y) ∈ (b.sourceHistory h).zip ((b.sourceHistory h).drop 1) →
      0 < b.sourceStep x y) ∧
  b.sourceStates ≠ [] ∧
  (∀ h ∈ b.frontier, ∀ s ∈ b.sourceHistory h, s ∈ b.sourceStates)

/-- These are local raw map/table equations, not named conclusion fields. -/
def BridgeCoreLaws (b : RawBridge H S T E R SC TC RR M) : Prop :=
  (∀ s, b.targetCoord (b.mapState s) = b.mapCoord (b.sourceCoord s) ∧
    b.targetClass (b.mapState s) = b.mapClass (b.sourceClass s) ∧
    b.targetTick (b.mapState s) = b.sourceTick s ∧
    b.targetMaintenance (b.mapState s) =
      b.mapMaintenance (b.sourceMaintenance s) ∧
    b.targetOwner (b.mapState s) = b.targetId) ∧
  (∀ s t, b.sourceStep s t > 0 →
    b.targetStep (b.mapState s) (b.mapState t) = b.sourceStep s t) ∧
  (∀ h ∈ b.frontier,
    b.targetOrder h = b.sourceOrder h ∧
    b.targetProgress h = b.sourceProgress h) ∧
  RecordMapStepLaw b.record ∧ PositiveRecordIncrement b.record ∧
  (∀ r ∈ b.routeIds,
    b.targetRoute r = (b.sourceRoute r).map b.record.mapEvent ∧
    b.targetResidue r = b.sourceResidue r ∧
    b.targetReadout r = b.sourceReadout r)

/-- A bisimulation equation on raw action rows. It says nothing about future
answers directly; all finite-word consequences follow by recursion. -/
def SourceActionBisim (b : RawBridge H S T E R SC TC RR M) : Prop :=
  ∀ s t, b.sourceClass s = b.sourceClass t →
    ∀ a u, u ∈ b.sourceStates →
      b.sourceActionStep s a u = b.sourceActionStep t a u

def FutureMapLaws (b : RawBridge H S T E R SC TC RR M) : Prop :=
  b.targetStates = b.sourceStates.map b.mapState ∧
  ∀ s u a, b.targetActionStep (b.mapState s) a (b.mapState u) =
    b.sourceActionStep s a u

theorem source_future_sufficient_of_bisim
    (b : RawBridge H S T E R SC TC RR M) (hb : SourceActionBisim b) :
    SourceFutureSufficient b := by
  intro s t hclass query
  cases query with
  | nil => rfl
  | cons destination word =>
      simp only [sourceFuture]
      cases hd : b.sourceStates[destination]? with
      | none => simp
      | some d =>
          have wordEq (w : List Nat) : ∀ s t d,
              b.sourceClass s = b.sourceClass t →
              sourceWord b s w d = sourceWord b t w d := by
            induction w with
            | nil =>
                intro s t d hs
                simp only [sourceWord]
                rw [← hs]
            | cons a rest ih =>
                intro s t d hs
                simp only [sourceWord]
                congr 1
                apply List.map_congr_left
                intro u hu
                rw [hb s t hs a u hu]
          simpa [hd] using wordEq word s t d hclass

theorem future_transport_of_raw
    (b : RawBridge H S T E R SC TC RR M)
    (hc : BridgeCoreLaws b) (hf : FutureMapLaws b)
    (hinj : Function.Injective b.mapClass) :
    ∀ s query, targetFuture b (b.mapState s) query = sourceFuture b s query := by
  have wordEq (w : List Nat) : ∀ s d,
      targetWord b (b.mapState s) w (b.mapState d) =
        sourceWord b s w d := by
    induction w with
    | nil =>
        intro s d
        have hs := (hc.1 s).2.1
        have hd := (hc.1 d).2.1
        have heq : (b.targetClass (b.mapState s) =
            b.targetClass (b.mapState d)) ↔
            b.sourceClass s = b.sourceClass d := by
          rw [hs, hd]
          exact ⟨fun h => hinj h, congrArg b.mapClass⟩
        simp only [sourceWord, targetWord]
        by_cases hsource : b.sourceClass s = b.sourceClass d
        · simp [hsource, heq.mpr hsource]
        · have htarget : ¬ b.targetClass (b.mapState s) =
              b.targetClass (b.mapState d) := fun h => hsource (heq.mp h)
          simp [hsource, htarget]
    | cons a rest ih =>
        intro s d
        simp only [sourceWord, targetWord, hf.1, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u _
        simp only [Function.comp_apply]
        rw [hf.2 s u a, ih u d]
  intro s query
  cases query with
  | nil => rfl
  | cons destination word =>
      simp only [sourceFuture, targetFuture, hf.1, List.getElem?_map]
      cases h : b.sourceStates[destination]? with
      | none => simp
      | some d => simpa [h] using wordEq word s d

/-- Source increments are checked on raw numbered history edges. The target
equations commute with those readouts; target strictness is not a field. -/
def BridgeStrictStepLaws (b : RawBridge H S T E R SC TC RR M) : Prop :=
  ∀ h ∈ b.frontier, ∀ i, i + 1 < (b.sourceHistory h).length →
    (b.sourceOrder h).getD (i + 1) 0 =
      (b.sourceOrder h).getD i 0 + 1 ∧
    b.sourceProgressAt h (i + 1) = b.sourceProgressAt h i + 1 ∧
    b.targetProgressAt h i = b.sourceProgressAt h i ∧
    b.targetProgressAt h (i + 1) = b.sourceProgressAt h (i + 1) ∧
    ∃ x, (b.sourceHistory h)[i]? = some x ∧ 0 < b.sourceTick x

/-- The separate order, tick, and progress inequalities are consequences of
the raw increment laws and the ordinary bridge equations. -/
def StrictOrderTickProgressAt
    (b : RawBridge H S T E R SC TC RR M) (h : H) : Prop :=
  ∀ i, i + 1 < (b.sourceHistory h).length →
    (b.targetOrder h).getD i 0 < (b.targetOrder h).getD (i + 1) 0 ∧
    b.targetProgressAt h i < b.targetProgressAt h (i + 1) ∧
    ∃ x, (b.sourceHistory h)[i]? = some x ∧
      0 < b.targetTick (b.mapState x)

theorem strict_order_tick_progress_of_raw
    (b : RawBridge H S T E R SC TC RR M)
    (hc : BridgeCoreLaws b) (hs : BridgeStrictStepLaws b)
    (h : H) (hh : Reachable b h) : StrictOrderTickProgressAt b h := by
  intro i hi
  obtain ⟨ho, hp, hpi, hpnext, x, hx, htick⟩ := hs h hh i hi
  have horder := (hc.2.2.1 h hh).1
  have htickMap := (hc.1 x).2.2.1
  rw [horder]
  exact ⟨by omega, by omega, x, hx, by simpa [htickMap] using htick⟩

/-- The reachable-history M-class probe and selected raw signature readouts.
Record-arrow and executed route status are separate conclusions below. This
is not yet a projection to every field of `CSTTT.TemporalSignature`: its full
C6 future observation and finite component alphabets require another bridge. -/
def TemporalSignatureAgreementAt
    (b : RawBridge H S T E R SC TC RR M) (h : H) : Prop :=
  TargetHistoryClass b h = (SourceHistoryClass b h).map b.mapClass ∧
  b.targetOrder h = b.sourceOrder h ∧
  b.targetProgress h = b.sourceProgress h ∧
  (∀ s ∈ b.sourceHistory h,
    b.targetCoord (b.mapState s) = b.mapCoord (b.sourceCoord s) ∧
    b.targetTick (b.mapState s) = b.sourceTick s ∧
    b.targetMaintenance (b.mapState s) =
      b.mapMaintenance (b.sourceMaintenance s) ∧
    b.targetOwner (b.mapState s) = b.targetId ∧
    ∀ w, targetFuture b (b.mapState s) w = sourceFuture b s w)

def StrictSuccessorPreserved
    (b : RawBridge H S T E R SC TC RR M) (h : H) : Prop :=
  ∀ x y, (x,y) ∈ (b.sourceHistory h).zip ((b.sourceHistory h).drop 1) →
    b.sourceStep x y > 0 → b.targetStep (b.mapState x) (b.mapState y) > 0

def StrictRecordArrowPreserved
    (b : RawBridge H S T E R SC TC RR M) : Prop :=
  ∀ a c, SourceArrow b.record a c →
    TargetArrow b.record (b.record.mapEvent a) (b.record.mapEvent c)

/-- A pair enters comparison only after both raw route paths are supported,
both histories reach one target endpoint, and the funded result-state register
and readout are actually present and consistent. -/
def RoutePairDomain (b : RawBridge H S T E R SC TC RR M) (r s : R) : Prop :=
  r ∈ b.routeIds ∧ s ∈ b.routeIds ∧ r ≠ s ∧
  b.targetRoute r ≠ [] ∧ b.targetRoute s ≠ [] ∧
  (∀ pair ∈ (b.targetRoute r).zip ((b.targetRoute r).drop 1),
    pair ∈ b.record.targetEdges) ∧
  (∀ pair ∈ (b.targetRoute s).zip ((b.targetRoute s).drop 1),
    pair ∈ b.record.targetEdges) ∧
  (∃ endpoint, (b.targetHistory (b.routeHistory r)).getLast? = some endpoint ∧
    (b.targetHistory (b.routeHistory s)).getLast? = some endpoint) ∧
  b.targetRouteSteps r ≠ [] ∧ b.targetRouteSteps s ≠ [] ∧
  (∀ entry ∈ b.targetRouteSteps r,
    entry.1 = b.targetResidue r ∧ some entry.2 = b.targetReadout r) ∧
  (∀ entry ∈ b.targetRouteSteps s,
    entry.1 = b.targetResidue s ∧ some entry.2 = b.targetReadout s)

def RouteComparisonNonempty (b : RawBridge H S T E R SC TC RR M) : Prop :=
  ∃ r s, RoutePairDomain b r s

def RouteIndexed (b : RawBridge H S T E R SC TC RR M) : Prop :=
  ∃ r s, RoutePairDomain b r s ∧
    b.targetResidue r ≠ b.targetResidue s ∧
    b.targetReadout r ≠ b.targetReadout s

/-- Without a flatness certificate, the only computed statuses are indexed
and unresolved. In particular an empty comparison domain never yields flat. -/
noncomputable def routeStatusOfRaw
    (b : RawBridge H S T E R SC TC RR M) : CSTTT.RouteStatus := by
  classical
  exact if RouteIndexed b then .routeIndexed else .unresolved

def RouteStatusPreserved (b : RawBridge H S T E R SC TC RR M) : Prop :=
  RouteComparisonNonempty b ∧
  ∀ r s, RoutePairDomain b r s →
    b.sourceResidue r ≠ b.sourceResidue s →
    b.sourceReadout r ≠ b.sourceReadout s →
    routeStatusOfRaw b = .routeIndexed

/-- Every premise is raw table data or an independently checked equation.
The comparison domain is nonempty before route status can be certified. -/
def BridgePrimitiveLaws (b : RawBridge H S T E R SC TC RR M) : Prop :=
  BridgeCoreLaws b ∧ SourceActionBisim b ∧ FutureMapLaws b ∧
    Function.Injective b.mapClass ∧ BridgeStrictStepLaws b ∧
    RouteComparisonNonempty b

/-- The predictive class factors through the raw state map. Equal source
classes therefore have equal target images without a representative field. -/
theorem representativeIndependent_of_raw
    (b : RawBridge H S T E R SC TC RR M)
    (ha : BridgeAdmissible b) (hl : BridgePrimitiveLaws b) :
    RepresentativeIndependent (Reachable b)
      (SourceHistoryClass b) (TargetHistoryClass b) := by
  intro x y hx hy hclass
  have hc : BridgeCoreLaws b := hl.1
  have mapped (h : H) (hh : Reachable b h) :
      TargetHistoryClass b h = (SourceHistoryClass b h).map b.mapClass := by
    have hp := (ha.2.1 h hh).2
    simp [TargetHistoryClass, SourceHistoryClass, hp, List.getLast?_map]
    congr 1
    funext s
    exact (hc.1 s).2.1
  rw [mapped x hx, mapped y hy, hclass]

/-- Candidate TTH-03 raw-history theorem. It derives all-word M-class probe
sufficiency, strict order/tick/progress steps, record-arrow transport, and
nonempty executed-route comparison. The full frozen signature projection is
still open, so this theorem alone does not promote TTH-03. -/
theorem bundledHeterogeneousTemporalTransport_generic
    (b : RawBridge H S T E R SC TC RR M)
    (ha : BridgeAdmissible b) (hl : BridgePrimitiveLaws b) :
    RepresentativeIndependent (Reachable b)
      (SourceHistoryClass b) (TargetHistoryClass b) ∧
    (∀ h, Reachable b h →
      TemporalSignatureAgreementAt b h ∧ StrictSuccessorPreserved b h) ∧
    StrictRecordArrowPreserved b ∧ RouteStatusPreserved b ∧
    TargetFutureSufficientOnImage b ∧
    (∀ h, Reachable b h → StrictOrderTickProgressAt b h) := by
  have hc : BridgeCoreLaws b := hl.1
  have hfuture := future_transport_of_raw b hc hl.2.2.1 hl.2.2.2.1
  refine ⟨representativeIndependent_of_raw b ha hl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    have hp := (ha.2.1 h hh).2
    have hclass : TargetHistoryClass b h =
        (SourceHistoryClass b h).map b.mapClass := by
      simp [TargetHistoryClass, SourceHistoryClass, hp, List.getLast?_map]
      congr 1
      funext s
      exact (hc.1 s).2.1
    refine ⟨⟨hclass, (hc.2.2.1 h hh).1,
      (hc.2.2.1 h hh).2, ?_⟩, ?_⟩
    · intro s _
      have hs := hc.1 s
      exact ⟨hs.1, hs.2.2.1, hs.2.2.2.1,
        hs.2.2.2.2, hfuture s⟩
    · intro x y _ hstep
      rw [(hc.2.1 x y hstep)]
      exact hstep
  · exact CSTTT.RecordTheory.monotoneRecordDescentTransportsArrow_generic
      b.record hc.2.2.2.1 hc.2.2.2.2.1
  · refine ⟨hl.2.2.2.2.2, ?_⟩
    intro r s hdomain hres hread
    have hr := hc.2.2.2.2.2 r hdomain.1
    have hs := hc.2.2.2.2.2 s hdomain.2.1
    have hresTarget : b.targetResidue r ≠ b.targetResidue s := by
      rw [hr.2.1, hs.2.1]
      exact hres
    have hreadTarget : b.targetReadout r ≠ b.targetReadout s := by
      rw [hr.2.2, hs.2.2]
      exact hread
    have hi : RouteIndexed b := ⟨r, s, hdomain, hresTarget, hreadTarget⟩
    simp [routeStatusOfRaw, hi]
  · intro s t hclass w
    have hs := hc.1 s
    have ht := hc.1 t
    have hsource : b.sourceClass s = b.sourceClass t :=
      hl.2.2.2.1 (by simpa [hs.2.1, ht.2.1] using hclass)
    rw [hfuture s w, hfuture t w]
    exact source_future_sufficient_of_bisim b hl.2.1 s t hsource w
  · intro h hh
    exact strict_order_tick_progress_of_raw b hc hl.2.2.2.2.1 h hh

end CSTTT.TransportTheory
