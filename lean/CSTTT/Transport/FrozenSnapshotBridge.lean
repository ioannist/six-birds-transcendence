import CSTTT.Transport.RawBridge
import CSTTT.Transport.SnapshotImages

/-! G1c: the frozen TemporalSignature is constructed on an exact finite image
of audited bridge snapshots. The bridge's history/event counters remain Nat
at run level. Tick phase is accumulated raw history ticks modulo the declared
clock period, not the one-step increment itself. The additional hypotheses
are raw snapshot coverage and full-observation equations, not stored verdicts.
All conclusions are scoped to the declared audited frontier; the future test
itself quantifies over all finite words, without a frontier or horizon bound. -/
namespace CSTTT.TransportTheory

open CSTTT.RecordTheory

structure BridgeSnapshot (H S E R : Type) where
  history : H
  state : S
  occurrence : Nat
  event : E
  route : R

structure BridgeSnapshotAudit (I H S E R : Type) where
  frontier : List I
  snapshot : I → BridgeSnapshot H S E R
  tickPeriod : Nat

variable {I H S T E R SC TC RR M : Type}

/-- Each displayed snapshot is an actual covered history occurrence and a
listed route event. Every reachable history's terminal occurrence is displayed.
Positive occurrences allow the strict per-edge laws to supply progress. -/
def SnapshotAuditCheck (b : RawBridge H S T E R SC TC RR M)
    (d : BridgeSnapshotAudit I H S E R) : Prop :=
  d.frontier ≠ [] ∧ 0 < d.tickPeriod ∧
  (∀ i ∈ d.frontier,
    let x := d.snapshot i
    x.history ∈ b.frontier ∧ x.route ∈ b.routeIds ∧
    0 < x.occurrence ∧ x.occurrence < (b.sourceHistory x.history).length ∧
    (b.sourceHistory x.history)[x.occurrence]? = some x.state ∧
    x.event ∈ b.sourceRoute x.route ∧ x.history = b.routeHistory x.route ∧
    (∃ a c, (a, c) ∈ b.record.sourceEdges ∧ (x.event = a ∨ x.event = c))) ∧
  (∀ h ∈ b.frontier, ∃ i ∈ d.frontier,
    (d.snapshot i).history = h ∧
    (d.snapshot i).occurrence + 1 = (b.sourceHistory h).length)

def sourceSnapshotTicks (b : RawBridge H S T E R SC TC RR M)
    (x : BridgeSnapshot H S E R) : Nat :=
  ((b.sourceHistory x.history).take x.occurrence |>.map b.sourceTick).sum

def targetSnapshotTicks (b : RawBridge H S T E R SC TC RR M)
    (x : BridgeSnapshot H S E R) : Nat :=
  ((b.targetHistory x.history).take x.occurrence |>.map b.targetTick).sum

def sourceSnapshotReadout (b : RawBridge H S T E R SC TC RR M)
    (d : BridgeSnapshotAudit I H S E R) (i : I) : TemporalSnapshotReadout SC RR M :=
  let x := d.snapshot i
  ⟨b.sourceClass x.state, (b.sourceOrder x.history).getD x.occurrence 0,
    sourceSnapshotTicks b x % d.tickPeriod, b.sourceProgressAt x.history x.occurrence,
    b.record.sourceRecord x.event, b.sourceResidue x.route,
    b.sourceMaintenance x.state, b.sourceOwner x.state⟩

def targetSnapshotReadout (b : RawBridge H S T E R SC TC RR M)
    (d : BridgeSnapshotAudit I H S E R) (i : I) : TemporalSnapshotReadout TC RR M :=
  let x := d.snapshot i
  ⟨b.targetClass (b.mapState x.state), (b.targetOrder x.history).getD x.occurrence 0,
    targetSnapshotTicks b x % d.tickPeriod, b.targetProgressAt x.history x.occurrence,
    b.record.targetRecord (b.record.mapEvent x.event), b.targetResidue x.route,
    b.targetMaintenance (b.mapState x.state), b.targetOwner (b.mapState x.state)⟩

def bridgeSnapshotMaps (b : RawBridge H S T E R SC TC RR M) :
    SnapshotRawMaps SC TC RR M where
  predictive := b.mapClass
  order := id
  tickPhase := id
  progress := id
  record := b.record.translate
  residue := id
  maintenance := b.mapMaintenance
  owner := fun _ => b.targetId

theorem snapshot_ticks_transport (b : RawBridge H S T E R SC TC RR M)
    (ha : BridgeAdmissible b) (hc : BridgeCoreLaws b)
    (x : BridgeSnapshot H S E R) (hh : x.history ∈ b.frontier) :
    targetSnapshotTicks b x = sourceSnapshotTicks b x := by
  unfold targetSnapshotTicks sourceSnapshotTicks
  rw [(ha.2.1 x.history hh).2, ← List.map_take, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s _
  exact (hc.1 s).2.2.1

theorem bridge_snapshot_map_check (b : RawBridge H S T E R SC TC RR M)
    (d : BridgeSnapshotAudit I H S E R) (ha : BridgeAdmissible b)
    (hl : BridgePrimitiveLaws b) (hd : SnapshotAuditCheck b d) :
    SnapshotMapCheck d.frontier (sourceSnapshotReadout b d)
      (targetSnapshotReadout b d) (bridgeSnapshotMaps b) := by
  intro i hi
  let x := d.snapshot i
  obtain ⟨hh, hr, hpositive, hlength, _, _, _, _⟩ := hd.2.2.1 i hi
  change 0 < x.occurrence at hpositive
  change x.occurrence < (b.sourceHistory x.history).length at hlength
  have hc : BridgeCoreLaws b := hl.1
  have hstate := hc.1 x.state
  have horder := (hc.2.2.1 x.history hh).1
  have hticks := snapshot_ticks_transport b ha hc x hh
  have hiEdge : x.occurrence - 1 + 1 < (b.sourceHistory x.history).length := by
    omega
  obtain ⟨_, _, _, hprogress, _, _, _⟩ :=
    hl.2.2.2.2.1 x.history hh (x.occurrence - 1) hiEdge
  have hprogress' : b.targetProgressAt x.history x.occurrence =
      b.sourceProgressAt x.history x.occurrence := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ x.occurrence)] using hprogress
  have hrecord := hc.2.2.2.1.2 x.event
  have hroute := (hc.2.2.2.2.2 x.route hr).2.1
  simp only [mapSnapshotReadout, bridgeSnapshotMaps, sourceSnapshotReadout,
    targetSnapshotReadout, id_eq, TemporalSnapshotReadout.mk.injEq]
  exact ⟨hstate.2.1.symm, congrArg (fun xs : List Nat => xs.getD x.occurrence 0)
    horder.symm, congrArg (· % d.tickPeriod) hticks.symm,
    hprogress'.symm, hrecord.symm, hroute.symm, hstate.2.2.2.1.symm,
    hstate.2.2.2.2.symm⟩

/-- The frozen clock's compatibility propositions are computed bridge tests;
they are not input flags. Their proofs are supplied by the raw G1 theorem. -/
def bridgeSnapshotClock (b : RawBridge H S T E R SC TC RR M)
    (d : BridgeSnapshotAudit I H S E R) (ha : BridgeAdmissible b)
    (hl : BridgePrimitiveLaws b) (hd : SnapshotAuditCheck b d) :
    ClockTranslation (snapshotAlphabet d.frontier (sourceSnapshotReadout b d))
      (snapshotAlphabet d.frontier (targetSnapshotReadout b d)) where
  mapPredictive := mapSnapshotImage d.frontier _ _ b.mapClass
    (fun i hi => congrArg TemporalSnapshotReadout.predictive
      (bridge_snapshot_map_check b d ha hl hd i hi))
  mapOrder := mapSnapshotImage d.frontier _ _ id
    (fun i hi => congrArg TemporalSnapshotReadout.order
      (bridge_snapshot_map_check b d ha hl hd i hi))
  mapTick := mapSnapshotImage d.frontier _ _ id
    (fun i hi => congrArg TemporalSnapshotReadout.tickPhase
      (bridge_snapshot_map_check b d ha hl hd i hi))
  mapProgress := mapSnapshotImage d.frontier _ _ id
    (fun i hi => congrArg TemporalSnapshotReadout.progress
      (bridge_snapshot_map_check b d ha hl hd i hi))
  mapRecord := mapSnapshotImage d.frontier _ _ b.record.translate
    (fun i hi => congrArg TemporalSnapshotReadout.record
      (bridge_snapshot_map_check b d ha hl hd i hi))
  mapRoute := mapSnapshotImage d.frontier _ _ id
    (fun i hi => congrArg TemporalSnapshotReadout.residue
      (bridge_snapshot_map_check b d ha hl hd i hi))
  mapMaintenance := mapSnapshotImage d.frontier _ _ b.mapMaintenance
    (fun i hi => congrArg TemporalSnapshotReadout.maintenance
      (bridge_snapshot_map_check b d ha hl hd i hi))
  successorCompatible := ∀ h, Reachable b h → StrictSuccessorPreserved b h
  progressCompatible := ∀ h, Reachable b h → StrictOrderTickProgressAt b h
  recordMonotone := StrictRecordArrowPreserved b

theorem bridge_snapshot_clock_laws (b : RawBridge H S T E R SC TC RR M)
    (d : BridgeSnapshotAudit I H S E R) (ha : BridgeAdmissible b)
    (hl : BridgePrimitiveLaws b) (hd : SnapshotAuditCheck b d) :
    (bridgeSnapshotClock b d ha hl hd).successorCompatible ∧
    (bridgeSnapshotClock b d ha hl hd).progressCompatible ∧
    (bridgeSnapshotClock b d ha hl hd).recordMonotone := by
  have ht := bundledHeterogeneousTemporalTransport_generic b ha hl
  exact ⟨fun h hh => (ht.2.1 h hh).2, ht.2.2.2.2.2, ht.2.2.1⟩

/-- Audit contexts are selected by raw bridge-owned selectors. -/
def bridgeSnapshotAudit (b : RawBridge H S T E R SC TC RR M) :
    BridgeSnapshotAudit b.AuditIndex H S E R where
  frontier := b.auditFrontier
  snapshot := fun i => ⟨b.auditHistory i, b.auditState i, b.auditOccurrence i,
    b.auditEvent i, b.auditRoute i⟩
  tickPeriod := b.runTickPeriod

def bridgeSourceRun (b : RawBridge H S T E R SC TC RR M) (i : b.AuditIndex) : b.RunState :=
  let x := (bridgeSnapshotAudit b).snapshot i
  b.makeSourceRun x.state x.occurrence (sourceSnapshotTicks b x)
    (b.sourceResidue x.route) (b.sourceMaintenance x.state)

def bridgeTargetRun (b : RawBridge H S T E R SC TC RR M) (i : b.AuditIndex) : b.RunState :=
  let x := (bridgeSnapshotAudit b).snapshot i
  b.makeTargetRun (b.mapState x.state) x.occurrence (targetSnapshotTicks b x)
    (b.targetResidue x.route) (b.targetMaintenance (b.mapState x.state))

def bridgeFutureRoots (b : RawBridge H S T E R SC TC RR M) : List b.RunState :=
  b.auditFrontier.map (bridgeSourceRun b) ++ b.auditFrontier.map (bridgeTargetRun b)

abbrev BridgeFutureClosure (b : RawBridge H S T E R SC TC RR M) :=
  FutureClosure (bridgeRunDynamics b) (bridgeFutureRoots b)

/-- Typed predictive maps are raw coordinate maps; the lift of all eight
fields is defined, not an independently supplied display. -/
def liftRunSnapshot {P Q R M : Type} (predictive : P → Q)
    (v : TemporalSnapshotReadout P R M) : TemporalSnapshotReadout Q R M :=
  ⟨predictive v.predictive, v.order, v.tickPhase, v.progress, v.record,
    v.residue, v.maintenance, v.owner⟩

/-- Raw equations bind the typed run constructors to the audit occurrences. -/
def SnapshotRunCheck (b : RawBridge H S T E R SC TC RR M) : Prop :=
  ∀ i ∈ b.auditFrontier,
    b.runSourceFactor (bridgeSourceRun b i) = some (b.auditState i) ∧
    b.runTargetFactor (bridgeTargetRun b i) = some (b.mapState (b.auditState i)) ∧
    b.runEnabled (bridgeSourceRun b i) = true ∧ b.runEnabled (bridgeTargetRun b i) = true ∧
    b.runCounter (bridgeSourceRun b i) = b.auditOccurrence i ∧
    b.runCounter (bridgeTargetRun b i) = b.auditOccurrence i ∧
    b.runTicks (bridgeSourceRun b i) = sourceSnapshotTicks b ((bridgeSnapshotAudit b).snapshot i) ∧
    b.runTicks (bridgeTargetRun b i) = targetSnapshotTicks b ((bridgeSnapshotAudit b).snapshot i)

/-- The only observation interface is the bridge-defined readout. Injective
predictive coordinate maps exclude loss of a frozen field in its typed lift. -/
def BridgeSnapshotReadoutCheck (b : RawBridge H S T E R SC TC RR M) : Prop :=
  (∀ p q, b.sourcePredictiveMap p = b.sourcePredictiveMap q → p = q) ∧
  (∀ p q, b.targetPredictiveMap p = b.targetPredictiveMap q → p = q) ∧
  ∀ i ∈ b.auditFrontier,
    bridgeRunObservation b (bridgeSourceRun b i) =
      liftRunSnapshot b.sourcePredictiveMap (sourceSnapshotReadout b (bridgeSnapshotAudit b) i) ∧
    bridgeRunObservation b (bridgeTargetRun b i) =
      liftRunSnapshot b.targetPredictiveMap (targetSnapshotReadout b (bridgeSnapshotAudit b) i)

/-- Root identity plus every component law throughout the bridge's computed
closure. The root checks prevent constant preserved labels from passing. -/
def BridgeRunReadoutLaws (b : RawBridge H S T E R SC TC RR M) : Prop :=
  SnapshotRunCheck b ∧ BridgeSnapshotReadoutCheck b ∧
    ∀ x, BridgeFutureClosure b x → ∀ a o, o ∈ b.runOutcomes →
      BridgeReadoutUpdateAt b x a o

/-- Parameterized sensitivity: any failed component equation at any closure
state rejects the complete readout gate. The component selector can be any
field of BridgeReadoutUpdateAt, including the record/availability equations. -/
theorem bridge_readout_step_guard (b : RawBridge H S T E R SC TC RR M)
    (x : b.RunState) (hx : BridgeFutureClosure b x) (a : b.RunAction) (o : b.RunOutcome)
    (ho : o ∈ b.runOutcomes) (hbad : ¬ BridgeReadoutUpdateAt b x a o) :
    ¬ BridgeRunReadoutLaws b := fun h => hbad (h.2.2 x hx a o ho)

theorem bridge_readout_root_guard (b : RawBridge H S T E R SC TC RR M)
    (hbad : ¬ BridgeSnapshotReadoutCheck b) : ¬ BridgeRunReadoutLaws b :=
  fun h => hbad h.2.1

/-- One generic guard, explicitly parameterized over EVERY run readout.
All per-field concrete guards below instantiate this or the root-value gate. -/
theorem bridge_readout_field_update_guard (b : RawBridge H S T E R SC TC RR M)
    (f : RunReadoutField) (x : b.RunState) (hx : BridgeFutureClosure b x)
    (a : b.RunAction) (o : b.RunOutcome) (ho : o ∈ b.runOutcomes)
    (hne : runReadout b f (b.runUpdate x a o) ≠ expectedNextReadout b f x a o) :
    ¬ BridgeRunReadoutLaws b := by
  apply bridge_readout_step_guard b x hx a o ho
  exact fun h => hne (bridge_readout_update_field b f x a o h)

def bridgeRootRun (b : RawBridge H S T E R SC TC RR M) (target : Bool)
    (i : b.AuditIndex) : b.RunState :=
  if target then bridgeTargetRun b i else bridgeSourceRun b i

def bridgeRootExpectedObservation (b : RawBridge H S T E R SC TC RR M)
    (target : Bool) (i : b.AuditIndex) : BridgeRunObservation b :=
  if target then liftRunSnapshot b.targetPredictiveMap
    (targetSnapshotReadout b (bridgeSnapshotAudit b) i)
  else liftRunSnapshot b.sourcePredictiveMap
    (sourceSnapshotReadout b (bridgeSnapshotAudit b) i)

/-- Parameterized root-value guard, including fixed-point-valued readouts
whose preservation equation alone cannot detect an incorrect constant. -/
theorem bridge_readout_initial_observation_guard
    (b : RawBridge H S T E R SC TC RR M) (target : Bool)
    (i : b.AuditIndex) (hi : i ∈ b.auditFrontier) {V : Type}
    (project : BridgeRunObservation b → V)
    (hne : project (bridgeRunObservation b (bridgeRootRun b target i)) ≠
      project (bridgeRootExpectedObservation b target i)) : ¬ BridgeRunReadoutLaws b := by
  intro h
  have he := h.2.1.2.2 i hi
  cases target with
  | false => exact hne (congrArg project he.1)
  | true => exact hne (congrArg project he.2)

def frozenBridgeSource (b : RawBridge H S T E R SC TC RR M)
    (i : Audited b.auditFrontier) :=
  letI := bridgeRunObservationDecEq b
  frozenSnapshot (bridgeFutureModel b) b.auditFrontier
    (sourceSnapshotReadout b (bridgeSnapshotAudit b)) i

def frozenBridgeTarget (b : RawBridge H S T E R SC TC RR M)
    (i : Audited b.auditFrontier) :=
  letI := bridgeRunObservationDecEq b
  frozenSnapshot (bridgeFutureModel b) b.auditFrontier
    (targetSnapshotReadout b (bridgeSnapshotAudit b)) i

/-- Construct the actual frozen structures, with the defined all-word test. -/
theorem bridge_constructs_frozen_signatures
    (b : RawBridge H S T E R SC TC RR M) (ha : BridgeAdmissible b)
    (hl : BridgePrimitiveLaws b) (hd : SnapshotAuditCheck b (bridgeSnapshotAudit b))
    (_hupdates : BridgeRunReadoutLaws b)
    (hb : BridgeFutureBisim b) (i : Audited b.auditFrontier) :
    TemporalSignatureAgreement (bridgeSnapshotClock b (bridgeSnapshotAudit b) ha hl hd) b.targetId
      (frozenBridgeSource b i) (frozenBridgeTarget b i) ∧
    transportFrozenSnapshot b.auditFrontier (sourceSnapshotReadout b (bridgeSnapshotAudit b))
      (targetSnapshotReadout b (bridgeSnapshotAudit b)) (bridgeSnapshotMaps b)
      (bridge_snapshot_map_check b (bridgeSnapshotAudit b) ha hl hd)
      (frozenBridgeSource b i) = frozenBridgeTarget b i ∧
    (frozenBridgeSource b i).predictiveNow.futureSufficient ∧
    (frozenBridgeTarget b i).predictiveNow.futureSufficient := by
  letI := bridgeRunObservationDecEq b
  refine ⟨?_, frozen_snapshot_transport (bridgeFutureModel b) b.auditFrontier _ _ _ _ i,
    bridge_defined_future_sufficient b hb, bridge_defined_future_sufficient b hb⟩
  constructor
  · simp only [bridgeSnapshotClock, frozenBridgeSource, frozenBridgeTarget, frozenSnapshot]
    apply snapshot_map_encode
  · simp only [bridgeSnapshotClock, frozenBridgeSource, frozenBridgeTarget, frozenSnapshot]
    apply snapshot_map_encode
  · rfl
  · simp only [bridgeSnapshotClock, frozenBridgeSource, frozenBridgeTarget, frozenSnapshot]
    apply snapshot_map_encode
  · simp only [bridgeSnapshotClock, frozenBridgeSource, frozenBridgeTarget, frozenSnapshot]
    apply snapshot_map_encode
  · simp only [bridgeSnapshotClock, frozenBridgeSource, frozenBridgeTarget, frozenSnapshot]
    apply snapshot_map_encode
  · simp only [bridgeSnapshotClock, frozenBridgeSource, frozenBridgeTarget, frozenSnapshot]
    apply snapshot_map_encode
  · simp only [bridgeSnapshotClock, frozenBridgeSource, frozenBridgeTarget, frozenSnapshot]
    apply snapshot_map_encode
  · exact (hl.1.1 (b.auditState i.val)).2.2.2.2

/-- Certified result with NO supplied model, raw proposal, snapshot data,
run embedding, code, display, decoder or clock. All these are defined from b. -/
structure FrozenBridgeSnapshotResult
    (b : RawBridge H S T E R SC TC RR M) (ha : BridgeAdmissible b)
    (hl : BridgePrimitiveLaws b) (hd : SnapshotAuditCheck b (bridgeSnapshotAudit b))
    (i : Audited b.auditFrontier) : Prop where
  runEmbedding : SnapshotRunCheck b
  coherence : BridgeRunCoherence b
  readoutLaws : BridgeRunReadoutLaws b
  readoutCoherence : BridgeSnapshotReadoutCheck b
  actualFuture : ∀ x y, BridgeFutureClosure b x → BridgeFutureClosure b y →
    bridgeRunCode b x = bridgeRunCode b y → ∀ word trace,
    bridgeFuture b x word trace = bridgeFuture b y word trace
  agreement : TemporalSignatureAgreement (bridgeSnapshotClock b (bridgeSnapshotAudit b) ha hl hd)
    b.targetId (frozenBridgeSource b i) (frozenBridgeTarget b i)
  typedImage : transportFrozenSnapshot b.auditFrontier
    (sourceSnapshotReadout b (bridgeSnapshotAudit b))
    (targetSnapshotReadout b (bridgeSnapshotAudit b)) (bridgeSnapshotMaps b)
    (bridge_snapshot_map_check b (bridgeSnapshotAudit b) ha hl hd)
    (frozenBridgeSource b i) = frozenBridgeTarget b i
  sourceCodec : decodeFrozenSnapshot b.auditFrontier
    (sourceSnapshotReadout b (bridgeSnapshotAudit b)) (frozenBridgeSource b i) =
    sourceSnapshotReadout b (bridgeSnapshotAudit b) i.val
  targetCodec : decodeFrozenSnapshot b.auditFrontier
    (targetSnapshotReadout b (bridgeSnapshotAudit b)) (frozenBridgeTarget b i) =
    targetSnapshotReadout b (bridgeSnapshotAudit b) i.val
  sourceObservation : bridgeRunObservation b (bridgeSourceRun b i.val) =
    liftRunSnapshot b.sourcePredictiveMap (sourceSnapshotReadout b (bridgeSnapshotAudit b) i.val)
  targetObservation : bridgeRunObservation b (bridgeTargetRun b i.val) =
    liftRunSnapshot b.targetPredictiveMap (targetSnapshotReadout b (bridgeSnapshotAudit b) i.val)
  sourceFutureCode : bridgeRunCode b (bridgeSourceRun b i.val) =
    bridgeCodeOfObservation (liftRunSnapshot b.sourcePredictiveMap
      (sourceSnapshotReadout b (bridgeSnapshotAudit b) i.val))
  targetFutureCode : bridgeRunCode b (bridgeTargetRun b i.val) =
    bridgeCodeOfObservation (liftRunSnapshot b.targetPredictiveMap
      (targetSnapshotReadout b (bridgeSnapshotAudit b) i.val))
  sourceFullFuture : (frozenBridgeSource b i).predictiveNow.futureSufficient
  targetFullFuture : (frozenBridgeTarget b i).predictiveNow.futureSufficient

/-- The main generic certificate construction. Every input other than b and
an audited index is a proof of equations/checks on defined functions. -/
theorem bundledHeterogeneousTemporalTransport_frozen
    (b : RawBridge H S T E R SC TC RR M) (ha : BridgeAdmissible b)
    (hl : BridgePrimitiveLaws b) (hd : SnapshotAuditCheck b (bridgeSnapshotAudit b))
    (hbc : BridgeRunCoherence b) (hrun : SnapshotRunCheck b)
    (hread : BridgeSnapshotReadoutCheck b) (hupdates : BridgeRunReadoutLaws b)
    (hb : BridgeFutureBisim b) :
    RepresentativeIndependent (Reachable b) (SourceHistoryClass b) (TargetHistoryClass b) ∧
    StrictRecordArrowPreserved b ∧ RouteStatusPreserved b ∧
    (∀ h, Reachable b h → StrictSuccessorPreserved b h ∧ StrictOrderTickProgressAt b h) ∧
    (∀ i : Audited b.auditFrontier, FrozenBridgeSnapshotResult b ha hl hd i) := by
  have hg := bundledHeterogeneousTemporalTransport_generic b ha hl
  refine ⟨hg.1, hg.2.2.1, hg.2.2.2.1, ?_, ?_⟩
  · intro h hh
    exact ⟨(hg.2.1 h hh).2, hg.2.2.2.2.2 h hh⟩
  · intro i
    obtain ⟨ha', himage, hsf, htf⟩ := bridge_constructs_frozen_signatures b ha hl hd hupdates hb i
    refine ⟨hrun, hbc, hupdates, hread, ?_, ha', himage, rfl, rfl,
      (hread.2.2 i.val i.property).1, (hread.2.2 i.val i.property).2,
      congrArg bridgeCodeOfObservation (hread.2.2 i.val i.property).1,
      congrArg bridgeCodeOfObservation (hread.2.2 i.val i.property).2, hsf, htf⟩
    intro x y _ _ hc word trace
    exact bridge_defined_future_sufficient b hb x y hc word trace

theorem bridge_frozen_snapshot_exists
    (b : RawBridge H S T E R SC TC RR M) (ha : BridgeAdmissible b)
    (hl : BridgePrimitiveLaws b) (hd : SnapshotAuditCheck b (bridgeSnapshotAudit b))
    (hbc : BridgeRunCoherence b) (hrun : SnapshotRunCheck b)
    (hread : BridgeSnapshotReadoutCheck b) (hupdates : BridgeRunReadoutLaws b)
    (hb : BridgeFutureBisim b) :
    ∃ i : Audited b.auditFrontier, FrozenBridgeSnapshotResult b ha hl hd i := by
  have hg := bundledHeterogeneousTemporalTransport_frozen b ha hl hd hbc hrun hread hupdates hb
  obtain ⟨i⟩ := audited_nonempty b.auditFrontier hd.1
  exact ⟨i, hg.2.2.2.2 i⟩

/-- Proposal corollaries alone take candidate components. Every component
must equal the defined one on the ENTIRE bridge-computed closure. -/
def BridgeFutureProposalCheck (b : RawBridge H S T E R SC TC RR M)
    (candidate : FullFutureModel b.RunState b.RunAction b.RunOutcome
      (BridgeRunCode b) (BridgeRunObservation b)) : Prop :=
  candidate.outcomes = b.runOutcomes ∧ ∀ x, BridgeFutureClosure b x →
    candidate.code x = bridgeRunCode b x ∧ candidate.observe x = bridgeRunObservation b x ∧
    ∀ a o, candidate.weight x a o = (bridgeRunDynamics b).actionRow x a o ∧
      candidate.next x a o = b.runUpdate x a o

theorem bridge_defined_proposal_check (b : RawBridge H S T E R SC TC RR M) :
    BridgeFutureProposalCheck b (bridgeFutureModel b) :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩⟩

theorem bridge_proposal_observation_mismatch
    (b : RawBridge H S T E R SC TC RR M)
    (candidate : FullFutureModel b.RunState b.RunAction b.RunOutcome
      (BridgeRunCode b) (BridgeRunObservation b)) (x : b.RunState)
    (hx : BridgeFutureClosure b x)
    (hne : candidate.observe x ≠ bridgeRunObservation b x) :
    ¬ BridgeFutureProposalCheck b candidate := fun h => hne (h.2 x hx).2.1

/-- Proposals never replace the defined result: acceptance additionally proves
all five components equal the bridge-owned functions on the whole closure. -/
structure FrozenBridgeProposalResult
    (b : RawBridge H S T E R SC TC RR M) (ha : BridgeAdmissible b)
    (hl : BridgePrimitiveLaws b) (hd : SnapshotAuditCheck b (bridgeSnapshotAudit b))
    (candidate : FullFutureModel b.RunState b.RunAction b.RunOutcome
      (BridgeRunCode b) (BridgeRunObservation b)) (i : Audited b.auditFrontier) : Prop where
  canonical : FrozenBridgeSnapshotResult b ha hl hd i
  equalityOnClosure : BridgeFutureProposalCheck b candidate

/-- Equality of proposal trace laws follows from the closure-wide equations;
there is no supplied derived future law and no bounded-word check. -/
theorem bridge_proposal_future_eq_defined
    (b : RawBridge H S T E R SC TC RR M)
    (candidate : FullFutureModel b.RunState b.RunAction b.RunOutcome
      (BridgeRunCode b) (BridgeRunObservation b))
    (h : BridgeFutureProposalCheck b candidate) (x : b.RunState)
    (hx : BridgeFutureClosure b x) (word : List b.RunAction)
    (trace : List (BridgeRunObservation b)) :
    letI := bridgeRunObservationDecEq b
    fullFuture candidate x word trace = bridgeFuture b x word trace := by
  letI := bridgeRunObservationDecEq b
  change fullFuture candidate x word trace = fullFuture (bridgeFutureModel b) x word trace
  induction word generalizing x trace with
  | nil => simp only [fullFuture, (h.2 x hx).2.1]; rfl
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      simp only [fullFuture]
      rw [(h.2 x hx).2.1]
      by_cases ho : first = bridgeRunObservation b x
      · simp only [show (bridgeFutureModel b).observe x = bridgeRunObservation b x from rfl,
          ho, if_true]
        rw [h.1]
        apply congrArg List.sum
        apply List.map_congr_left
        intro o hm
        obtain ⟨hw, hn⟩ := (h.2 x hx).2.2 a o
        rw [hw, hn, ih (b.runUpdate x a o) (FutureClosure.step hx a o hm) tail]
        rfl
      · simp only [show (bridgeFutureModel b).observe x = bridgeRunObservation b x from rfl,
          ho, if_false]

theorem bridge_proposal_future_sufficient_on_closure
    (b : RawBridge H S T E R SC TC RR M)
    (candidate : FullFutureModel b.RunState b.RunAction b.RunOutcome
      (BridgeRunCode b) (BridgeRunObservation b))
    (h : BridgeFutureProposalCheck b candidate) (hb : BridgeFutureBisim b)
    (x y : b.RunState) (hx : BridgeFutureClosure b x) (hy : BridgeFutureClosure b y)
    (hc : candidate.code x = candidate.code y)
    (word : List b.RunAction) (trace : List (BridgeRunObservation b)) :
    letI := bridgeRunObservationDecEq b
    fullFuture candidate x word trace = fullFuture candidate y word trace := by
  letI := bridgeRunObservationDecEq b
  rw [bridge_proposal_future_eq_defined b candidate h x hx,
      bridge_proposal_future_eq_defined b candidate h y hy]
  have he : bridgeRunCode b x = bridgeRunCode b y := by
    rw [← (h.2 x hx).1, ← (h.2 y hy).1]
    exact hc
  exact bridge_defined_future_sufficient b hb x y he word trace

/-- The capped-order proposal is expressible as data, never as the theorem's
model argument. It fails on any closure state whose raw order exceeds two. -/
def cappedOrderProposal (b : RawBridge H S T E R SC TC RR M) :=
  { bridgeFutureModel b with observe := fun x =>
    { bridgeRunObservation b x with order := min (b.runCounter x) 2 } }

theorem capped_order_proposal_fails (b : RawBridge H S T E R SC TC RR M)
    (x : b.RunState) (hx : BridgeFutureClosure b x) (hgt : 2 < b.runCounter x) :
    ¬ BridgeFutureProposalCheck b (cappedOrderProposal b) := by
  apply bridge_proposal_observation_mismatch b (cappedOrderProposal b) x hx
  intro he
  have ho := congrArg TemporalSnapshotReadout.order he
  change min (b.runCounter x) 2 = b.runCounter x at ho
  have hm := Nat.min_le_right (b.runCounter x) 2
  omega

/-- Names retained as proposal guards, not candidate certificate constructors. -/
theorem frozen_bridge_raw_weight_mismatch
    (b : RawBridge H S T E R SC TC RR M)
    (candidate : FullFutureModel b.RunState b.RunAction b.RunOutcome
      (BridgeRunCode b) (BridgeRunObservation b)) (x : b.RunState)
    (hx : BridgeFutureClosure b x) (a : b.RunAction) (o : b.RunOutcome)
    (hne : candidate.weight x a o ≠ (bridgeRunDynamics b).actionRow x a o) :
    ¬ BridgeFutureProposalCheck b candidate := fun h => hne ((h.2 x hx).2.2 a o).1

theorem frozen_bridge_raw_successor_mismatch
    (b : RawBridge H S T E R SC TC RR M)
    (candidate : FullFutureModel b.RunState b.RunAction b.RunOutcome
      (BridgeRunCode b) (BridgeRunObservation b)) (x : b.RunState)
    (hx : BridgeFutureClosure b x) (a : b.RunAction) (o : b.RunOutcome)
    (hne : candidate.next x a o ≠ b.runUpdate x a o) :
    ¬ BridgeFutureProposalCheck b candidate := fun h => hne ((h.2 x hx).2.2 a o).2

end CSTTT.TransportTheory
