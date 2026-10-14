import CSTTT.POS04.FutureDynamics
import CSTTT.Transport.FrozenSnapshotBridge

/-! G1c exact POS-04 snapshots. The audited frontier is the two declared
route histories, repA/repB, at the occurrences after their first and second
supported history steps. The corresponding realized events are mix1/mix2.
Thus four actual history/event/route contexts exercise a strict record edge
and both retained route tuples; both route endpoints are included. The clock
period two is the frozen C6 rule (`audit/M3_model_spec.md:22,32`). Counters
remain unbounded in C6State; these alphabets contain their exact snapshot
values, without an imposed bound. This is an audit of declared POS-04 data,
not a new model. The old four-history bridge and its controls remain available.
C6 retains its declared surrogate grade, and no physical claim is made. -/
namespace CSTTT.POS04

open CSTTT.TransportTheory
open CSTTT.Objecthood.T1Audit

/-- Restrict the generic witness to actual declared route histories. This is
the entire reachable domain of this adapter, rather than an implicit claim
about all possible T1 histories or about its counterfactual test histories. -/
def pos04SnapshotBridge : POS04RawBridge :=
  { pos04RawBridge .positive with
    frontier := routeIds.map (fun r => (routeOf r).sourceHistory) }

local instance : DecidableEq pos04SnapshotBridge.AuditIndex := inferInstanceAs (DecidableEq SnapshotIndex)

theorem snapshot_bridge_frontier_subset (h : HistoryId)
    (hh : h ∈ pos04SnapshotBridge.frontier) :
    h ∈ (pos04RawBridge .positive).frontier := by
  cases h <;> decide

theorem pos04_snapshot_bridge_admissible : BridgeAdmissible pos04SnapshotBridge := by
  have ha := pos04_bridge_admissible
  refine ⟨by decide, ?_, ?_, ?_, ha.2.2.2.2.1, ?_⟩
  · intro h hh
    exact ha.2.1 h (snapshot_bridge_frontier_subset h hh)
  · exact ⟨.repA, by decide, .p1w0, .p2w1, by decide⟩
  · intro h hh x y hp
    exact ha.2.2.2.1 h (snapshot_bridge_frontier_subset h hh) x y hp
  · intro h hh s hs
    exact ha.2.2.2.2.2 h (snapshot_bridge_frontier_subset h hh) s hs

theorem pos04_snapshot_bridge_raw_laws : BridgePrimitiveLaws pos04SnapshotBridge := by
  have hl := pos04_bridge_raw_laws
  refine ⟨?_, hl.2.1, hl.2.2.1, hl.2.2.2.1, ?_, hl.2.2.2.2.2⟩
  · refine ⟨hl.1.1, hl.1.2.1, ?_, hl.1.2.2.2.1,
      hl.1.2.2.2.2.1, hl.1.2.2.2.2.2⟩
    intro h hh
    exact hl.1.2.2.1 h (snapshot_bridge_frontier_subset h hh)
  · intro h hh i hi
    exact hl.2.2.2.2.1 h (snapshot_bridge_frontier_subset h hh) i hi

def pos04SnapshotAudit := bridgeSnapshotAudit pos04SnapshotBridge

theorem pos04_snapshot_audit_check : SnapshotAuditCheck pos04SnapshotBridge pos04SnapshotAudit := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro i _
    rcases i with ⟨r, p⟩
    cases r <;> cases p <;>
      exact ⟨by decide, by decide, by decide, by decide, by decide,
        by decide, by decide, .mix1, .mix2, by decide, by decide⟩
  · intro h hh
    cases h with
    | repA => exact ⟨(.a, .endpoint), by decide, rfl, by decide⟩
    | repB => exact ⟨(.b, .endpoint), by decide, rfl, by decide⟩
    | classB => contradiction
    | split => contradiction

/-- The only partiality is for out-of-K future observations. Active frontier
observations decode all eight fields, including ownership, exactly. -/
def decodeC6Snapshot (o : C6Observation) :
    Option (TemporalSnapshotReadout (Nat × List (List Bool))
      (List KState × List EventId) Bool) :=
  match o.predictive with
  | .active m => some ⟨m, o.eventOrder, o.tickPhase, o.cumulativeProgress,
      o.endogenousRecordCount, o.routeResidue, o.maintenanceState, tagCarrierId o.owner⟩
  | .exit2 | .exit5 => none

def displayC6Snapshot (tag : Tag)
    (o : TemporalSnapshotReadout (Nat × List (List Bool))
      (List KState × List EventId) Bool) : C6Observation :=
  ⟨.active o.predictive, o.order, o.tickPhase, o.progress, o.record,
    o.residue, o.maintenance, tag⟩

def snapshotC6Code (tag : Tag)
    (o : TemporalSnapshotReadout (Nat × List (List Bool))
      (List KState × List EventId) Bool) : C6Code :=
  ⟨.active o.predictive, o.order, o.tickPhase, o.residue, o.maintenance, tag⟩

/-- Both run states use the exact raw bridge readouts for factor, accumulated
ticks, residue, maintenance and resource ownership. Event count is the
audited history occurrence; the link checks order, progress and record too. -/
def pos04SourceSnapshotRun := bridgeSourceRun pos04SnapshotBridge
def pos04TargetSnapshotRun := bridgeTargetRun pos04SnapshotBridge

def pos04SourceSnapshotObservation : SnapshotObservationData SnapshotIndex C6State C6Code C6Observation
    (Nat × List (List Bool)) (List KState × List EventId) Bool where
  run := pos04SourceSnapshotRun
  code := snapshotC6Code .source
  display := displayC6Snapshot .source
  decode := decodeC6Snapshot

def pos04TargetSnapshotObservation : SnapshotObservationData SnapshotIndex C6State C6Code C6Observation
    (Nat × List (List Bool)) (List KState × List EventId) Bool where
  run := pos04TargetSnapshotRun
  code := snapshotC6Code .target
  display := displayC6Snapshot .target
  decode := decodeC6Snapshot

theorem pos04_source_snapshot_full_observation_check :
    SnapshotObservationCheck pos04FullFuture pos04SnapshotBridge.auditFrontier
      (sourceSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit)
      pos04SourceSnapshotObservation := by
  intro i _
  rcases i with ⟨r, p⟩
  cases r <;> cases p <;> decide

theorem pos04_target_snapshot_full_observation_check :
    SnapshotObservationCheck pos04FullFuture pos04SnapshotBridge.auditFrontier
      (targetSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit)
      pos04TargetSnapshotObservation := by
  intro i _
  rcases i with ⟨r, p⟩
  cases r <;> cases p <;> decide

/-- The tag is the only changed full-interface coordinate in this isomorphic
instance. The equation is checked from the raw per-tag readouts, not assumed
as a success field. In the generic theorem each component has its own map. -/
def snapshotObservationTransfer (o : C6Observation) : C6Observation :=
  { o with owner := swapTag o.owner }

def snapshotCodeTransfer (c : C6Code) : C6Code :=
  { c with owner := swapTag c.owner }

theorem pos04_snapshot_full_interface_translation (i : SnapshotIndex) :
    pos04FullFuture.observe (pos04TargetSnapshotRun i) =
      snapshotObservationTransfer (pos04FullFuture.observe (pos04SourceSnapshotRun i)) ∧
    pos04FullFuture.code (pos04TargetSnapshotRun i) =
      snapshotCodeTransfer (pos04FullFuture.code (pos04SourceSnapshotRun i)) := by
  rcases i with ⟨r, p⟩
  cases r <;> cases p <;> decide

theorem pos04_snapshot_run_embedding :
    SnapshotRunCheck pos04SnapshotBridge := by
  intro i _
  rcases i with ⟨r, p⟩
  cases r <;> cases p <;> decide

theorem pos04_snapshot_run_coherence : BridgeRunCoherence pos04SnapshotBridge :=
  pos04_bridge_run_coherence .positive

/-- The reference is constructed from bridge-owned raw numerators and update
laws; POS-04's former standalone reference agrees with it by computation. -/
theorem pos04_snapshot_bridge_reference_eq :
    bridgeRunDynamics pos04SnapshotBridge = pos04RawFutureDynamics := by
  change RawFutureDynamics.mk outcomeClasses
    (fun x a c => (effectiveMass x a c : Rat) / 4) pos04RawFutureUpdate =
    RawFutureDynamics.mk outcomeClasses pos04RawFutureRow pos04RawFutureUpdate
  apply congrArg (fun w => RawFutureDynamics.mk outcomeClasses w pos04RawFutureUpdate)
  funext x a c
  exact pos04_raw_future_weight_link x a c

theorem pos04_snapshot_raw_bridge_dynamics_check (roots : List C6State) :
    BridgeDynamicsCheck pos04SnapshotBridge pos04RawFutureDynamics roots := by
  rw [← pos04_snapshot_bridge_reference_eq]
  exact bridge_dynamics_check_self pos04SnapshotBridge roots

theorem pos04_snapshot_readout_check : BridgeSnapshotReadoutCheck pos04SnapshotBridge := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q h; exact PredictiveNow.active.inj h
  · intro p q h; exact PredictiveNow.active.inj h
  · intro i _
    rcases i with ⟨r, p⟩
    cases r <;> cases p <;> constructor <;> rfl

theorem pos04_snapshot_defined_bisim : BridgeFutureBisim pos04SnapshotBridge :=
  pos04_defined_future_bisim .positive

theorem pos04_snapshot_readout_laws : BridgeRunReadoutLaws pos04SnapshotBridge :=
  ⟨pos04_snapshot_run_embedding, pos04_snapshot_readout_check,
    fun x _ a o _ => by
      have h := pos04_bridge_readout_updates .positive x a o
      exact {
        sourceFactor := h.sourceFactor
        targetFactor := h.targetFactor
        predictive := h.predictive
        sourcePredictive := h.sourcePredictive
        targetPredictive := h.targetPredictive
        counter := h.counter
        ticks := h.ticks
        progress := h.progress
        supportedAdvances := h.supportedAdvances
        residue := h.residue
        maintenance := h.maintenance
        ownerPreserved := h.ownerPreserved
        owner := h.owner
        sourceOwner := h.sourceOwner
        targetOwner := h.targetOwner
        writerNow := h.writerNow
        writerNext := h.writerNext
        enabledNow := h.enabledNow
        enabledNext := h.enabledNext
        recordNow := h.recordNow
        recordNext := h.recordNext
      }⟩

theorem pos04_frozen_temporal_transport :
    RepresentativeIndependent (Reachable pos04SnapshotBridge)
      (SourceHistoryClass pos04SnapshotBridge) (TargetHistoryClass pos04SnapshotBridge) ∧
    StrictRecordArrowPreserved pos04SnapshotBridge ∧ RouteStatusPreserved pos04SnapshotBridge ∧
    (∀ h, Reachable pos04SnapshotBridge h → StrictSuccessorPreserved pos04SnapshotBridge h ∧
      StrictOrderTickProgressAt pos04SnapshotBridge h) ∧
    (∀ i : Audited pos04SnapshotBridge.auditFrontier,
      FrozenBridgeSnapshotResult pos04SnapshotBridge pos04_snapshot_bridge_admissible
        pos04_snapshot_bridge_raw_laws pos04_snapshot_audit_check i) :=
  bundledHeterogeneousTemporalTransport_frozen pos04SnapshotBridge
    pos04_snapshot_bridge_admissible pos04_snapshot_bridge_raw_laws pos04_snapshot_audit_check
    pos04_snapshot_run_coherence pos04_snapshot_run_embedding pos04_snapshot_readout_check
    pos04_snapshot_readout_laws pos04_snapshot_defined_bisim

theorem pos04_frozen_snapshot_instance (i : Audited pos04SnapshotBridge.auditFrontier) :
    FrozenBridgeSnapshotResult pos04SnapshotBridge
      pos04_snapshot_bridge_admissible pos04_snapshot_bridge_raw_laws pos04_snapshot_audit_check i :=
  pos04_frozen_temporal_transport.2.2.2.2 i

def snapshotEndpointA : Audited pos04SnapshotBridge.auditFrontier := ⟨(.a, .endpoint), by decide⟩
def snapshotEndpointB : Audited pos04SnapshotBridge.auditFrontier := ⟨(.b, .endpoint), by decide⟩

theorem pos04_frozen_frontier_nonempty :
    pos04SnapshotBridge.auditFrontier.length = 4 ∧
    Nonempty (Audited pos04SnapshotBridge.auditFrontier) :=
  ⟨by decide, ⟨snapshotEndpointA⟩⟩

theorem pos04_frozen_snapshot_exists :
    ∃ i : Audited pos04SnapshotBridge.auditFrontier,
      FrozenBridgeSnapshotResult pos04SnapshotBridge
        pos04_snapshot_bridge_admissible pos04_snapshot_bridge_raw_laws pos04_snapshot_audit_check i :=
  ⟨snapshotEndpointA, pos04_frozen_snapshot_instance snapshotEndpointA⟩

abbrev pos04FrozenSource (i : Audited pos04SnapshotBridge.auditFrontier) :=
  frozenBridgeSource pos04SnapshotBridge i
abbrev pos04FrozenTarget (i : Audited pos04SnapshotBridge.auditFrontier) :=
  frozenBridgeTarget pos04SnapshotBridge i

/-- Equal predictive classes behind genuine different pasts, and different
retained route residues, survive the finite codec on both tagged carriers. -/
theorem pos04_frozen_representatives_nontrivial :
    sourceHistory .repA ≠ sourceHistory .repB ∧
    (pos04FrozenSource snapshotEndpointA).predictiveNow.predictiveClass =
      (pos04FrozenSource snapshotEndpointB).predictiveNow.predictiveClass ∧
    (pos04FrozenTarget snapshotEndpointA).predictiveNow.predictiveClass =
      (pos04FrozenTarget snapshotEndpointB).predictiveNow.predictiveClass ∧
    (pos04FrozenSource snapshotEndpointA).predictiveNow.routeResidue ≠
      (pos04FrozenSource snapshotEndpointB).predictiveNow.routeResidue ∧
    (pos04FrozenTarget snapshotEndpointA).predictiveNow.routeResidue ≠
      (pos04FrozenTarget snapshotEndpointB).predictiveNow.routeResidue := by
  have hroute : routeRegister .a ≠ routeRegister .b := by decide
  refine ⟨by decide, Subtype.ext rfl, Subtype.ext rfl, ?_, ?_⟩
  · intro h
    exact hroute (congrArg Subtype.val h)
  · intro h
    exact hroute (congrArg Subtype.val h)

theorem pos04_frozen_snapshot_owners_distinct (i : Audited pos04SnapshotBridge.auditFrontier) :
    (pos04FrozenSource i).owner = tagCarrierId (resourceOwner .source) ∧
    (pos04FrozenTarget i).owner = tagCarrierId (resourceOwner .target) ∧
    (pos04FrozenSource i).owner ≠ (pos04FrozenTarget i).owner := by
  refine ⟨rfl, rfl, ?_⟩
  change tagCarrierId .source ≠ tagCarrierId .target
  decide

/-- The finite predictive codes are exactly the raw action/hazard M fibers,
and therefore exactly the imported T1 partition, as required by the L5 rule. -/
theorem pos04_frozen_predictive_M_link (i j : Audited pos04SnapshotBridge.auditFrontier) :
    ((pos04FrozenSource i).predictiveNow.predictiveClass =
        (pos04FrozenSource j).predictiveNow.predictiveClass ↔
      taggedMClass .source (pos04SnapshotAudit.snapshot i.val).state =
        taggedMClass .source (pos04SnapshotAudit.snapshot j.val).state) ∧
    ((pos04FrozenTarget i).predictiveNow.predictiveClass =
        (pos04FrozenTarget j).predictiveNow.predictiveClass ↔
      taggedMClass .target (pos04SnapshotAudit.snapshot i.val).state =
        taggedMClass .target (pos04SnapshotAudit.snapshot j.val).state) := by
  constructor
  · exact (snapshot_value_no_loss pos04SnapshotBridge.auditFrontier
      (fun k => (sourceSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit k).predictive)
      i j).trans (rawM_iff_imported_M .source _ _)
  · exact (snapshot_value_no_loss pos04SnapshotBridge.auditFrontier
      (fun k => (targetSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit k).predictive)
      i j).trans (rawM_iff_imported_M .target _ _)

theorem pos04_frozen_route_status :
    routeStatusOfRaw pos04SnapshotBridge = .routeIndexed :=
  pos04_computed_route_status

/-- The two full codes, including route, maintenance and owner, are computed
from the decoded frozen fields. This theorem is about the original C6 F and
all finite words, rather than only a snapshot equality or a bounded probe. -/
theorem pos04_frozen_source_all_word_future
    (i j : Audited pos04SnapshotBridge.auditFrontier)
    (h : decodeFrozenSnapshot pos04SnapshotBridge.auditFrontier
        (sourceSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit) (pos04FrozenSource i) =
      decodeFrozenSnapshot pos04SnapshotBridge.auditFrontier
        (sourceSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit) (pos04FrozenSource j))
    (word : List Action) (trace : List C6Observation) :
    F .positive (pos04SourceSnapshotRun i.val) word trace =
      F .positive (pos04SourceSnapshotRun j.val) word trace := by
  rw [← pos04_full_future_eq_c6, ← pos04_full_future_eq_c6]
  exact frozen_snapshot_future_from_fields pos04FullFuture pos04_full_one_step_bisim
    pos04SnapshotBridge.auditFrontier _ pos04SourceSnapshotObservation
    pos04_source_snapshot_full_observation_check i j h word trace

theorem pos04_frozen_target_all_word_future
    (i j : Audited pos04SnapshotBridge.auditFrontier)
    (h : decodeFrozenSnapshot pos04SnapshotBridge.auditFrontier
        (targetSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit) (pos04FrozenTarget i) =
      decodeFrozenSnapshot pos04SnapshotBridge.auditFrontier
        (targetSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit) (pos04FrozenTarget j))
    (word : List Action) (trace : List C6Observation) :
    F .positive (pos04TargetSnapshotRun i.val) word trace =
      F .positive (pos04TargetSnapshotRun j.val) word trace := by
  rw [← pos04_full_future_eq_c6, ← pos04_full_future_eq_c6]
  exact frozen_snapshot_future_from_fields pos04FullFuture pos04_full_one_step_bisim
    pos04SnapshotBridge.auditFrontier _ pos04TargetSnapshotObservation
    pos04_target_snapshot_full_observation_check i j h word trace

def pos04SnapshotRepControl : POS04RawBridge :=
  { pos04RawBridge .bridgeRep with frontier := pos04SnapshotBridge.frontier }

theorem neg_bridge_rep_snapshot_not_admissible : ¬ BridgeAdmissible pos04SnapshotRepControl := by
  intro ha
  have heq := (ha.2.1 .repB (by decide)).2
  have hneq : targetHistoryFor .bridgeRep .repB ≠ sourceHistory .repB := by decide
  exact hneq (by simpa [pos04SnapshotRepControl, pos04RawBridge] using heq)

/-- Reuse the declared NEG-C6-RECORD writer intervention. The snapshot and
bridge tables stay fixed; the same observation-link test detects the absent
target route-B writer instead of certifying its positive record readout. -/
def pos04SnapshotWriterControl : FullFutureModel C6State Action OutcomeClass C6Code C6Observation :=
  { pos04FullFuture with observe := observe .negRecord, next := c6Next .negRecord }

theorem neg_record_snapshot_observation_link_fails :
    ¬ SnapshotObservationCheck pos04SnapshotWriterControl pos04SnapshotBridge.auditFrontier
      (targetSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit)
      pos04TargetSnapshotObservation := by
  intro h
  have hrecord := congrArg C6Observation.endogenousRecordCount
    (h (.b, .endpoint) (by decide)).1
  have hneq : (pos04SnapshotWriterControl.observe
      (pos04TargetSnapshotObservation.run (.b, .endpoint))).endogenousRecordCount ≠
      (pos04TargetSnapshotObservation.display
        (targetSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit (.b, .endpoint))).endogenousRecordCount := by
    decide
  exact hneq hrecord

/-- The bridge's raw transition numerators are the very action rows whose
M-pushforward defines the future dynamics; no separate transition oracle. -/
theorem pos04_snapshot_bridge_action_row_link (s t : KState) (a : Action) :
    pos04SnapshotBridge.sourceActionStep s (actions.idxOf a) t =
      rowWeight (actionRow .source s a) t ∧
    pos04SnapshotBridge.targetActionStep s (actions.idxOf a) t =
      rowWeight (actionRow .target s a) t := by
  cases a <;> exact ⟨rfl, rfl⟩

/-- Roots from both exact audited frontiers; future closure is raw-driven. -/
def pos04SnapshotFutureRoots : List C6State :=
  bridgeFutureRoots pos04SnapshotBridge

theorem pos04_snapshot_future_roots_funded :
    ∀ x ∈ pos04SnapshotFutureRoots, x.funded = true := by
  decide

theorem pos04_snapshot_future_closure_ledger (x : C6State)
    (hx : FutureClosure pos04RawFutureDynamics pos04SnapshotFutureRoots x) :
    x.funded = true ∧ rawFutureBudget x = 1 ∧
      rawFutureBudgetAfter x = rawFutureBudget x :=
  pos04_future_closure_ledger _ pos04_snapshot_future_roots_funded x hx

/-- Review controls leave observations and codes unchanged. Neither can
certify the future of the raw action-row/counter/ledger execution. -/
def pos04UniformWeightControl : FullFutureModel C6State Action OutcomeClass C6Code C6Observation :=
  { pos04FullFuture with weight := fun _ _ _ => (1 : Rat) / 9 }

def pos04IdentitySuccessorControl : FullFutureModel C6State Action OutcomeClass C6Code C6Observation :=
  { pos04FullFuture with next := fun x _ _ => x }

theorem review_controls_snapshot_links_unchanged :
    SnapshotObservationCheck pos04UniformWeightControl pos04SnapshotBridge.auditFrontier
      (sourceSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit)
      pos04SourceSnapshotObservation ∧
    SnapshotObservationCheck pos04UniformWeightControl pos04SnapshotBridge.auditFrontier
      (targetSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit)
      pos04TargetSnapshotObservation ∧
    SnapshotObservationCheck pos04IdentitySuccessorControl pos04SnapshotBridge.auditFrontier
      (sourceSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit)
      pos04SourceSnapshotObservation ∧
    SnapshotObservationCheck pos04IdentitySuccessorControl pos04SnapshotBridge.auditFrontier
      (targetSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit)
      pos04TargetSnapshotObservation :=
  ⟨pos04_source_snapshot_full_observation_check, pos04_target_snapshot_full_observation_check,
    pos04_source_snapshot_full_observation_check, pos04_target_snapshot_full_observation_check⟩

private theorem snapshot_source_endpoint_root :
    FutureClosure pos04RawFutureDynamics pos04SnapshotFutureRoots
      (pos04SourceSnapshotRun (.a, .endpoint)) :=
  FutureClosure.root _ (by decide)

theorem uniform_weights_dynamics_link_fails :
    ¬ FutureDynamicsCheck pos04UniformWeightControl pos04RawFutureDynamics
      pos04SnapshotFutureRoots := by
  intro h
  have hw := (h.2 _ snapshot_source_endpoint_root .cw .m3).1
  have hn : pos04UniformWeightControl.weight (pos04SourceSnapshotRun (.a, .endpoint)) .cw .m3 ≠
      pos04RawFutureDynamics.actionRow (pos04SourceSnapshotRun (.a, .endpoint)) .cw .m3 := by
    decide +kernel
  exact hn hw

theorem identity_successor_dynamics_link_fails :
    ¬ FutureDynamicsCheck pos04IdentitySuccessorControl pos04RawFutureDynamics
      pos04SnapshotFutureRoots := by
  intro h
  have hn := congrArg C6State.eventCount
    (h.2 _ snapshot_source_endpoint_root .cw .m3).2
  have hneq : (pos04IdentitySuccessorControl.next
      (pos04SourceSnapshotRun (.a, .endpoint)) .cw .m3).eventCount ≠
    (pos04RawFutureDynamics.update
      (pos04SourceSnapshotRun (.a, .endpoint)) .cw .m3).eventCount := by decide
  exact hneq hn

/-- Eddy's substitution changes BOTH the candidate and proposed reference,
while keeping the audited bridge, snapshots, and observation/code fixed. -/
def pos04UniformStationaryModel : FullFutureModel C6State Action OutcomeClass C6Code C6Observation :=
  { pos04FullFuture with
    weight := fun _ _ _ => (1 : Rat) / 9
    next := fun x _ _ => x }

def pos04UniformStationaryRaw : RawFutureDynamics C6State Action OutcomeClass :=
  { pos04RawFutureDynamics with
    actionRow := fun _ _ _ => (1 : Rat) / 9
    update := fun x _ _ => x }

theorem uniform_stationary_candidate_matches_proposal (roots : List C6State) :
    FutureDynamicsCheck pos04UniformStationaryModel pos04UniformStationaryRaw roots :=
  ⟨rfl, fun _ _ _ _ => ⟨rfl, rfl⟩⟩

theorem uniform_stationary_candidate_bisim : FullOneStepBisim pos04UniformStationaryModel := by
  intro x y h
  refine ⟨(pos04_full_one_step_bisim x y h).1, ?_⟩
  intro a o
  exact ⟨rfl, h⟩

theorem uniform_stationary_snapshot_links_intact :
    SnapshotObservationCheck pos04UniformStationaryModel pos04SnapshotBridge.auditFrontier
      (sourceSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit)
      pos04SourceSnapshotObservation ∧
    SnapshotObservationCheck pos04UniformStationaryModel pos04SnapshotBridge.auditFrontier
      (targetSnapshotReadout pos04SnapshotBridge pos04SnapshotAudit)
      pos04TargetSnapshotObservation :=
  ⟨pos04_source_snapshot_full_observation_check, pos04_target_snapshot_full_observation_check⟩

private theorem snapshot_endpoint_in_bridge_closure :
    FutureClosure (bridgeRunDynamics pos04SnapshotBridge) pos04SnapshotFutureRoots
      (pos04SourceSnapshotRun (.a, .endpoint)) := by
  rw [pos04_snapshot_bridge_reference_eq]
  exact snapshot_source_endpoint_root

theorem uniform_stationary_raw_weight_link_fails :
    ¬ BridgeDynamicsCheck pos04SnapshotBridge pos04UniformStationaryRaw pos04SnapshotFutureRoots := by
  apply bridge_dynamics_weight_mismatch pos04SnapshotBridge pos04UniformStationaryRaw
    pos04SnapshotFutureRoots (pos04SourceSnapshotRun (.a, .endpoint))
    snapshot_endpoint_in_bridge_closure .cw .m3
  decide +kernel

theorem uniform_stationary_raw_successor_link_fails :
    ¬ BridgeDynamicsCheck pos04SnapshotBridge pos04UniformStationaryRaw pos04SnapshotFutureRoots := by
  apply bridge_dynamics_successor_mismatch pos04SnapshotBridge pos04UniformStationaryRaw
    pos04SnapshotFutureRoots (pos04SourceSnapshotRun (.a, .endpoint))
    snapshot_endpoint_in_bridge_closure .cw .m3
  intro h
  have hn := congrArg C6State.eventCount h
  change 2 = 3 at hn
  contradiction

/-- Moving the same stationary corruption into the bridge's new raw fields
also fails coherence with its unchanged genuine run counter law. -/
def pos04UniformStationaryBridge : POS04RawBridge :=
  { pos04SnapshotBridge with
    runNumerator := fun _ _ _ => 1
    runDenominator := 9
    runUpdate := fun x _ _ => x }

theorem uniform_stationary_bridge_coherence_fails :
    ¬ BridgeRunCoherence pos04UniformStationaryBridge := by
  intro h
  have hc := (h.2.2.2.2 (pos04SourceSnapshotRun (.a, .endpoint)) .cw .m3).2.2.1
  change 2 = 3 at hc
  contradiction

/-- Native proposals are diagnostic only; none is an input to the certificate. -/
def pos04NativeUniformWeights :=
  { bridgeFutureModel pos04SnapshotBridge with weight := fun _ _ _ => (1 : Rat) / 9 }
def pos04NativeIdentitySuccessor :=
  { bridgeFutureModel pos04SnapshotBridge with next := fun x _ _ => x }
def pos04NativeUniformStationary : FullFutureModel C6State Action OutcomeClass
    (BridgeRunCode pos04SnapshotBridge) (BridgeRunObservation pos04SnapshotBridge) :=
  { bridgeFutureModel pos04SnapshotBridge with
    weight := fun _ _ _ => (1 : Rat) / 9
    next := fun x _ _ => x }

theorem uniform_weights_frozen_result_fails (i : Audited pos04SnapshotBridge.auditFrontier) :
    ¬ FrozenBridgeProposalResult pos04SnapshotBridge pos04_snapshot_bridge_admissible
      pos04_snapshot_bridge_raw_laws pos04_snapshot_audit_check pos04NativeUniformWeights i := by
  intro h
  exact frozen_bridge_raw_weight_mismatch pos04SnapshotBridge pos04NativeUniformWeights
    (pos04SourceSnapshotRun (.a, .endpoint)) snapshot_endpoint_in_bridge_closure .cw .m3
    (by decide +kernel) h.equalityOnClosure

theorem identity_successor_frozen_result_fails (i : Audited pos04SnapshotBridge.auditFrontier) :
    ¬ FrozenBridgeProposalResult pos04SnapshotBridge pos04_snapshot_bridge_admissible
      pos04_snapshot_bridge_raw_laws pos04_snapshot_audit_check pos04NativeIdentitySuccessor i := by
  intro h
  apply frozen_bridge_raw_successor_mismatch pos04SnapshotBridge pos04NativeIdentitySuccessor
    (pos04SourceSnapshotRun (.a, .endpoint)) snapshot_endpoint_in_bridge_closure .cw .m3
    _ h.equalityOnClosure
  intro he
  have hn := congrArg C6State.eventCount he
  change 2 = 3 at hn
  contradiction

theorem uniform_stationary_substitution_frozen_result_fails
    (i : Audited pos04SnapshotBridge.auditFrontier) :
    ¬ FrozenBridgeProposalResult pos04SnapshotBridge pos04_snapshot_bridge_admissible
      pos04_snapshot_bridge_raw_laws pos04_snapshot_audit_check pos04NativeUniformStationary i := by
  intro h
  exact frozen_bridge_raw_weight_mismatch pos04SnapshotBridge pos04NativeUniformStationary
    (pos04SourceSnapshotRun (.a, .endpoint)) snapshot_endpoint_in_bridge_closure .cw .m3
    (by decide +kernel) h.equalityOnClosure

/-- A supported funded step from an actual audited endpoint has raw order 3. -/
def pos04AfterEndpoint := pos04SnapshotBridge.runUpdate
  (pos04SourceSnapshotRun (.a, .endpoint)) .cw .m3

theorem pos04_after_endpoint_supported :
    (bridgeRunDynamics pos04SnapshotBridge).actionRow
      (pos04SourceSnapshotRun (.a, .endpoint)) .cw .m3 = 1 ∧
    pos04SnapshotBridge.runCounter pos04AfterEndpoint = 3 := by
  exact ⟨by decide +kernel, rfl⟩

theorem pos04_after_endpoint_in_closure : BridgeFutureClosure pos04SnapshotBridge pos04AfterEndpoint := by
  apply FutureClosure.step snapshot_endpoint_in_bridge_closure .cw .m3
  change OutcomeClass.m3 ∈ outcomeClasses
  simp [outcomeClasses]

theorem pos04_capped_order_proposal_fails :
    ¬ BridgeFutureProposalCheck pos04SnapshotBridge (cappedOrderProposal pos04SnapshotBridge) :=
  capped_order_proposal_fails pos04SnapshotBridge pos04AfterEndpoint
    pos04_after_endpoint_in_closure (by decide)

theorem pos04_capped_order_frozen_result_fails
    (i : Audited pos04SnapshotBridge.auditFrontier) :
    ¬ FrozenBridgeProposalResult pos04SnapshotBridge pos04_snapshot_bridge_admissible
      pos04_snapshot_bridge_raw_laws pos04_snapshot_audit_check
      (cappedOrderProposal pos04SnapshotBridge) i :=
  fun h => pos04_capped_order_proposal_fails h.equalityOnClosure

/-- The attack agrees at all four roots; the rejecting witness is in the
future closure, not a changed snapshot or an independently supplied model. -/
theorem pos04_capped_order_roots_unchanged :
    ∀ x ∈ bridgeFutureRoots pos04SnapshotBridge,
      (cappedOrderProposal pos04SnapshotBridge).observe x = bridgeRunObservation pos04SnapshotBridge x := by
  intro x hx
  have hl : bridgeFutureRoots pos04SnapshotBridge =
      [pos04SourceSnapshotRun (.a, .afterFirst), pos04SourceSnapshotRun (.a, .endpoint),
       pos04SourceSnapshotRun (.b, .afterFirst), pos04SourceSnapshotRun (.b, .endpoint),
       pos04TargetSnapshotRun (.a, .afterFirst), pos04TargetSnapshotRun (.a, .endpoint),
       pos04TargetSnapshotRun (.b, .afterFirst), pos04TargetSnapshotRun (.b, .endpoint)] := rfl
  rw [hl] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h <;> subst x <;> rfl

end CSTTT.POS04
