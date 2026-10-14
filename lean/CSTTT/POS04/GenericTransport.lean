import CSTTT.POS04.Assembly
import CSTTT.POS04.RawRunDynamics
import CSTTT.Transport.RawBridge

/-! G1 adapters to the committed FIACH-POS-04 data
(`audit/M3_model_spec.md:21,30-31,40-48`). The generic predictive future
probe is the finite action-word M-class numerator computed from `actionRow`.
It omits the full C6 observation interface, whose separate POS-04 result is
`C6Pass`. This adapter therefore does not by itself instantiate every field
of the frozen `TemporalSignature`.
No success labels or free propositions are used as raw fields. -/
namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory
open CSTTT.RecordTheory

theorem action_rows_equal_of_rawM (s t : KState) (a : Action) :
    rawM .source s = rawM .source t →
      actionRow .source s a = actionRow .source t a := by
  cases s <;> cases t <;> cases a <;> decide

/-- Event support and record numbers are read from the realized POS-04 stage
and event tables. A record edge additionally needs the corresponding raw
writer availability on every compared route. One mixed event leads to the
next; the target also supports the exit edge. -/
def eventStageRank (e : EventId) : Nat :=
  stages.idxOf (eventOf e).toStage

def sourceRecordEdges : List (EventId × EventId) :=
  eventIds.flatMap fun a =>
    eventIds.filterMap fun b =>
      if (eventOf a).toStage == (eventOf b).fromStage &&
          (eventOf a).sourceSupport && (eventOf b).sourceSupport &&
          routeIds.all (recordWriterAvailable .source) &&
          decide ((eventOf a).toStage ∈ realizedStages) &&
          decide ((eventOf b).toStage ∈ realizedStages) then some (a,b)
      else none

def targetRecordEdges : List (EventId × EventId) :=
  eventIds.flatMap fun a =>
    eventIds.filterMap fun b =>
      if (eventOf a).toStage == (eventOf b).fromStage &&
          (eventOf a).targetSupport && (eventOf b).targetSupport &&
          routeIds.all (recordWriterAvailable .target) &&
          decide ((eventOf a).toStage ∈ realizedStages) &&
          decide ((eventOf b).toStage ∈ realizedStages) then some (a,b)
      else none

theorem source_record_edges_eq : sourceRecordEdges = [(.mix1,.mix2)] := by decide
theorem target_record_edges_eq : targetRecordEdges = [(.mix1,.mix2),(.mix2,.exit)] := by decide

def pos04RecordTransport : RawRecordTransport EventId EventId where
  sourceEdges := sourceRecordEdges
  targetEdges := targetRecordEdges
  mapEvent := id
  sourceRecord := eventStageRank
  targetRecord := eventStageRank
  translate := id
  increment := fun a b => eventStageRank b - eventStageRank a

theorem pos04_record_laws :
    RecordMapStepLaw pos04RecordTransport ∧
    PositiveRecordIncrement pos04RecordTransport := by
  constructor
  · constructor
    · intro a b
      cases a <;> cases b <;> decide
    · intro a
      rfl
  · intro a b
    cases a <;> cases b <;>
      simp [SourceArrow, pos04RecordTransport, source_record_edges_eq,
        eventStageRank, eventOf, stages, events] at * <;> decide

theorem pos04_record_strict_edge :
    SourceArrow pos04RecordTransport .mix1 .mix2 ∧
    TargetArrow pos04RecordTransport .mix1 .mix2 := by
  constructor <;>
    simp [SourceArrow, TargetArrow, pos04RecordTransport,
      source_record_edges_eq, target_record_edges_eq,
      eventStageRank, eventOf, stages, events] <;> decide

theorem pos04_record_arrow_instance :
    ∀ a b, SourceArrow pos04RecordTransport a b →
      TargetArrow pos04RecordTransport
        (pos04RecordTransport.mapEvent a)
        (pos04RecordTransport.mapEvent b) :=
  monotoneRecordDescentTransportsArrow_generic
    pos04RecordTransport pos04_record_laws.1 pos04_record_laws.2

def targetHistoryFor (v : ReceiverVariant) (h : HistoryId) : List KState :=
  match receiverFactor v h with
  | some target => (sourceHistory h).dropLast ++ [target]
  | none => []

/-- Progress counts supported transitions in a raw history prefix. -/
def prefixProgress (tag : Tag) (path : List KState) (i : Nat) : Nat :=
  let pathPrefix := path.take (i + 1)
  ((pathPrefix.zip (pathPrefix.drop 1)).filter
    (fun pair => taggedPNum tag pair.1 pair.2 > 0)).length

abbrev POS04RawBridge :=
  RawBridge HistoryId KState KState EventId RouteId
    (Nat × List (List Bool)) (Nat × List (List Bool))
    (List KState × List EventId) Bool

def pos04RawBridge (v : ReceiverVariant := .positive) : POS04RawBridge where
  frontier := bridgeFrontier
  sourceHistory := sourceHistory
  targetHistory := targetHistoryFor v
  mapState := id
  sourceCoord := publicPosition
  targetCoord := publicPosition
  mapCoord := id
  sourceClass := rawM .source
  targetClass := rawM .target
  mapClass := id
  sourceStates := kernel
  targetStates := kernel
  sourceClassDecEq := inferInstance
  targetClassDecEq := inferInstance
  sourceActionStep := fun s a u =>
    match actions[a]? with
    | none => 0
    | some action => rowWeight (actionRow .source s action) u
  targetActionStep := fun s a u =>
    match actions[a]? with
    | none => 0
    | some action => rowWeight (actionRow .target s action) u
  sourceStep := taggedPNum .source
  targetStep := taggedPNum .target
  sourceOrder := fun h => List.range (sourceHistory h).length
  targetOrder := fun h => List.range (targetHistoryFor v h).length
  sourceTick := fun s => tickIncrement .source s (canonicalAction s)
  targetTick := fun s => tickIncrement .target s (canonicalAction s)
  sourceProgress := historyProgress .source
  targetProgress := fun h =>
    ((targetHistoryFor v h).zip ((targetHistoryFor v h).drop 1)).length
  sourceProgressAt := fun h i => prefixProgress .source (sourceHistory h) i
  targetProgressAt := fun h i => prefixProgress .target (targetHistoryFor v h) i
  record := pos04RecordTransport
  routeIds := routeIds
  routeHistory := fun r => (routeOf r).sourceHistory
  sourceRoute := fun r => (routeOf r).eventPath
  targetRoute := fun r => (routeOf r).eventPath
  sourceResidue := routeRegister
  targetResidue := routeRegister
  sourceReadout := routeFutureOutput .positive
  targetReadout := routeFutureOutput .positive
  targetRouteSteps := fun r =>
    (routeFundedStep .positive r).filterMap fun step =>
      match step.register, routeReadFromState step with
      | some register, some readout => some (register, readout)
      | _, _ => none
  sourceMaintenance := fun _ => c8Available .funded .source
  targetMaintenance := fun _ => c8Available .funded .target
  mapMaintenance := id
  sourceOwner := fun _ => tagCarrierId (resourceOwner .source)
  targetOwner := fun _ => tagCarrierId (resourceOwner .target)
  targetId := tagCarrierId .target
  RunState := C6State
  RunAction := Action
  RunOutcome := OutcomeClass
  runOutcomeDecEq := inferInstance
  runOutcomes := outcomeClasses
  runDenominator := 4
  runNumerator := effectiveMass
  runUpdate := pos04RawFutureUpdate
  runSourceFactor := fun x => if x.tag = .source then
    match x.factor with | .inK s => some s | _ => none else none
  runTargetFactor := fun x => if x.tag = .target then
    match x.factor with | .inK s => some s | _ => none else none
  runSourceOutcome := fun s => classOf .source (.inK s)
  runTargetOutcome := fun s => classOf .target (.inK s)
  runActionIndex := actions.idxOf
  runEnabled := fun x => x.funded && rechargeAvailableAfterWithdrawal x.tag
  runCounter := C6State.eventCount
  runTicks := C6State.tickCount
  RunPredictive := PredictiveNow
  runPredictiveDecEq := inferInstance
  residueDecEq := inferInstance
  maintenanceDecEq := inferInstance
  runPredictive := fun x => predictiveNow x.tag x.factor
  sourcePredictiveMap := PredictiveNow.active
  targetPredictiveMap := PredictiveNow.active
  runProgress := C6State.eventCount
  runRecordWriter := fun x => writerForResidue .positive x.tag x.routeResidue
  runResidue := C6State.routeResidue
  runMaintenance := C6State.funded
  runOwner := fun x => tagCarrierId (resourceOwner x.tag)
  runRecord := fun x => if x.funded && writerForResidue .positive x.tag x.routeResidue
    then x.eventCount else 0
  runSourceFactorUpdate := fun x _ o => if x.tag = .source then
    match classRepresentative o with | .inK s => some s | _ => none else none
  runTargetFactorUpdate := fun x _ o => if x.tag = .target then
    match classRepresentative o with | .inK s => some s | _ => none else none
  runPredictiveUpdate := fun x _ o => predictiveNow x.tag (classRepresentative o)
  runTickAdvance := fun x a _ => match x.factor with
    | .inK s => tickIncrement x.tag s a | .p2w0 | .p5w1 => 0
  runProgressAdvance := fun _ _ _ => 1
  runWriterRule := fun residue _ => writerForResidue .positive .source residue
  runResidueUpdate := fun residue _ _ => residue
  runMaintenanceUpdate := fun funded _ _ =>
    funded && decide (ledger.initialBudget - ledger.actionCost + ledger.rechargePerAction > 0)
  runOwnerUpdate := fun owner _ _ => owner
  runEnabledRule := fun funded _ => funded
  runTickPeriod := 2
  AuditIndex := SnapshotIndex
  auditFrontier := routeIds.flatMap fun r => snapshotPositions.map (r, ·)
  auditHistory := fun (r, _) => (routeOf r).sourceHistory
  auditState := fun (r, p) =>
    (sourceHistory (routeOf r).sourceHistory).getD (snapshotOccurrence p) .p0w0
  auditOccurrence := fun (_, p) => snapshotOccurrence p
  auditEvent := fun (_, p) => snapshotEvent p
  auditRoute := Prod.fst
  makeSourceRun := fun s count ticks residue funded =>
    ⟨.source, .inK s, count, ticks, residue, funded⟩
  makeTargetRun := fun s count ticks residue funded =>
    ⟨.target, .inK s, count, ticks, residue, funded⟩

local instance : LawfulBEq OutcomeClass where
  rfl := by intro a; cases a <;> rfl
  eq_of_beq := by intro a b h; cases a <;> cases b <;> cases h <;> rfl

/-- Core outcome domain of the M-pushforward; ambient exits remain separate. -/
def coreRunOutcomes : List OutcomeClass := [.m0,.m1,.m2,.m3,.m4,.m5,.m6]

private theorem core_run_outcome_mem (tag : Tag) (s : KState) :
    classOf tag (.inK s) ∈ coreRunOutcomes := by
  cases tag <;> cases s <;> decide

private theorem core_run_mass (tag : Tag) (s : KState) (a : Action) (o : OutcomeClass)
    (ho : o ∈ coreRunOutcomes) :
    classMass tag (.inK s) a o = (kernel.map fun t =>
      if classOf tag (.inK t) = o then rowWeight (actionRow tag s a) t else 0).sum := by
  have h : ∀ u ∈ kernel, ∀ v ∈ actions, ∀ c ∈ coreRunOutcomes,
      classMass tag (.inK u) v c = (kernel.map fun t =>
        if classOf tag (.inK t) = c then rowWeight (actionRow tag u v) t else 0).sum := by
    cases tag <;> decide
  exact h s (by cases s <;> decide) a (by cases a <;> decide) o ho

private theorem core_run_representative (tag : Tag) (o : OutcomeClass)
    (ho : o ∈ coreRunOutcomes) :
    ∃ k ∈ kernel, classRepresentative o = .inK k ∧ classOf tag (.inK k) = o := by
  have h : ∀ c ∈ coreRunOutcomes,
      ∃ k ∈ kernel, classRepresentative c = .inK k ∧ classOf tag (.inK k) = c := by
    cases tag <;> decide
  exact h o ho

/-- Coherence holds for every run state, not merely the snapshot roots. -/
theorem pos04_bridge_run_coherence (v : ReceiverVariant) :
    BridgeRunCoherence (pos04RawBridge v) := by
  refine ⟨by change 0 < 4; decide, ?_, ?_, ?_, ?_⟩
  · intro s _
    change classOf .source (.inK s) ∈ outcomeClasses
    cases s <;> decide
  · intro s _
    change classOf .target (.inK s) ∈ outcomeClasses
    cases s <;> decide
  · intro x a o _
    change o ∈ outcomeClasses
    cases o <;> simp [outcomeClasses]
  · intro x a o
    refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · intro s hs hen ho
      cases ht : x.tag with
      | target => simp [pos04RawBridge, ht] at hs
      | source =>
        cases hf : x.factor with
        | inK k =>
            simp [pos04RawBridge, ht, hf] at hs
            subst s
            have he : x.funded = true := by
              simpa [pos04RawBridge, ht, rechargeAvailableAfterWithdrawal] using hen
            obtain ⟨t, _, hto⟩ := ho
            have hom : o ∈ coreRunOutcomes := by
              rw [← hto]
              exact core_run_outcome_mem .source t
            have hh := core_run_mass .source k a o hom
            cases a <;> simpa [pos04RawBridge, effectiveMass, ht, hf, he,
              rechargeAvailableAfterWithdrawal, actions] using hh
        | p2w0 => simp [pos04RawBridge, ht, hf] at hs
        | p5w1 => simp [pos04RawBridge, ht, hf] at hs
    · intro s hs hen ho
      cases ht : x.tag with
      | source => simp [pos04RawBridge, ht] at hs
      | target =>
        cases hf : x.factor with
        | inK k =>
            simp [pos04RawBridge, ht, hf] at hs
            subst s
            have he : x.funded = true := by
              simpa [pos04RawBridge, ht, rechargeAvailableAfterWithdrawal] using hen
            obtain ⟨t, _, hto⟩ := ho
            have hom : o ∈ coreRunOutcomes := by
              rw [← hto]
              exact core_run_outcome_mem .target t
            have hh := core_run_mass .target k a o hom
            cases a <;> simpa [pos04RawBridge, effectiveMass, ht, hf, he,
              rechargeAvailableAfterWithdrawal, actions] using hh
        | p2w0 => simp [pos04RawBridge, ht, hf] at hs
        | p5w1 => simp [pos04RawBridge, ht, hf] at hs
    · intro s hs
      cases ht : x.tag with
      | target => simp [pos04RawBridge, ht] at hs
      | source =>
        cases hf : x.factor with
        | inK k =>
            simp [pos04RawBridge, ht, hf] at hs
            subst s
            simp only [pos04RawBridge, pos04RawFutureUpdate, hf]
            cases k <;> cases a <;> rfl
        | p2w0 => simp [pos04RawBridge, ht, hf] at hs
        | p5w1 => simp [pos04RawBridge, ht, hf] at hs
    · intro s hs
      cases ht : x.tag with
      | source => simp [pos04RawBridge, ht] at hs
      | target =>
        cases hf : x.factor with
        | inK k =>
            simp [pos04RawBridge, ht, hf] at hs
            subst s
            simp only [pos04RawBridge, pos04RawFutureUpdate, hf]
            cases k <;> cases a <;> rfl
        | p2w0 => simp [pos04RawBridge, ht, hf] at hs
        | p5w1 => simp [pos04RawBridge, ht, hf] at hs

    · intro s hs ho
      cases ht : x.tag with
      | target => simp [pos04RawBridge, ht] at hs
      | source =>
        obtain ⟨t, _, hto⟩ := ho
        have hom : o ∈ coreRunOutcomes := by
          rw [← hto]
          exact core_run_outcome_mem .source t
        obtain ⟨u, hu, hrep, hc⟩ := core_run_representative .source o hom
        refine ⟨u, hu, ?_, hc⟩
        simp [pos04RawBridge, pos04RawFutureUpdate, ht, hrep]
    · intro s hs ho
      cases ht : x.tag with
      | source => simp [pos04RawBridge, ht] at hs
      | target =>
        obtain ⟨t, _, hto⟩ := ho
        have hom : o ∈ coreRunOutcomes := by
          rw [← hto]
          exact core_run_outcome_mem .target t
        obtain ⟨u, hu, hrep, hc⟩ := core_run_representative .target o hom
        refine ⟨u, hu, ?_, hc⟩
        simp [pos04RawBridge, pos04RawFutureUpdate, ht, hrep]


theorem pos04_source_future_sufficient :
    SourceFutureSufficient (pos04RawBridge .positive) := by
  apply source_future_sufficient_of_bisim
  intro s t h a u _
  change (match actions[a]? with
    | none => 0
    | some action => rowWeight (actionRow .source s action) u) =
    (match actions[a]? with
    | none => 0
    | some action => rowWeight (actionRow .source t action) u)
  cases ha : actions[a]? with
  | none => rfl
  | some action =>
      exact congrArg (fun row => rowWeight row u)
        (action_rows_equal_of_rawM s t action h)

/-- All four frozen histories are covered; repA/repB differ in their past
but have the same computed terminal M. The strict edge is p1w0→p2w1. -/
theorem pos04_bridge_admissible : BridgeAdmissible (pos04RawBridge .positive) := by
  unfold BridgeAdmissible
  refine ⟨by decide, ?_, ?_, ?_, by decide, ?_⟩
  · intro h _
    cases h <;> decide
  · refine ⟨.repA, by decide, .p1w0, .p2w1, ?_⟩
    decide
  · intro h _ x y
    cases h <;> cases x <;> cases y <;> decide
  · intro h _ s _
    cases s <;> decide

theorem pos04_strict_step_laws :
    BridgeStrictStepLaws (pos04RawBridge .positive) := by
  intro h _ i hi
  cases h <;>
    (have hi' : i = 0 ∨ i = 1 := by
      simp [pos04RawBridge, sourceHistory] at hi
      omega
     rcases hi' with rfl | rfl <;> decide)

theorem pos04_route_pair_domain :
    RoutePairDomain (pos04RawBridge .positive) .a .b := by
  simp [RoutePairDomain, pos04RawBridge, pos04RecordTransport,
    target_record_edges_eq, route_positive_steps, routeReadFromState,
    receiverFactor, receiverRaw, ambientPhase,
    route_positive_future_outputs, routes, routeOf,
    routeIds, sourceHistory, targetHistoryFor, routeRegister]
  exact ⟨.p1w0, by decide, by decide⟩

theorem pos04_route_comparison_nonempty :
    RouteComparisonNonempty (pos04RawBridge .positive) :=
  ⟨.a, .b, pos04_route_pair_domain⟩

theorem pos04_computed_route_status :
    routeStatusOfRaw (pos04RawBridge .positive) = .routeIndexed := by
  have hindexed : RouteIndexed (pos04RawBridge .positive) := by
    refine ⟨.a, .b, ?_, ?_, ?_⟩
    · exact pos04_route_pair_domain
    · decide
    · decide
  simp [routeStatusOfRaw, hindexed]

theorem pos04_computed_route_status_matches_assembly :
    routeStatusOfRaw (pos04RawBridge .positive) = routeStatusOf .positive := by
  rw [pos04_computed_route_status, route_status_positive]

/-- Deleting the comparison domain is a raw route intervention. It cannot
produce a flatness certificate or a route-indexed verdict. -/
def pos04NoRouteComparison : POS04RawBridge :=
  { pos04RawBridge .positive with routeIds := [] }

theorem no_route_comparison_is_unresolved :
    routeStatusOfRaw pos04NoRouteComparison = .unresolved := by
  have hnone : ¬ RouteIndexed pos04NoRouteComparison := by
    intro h
    obtain ⟨r, s, hdomain, _, _⟩ := h
    have hr := hdomain.1
    simp [pos04NoRouteComparison, pos04RawBridge] at hr
  simp [routeStatusOfRaw, hnone]

theorem pos04_bridge_raw_laws : BridgePrimitiveLaws (pos04RawBridge .positive) := by
  unfold BridgePrimitiveLaws
  refine ⟨?_, ?_, ?_, ?_, pos04_strict_step_laws,
    pos04_route_comparison_nonempty⟩
  · unfold BridgeCoreLaws
    refine ⟨?_, ?_, ?_, pos04_record_laws.1,
      pos04_record_laws.2, ?_⟩
    · intro s
      constructor
      · rfl
      constructor
      · cases s <;> decide
      constructor
      · cases s <;> decide
      constructor
      · cases s <;> decide
      · rfl
    · intro s t _
      rfl
    · intro h _
      cases h <;> decide
    · intro r _
      cases r <;> decide
  · intro s t h a u _
    change (match actions[a]? with
      | none => 0
      | some action => rowWeight (actionRow .source s action) u) =
      (match actions[a]? with
      | none => 0
      | some action => rowWeight (actionRow .source t action) u)
    cases ha : actions[a]? with
    | none => rfl
    | some action =>
        exact congrArg (fun row => rowWeight row u)
          (action_rows_equal_of_rawM s t action h)
  · constructor
    · rfl
    · intro s u a
      cases ha : actions[a]? with
      | none => rfl
      | some action => rfl
  · intro c d h
    exact h

/-- The two genuinely different past histories have one source predictive
class and, by the raw-map theorem, one target predictive class. -/
theorem pos04_representatives_nontrivial :
    sourceHistory .repA ≠ sourceHistory .repB ∧
    (sourceHistory .repA).take 2 ≠ (sourceHistory .repB).take 2 ∧
    Reachable (pos04RawBridge .positive) .repA ∧
    Reachable (pos04RawBridge .positive) .repB ∧
    SourceHistoryClass (pos04RawBridge .positive) .repA =
      SourceHistoryClass (pos04RawBridge .positive) .repB := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · simp [Reachable, pos04RawBridge, bridgeFrontier, historyIds]
  · simp [Reachable, pos04RawBridge, bridgeFrontier, historyIds]
  decide

theorem pos04_generic_bridge_instance :
    BridgeAdmissible (pos04RawBridge .positive) ∧
    BridgePrimitiveLaws (pos04RawBridge .positive) ∧
    RepresentativeIndependent (Reachable (pos04RawBridge .positive))
      (SourceHistoryClass (pos04RawBridge .positive))
      (TargetHistoryClass (pos04RawBridge .positive)) ∧
    (∀ h, Reachable (pos04RawBridge .positive) h →
      TemporalSignatureAgreementAt (pos04RawBridge .positive) h ∧
      StrictSuccessorPreserved (pos04RawBridge .positive) h) ∧
    StrictRecordArrowPreserved (pos04RawBridge .positive) ∧
    RouteStatusPreserved (pos04RawBridge .positive) ∧
    TargetFutureSufficientOnImage (pos04RawBridge .positive) ∧
    (∀ h, Reachable (pos04RawBridge .positive) h →
      StrictOrderTickProgressAt (pos04RawBridge .positive) h) := by
  exact ⟨pos04_bridge_admissible, pos04_bridge_raw_laws,
    bundledHeterogeneousTemporalTransport_generic
      (pos04RawBridge .positive) pos04_bridge_admissible pos04_bridge_raw_laws⟩

/-- The declared NEG-BRIDGE-REP receiver changes only the target terminal
representative for repB. It breaks raw class factoring under the same test. -/
theorem neg_bridge_rep_not_admissible :
    ¬ BridgeAdmissible (pos04RawBridge .bridgeRep) := by
  intro h
  have heq := (h.2.1 .repB (by decide)).2
  have hneq : targetHistoryFor .bridgeRep .repB ≠ sourceHistory .repB := by
    decide
  exact hneq (by simpa [pos04RawBridge] using heq)

theorem neg_bridge_rep_not_representative_independent :
    ¬ RepresentativeIndependent (Reachable (pos04RawBridge .bridgeRep))
      (SourceHistoryClass (pos04RawBridge .bridgeRep))
      (TargetHistoryClass (pos04RawBridge .bridgeRep)) := by
  intro h
  have hp := h .repA .repB
    (by simp [Reachable, pos04RawBridge, bridgeFrontier, historyIds])
    (by simp [Reachable, pos04RawBridge, bridgeFrontier, historyIds])
    (by decide)
  have hneq :
      TargetHistoryClass (pos04RawBridge .bridgeRep) .repA ≠
        TargetHistoryClass (pos04RawBridge .bridgeRep) .repB := by decide
  exact hneq hp

end CSTTT.POS04
