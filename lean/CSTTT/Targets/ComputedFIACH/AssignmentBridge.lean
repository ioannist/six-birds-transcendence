import CSTTT.Targets.ComputedFIACH.ExactAutonomyTransport

/-! G6_lane_spec.md:104–145. One RawBridge constructed from the shared staged
assignment. Every factor, event, route and run field is derived; no positive
adapter, signature or dynamics candidate is supplied. This module establishes
factor primitive laws; the full run-coherence/codec adapter is a separate gate. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory CSTTT.RecordTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192
instance : AuditEnum EventId := ⟨eventIds,by intro e; cases e <;> decide⟩

/-- Exact equality membership; PredictiveNow's derived BEq has no exported
LawfulBEq instance, so use a checked equality-based finite decision. -/
instance predictiveMembershipDecision (o : CSTTT.POS04.PredictiveNow)
    (xs : List CSTTT.POS04.PredictiveNow) : Decidable (o ∈ xs) :=
  decidable_of_iff ((xs.any fun v => decide (v = o)) = true) ⟨by
    intro h
    obtain ⟨v,hv,he⟩ := List.any_eq_true.mp h
    exact (of_decide_eq_true he) ▸ hv,
    by intro h; exact List.any_eq_true.mpr ⟨o,h,by simp⟩⟩

abbrev AcquisitionRun := Tag × Run6

def assignedFactorStep (a : Assignment) (t : Tag) (s u : KState) : Nat :=
  let d := runInputs6 a t
  rowWeight (d.base.base.rows s (d.base.base.policy s)) u

def assignedActionStep (a : Assignment) (t : Tag) (s : KState) (i : Nat) (u : KState) : Nat :=
  match actions[i]? with
  | none => 0
  | some act => rowWeight ((runInputs6 a t).base.base.rows s act) u

def assignedPrefixProgress (a : Assignment) (t : Tag) (path : List KState) (i : Nat) : Nat :=
  let p := path.take (i+1)
  ((p.zip (p.drop 1)).filter (fun pair => assignedFactorStep a t pair.1 pair.2 > 0)).length

def assignedRouteHistory (a : Assignment) (r : RouteId) : HistoryId :=
  ((runInputs6 a .source).base.routes.find? (fun v => v.id == r)).map Route.sourceHistory |>.getD .repA

def assignedRecordRank (a : Assignment) (e : EventId) : Nat :=
  ((event6 (runInputs6 a .target) e).map (fun v => stages.idxOf v.toStage)).getD 0

def assignedRecordEdges (a : Assignment) (t : Tag) : List (EventId × EventId) :=
  let d := runInputs6 a t
  eventIds.flatMap fun i => eventIds.filterMap fun j =>
    match event6 d i,event6 d j with
    | some e,some f =>
      let support := match t with
        | .source => e.sourceSupport && f.sourceSupport
        | .target => e.targetSupport && f.targetSupport
      if decide (e.toStage = f.fromStage) && support &&
          routeIds.all (d.base.writers t) && strictEvent6 d e && strictEvent6 d f
      then some (i,j) else none
    | _,_ => none

def assignedRecordTransport (a : Assignment) : RawRecordTransport EventId EventId :=
  ⟨assignedRecordEdges a .source,assignedRecordEdges a .target,id,
    assignedRecordRank a,assignedRecordRank a,id,
    fun i j => assignedRecordRank a j - assignedRecordRank a i⟩

def assignmentRawBridge (m : RawLaneModel) : POS04RawBridge where
  frontier := routeIds.map (assignedRouteHistory (image m.assignment))
  sourceHistory := (runInputs6 (image m.assignment) .source).base.histories
  targetHistory := acquisitionTargetHistory (image m.assignment)
  mapState := id
  sourceCoord := (runInputs6 (image m.assignment) .source).base.base.positions
  targetCoord := (runInputs6 (image m.assignment) .target).base.base.positions
  mapCoord := id
  sourceClass := predictive (runInputs6 (image m.assignment) .source).base.base
  targetClass := predictive (runInputs6 (image m.assignment) .target).base.base
  mapClass := id
  sourceStates := kernel
  targetStates := kernel
  sourceClassDecEq := inferInstance
  targetClassDecEq := inferInstance
  sourceActionStep := assignedActionStep (image m.assignment) .source
  targetActionStep := assignedActionStep (image m.assignment) .target
  sourceStep := assignedFactorStep (image m.assignment) .source
  targetStep := assignedFactorStep (image m.assignment) .target
  sourceOrder := fun h => List.range ((runInputs6 (image m.assignment) .source).base.histories h).length
  targetOrder := fun h => List.range (acquisitionTargetHistory (image m.assignment) h).length
  sourceTick := fun s => let d := runInputs6 (image m.assignment) .source; d.ticks s (d.base.base.policy s)
  targetTick := fun s => let d := runInputs6 (image m.assignment) .target; d.ticks s (d.base.base.policy s)
  sourceProgress := fun h => assignedPrefixProgress (image m.assignment) .source
    ((runInputs6 (image m.assignment) .source).base.histories h)
    ((runInputs6 (image m.assignment) .source).base.histories h).length
  targetProgress := fun h => assignedPrefixProgress (image m.assignment) .target
    (acquisitionTargetHistory (image m.assignment) h) (acquisitionTargetHistory (image m.assignment) h).length
  sourceProgressAt := fun h => assignedPrefixProgress (image m.assignment) .source
    ((runInputs6 (image m.assignment) .source).base.histories h)
  targetProgressAt := fun h => assignedPrefixProgress (image m.assignment) .target
    (acquisitionTargetHistory (image m.assignment) h)
  record := assignedRecordTransport (image m.assignment)
  routeIds := routeIds
  routeHistory := assignedRouteHistory (image m.assignment)
  sourceRoute := fun r => ((routeTuple (runInputs6 (image m.assignment) .source).base r).getD ([],[])).2
  targetRoute := fun r => ((routeTuple (runInputs6 (image m.assignment) .target).base r).getD ([],[])).2
  sourceResidue := fun r => (routeTuple (runInputs6 (image m.assignment) .source).base r).getD ([],[])
  targetResidue := fun r => (routeTuple (runInputs6 (image m.assignment) .target).base r).getD ([],[])
  sourceReadout := acquisitionRouteOutput m
  targetReadout := acquisitionRouteOutput m
  targetRouteSteps := fun r => (phase2Entries m r).filterMap fun e =>
    (acquisitionRouteRead e).map (e.register,·)
  sourceMaintenance := fun _ => available8 (clause8 (image m.assignment) .source) .source
  targetMaintenance := fun _ => available8 (clause8 (image m.assignment) .target) .target
  mapMaintenance := id
  sourceOwner := fun _ => tagCarrierId (runInputs6 (image m.assignment) .source).resource.owner
  targetOwner := fun _ => tagCarrierId (runInputs6 (image m.assignment) .target).resource.owner
  targetId := tagCarrierId .target
  RunState := AcquisitionRun
  RunAction := Action
  RunOutcome  := CSTTT.POS04.PredictiveNow
  runOutcomeDecEq := inferInstance
  runOutcomes := outcomes6 (runInputs6 (image m.assignment) .source) ++
    (outcomes6 (runInputs6 (image m.assignment) .target)).filter (fun o =>
      decide (o ∉ outcomes6 (runInputs6 (image m.assignment) .source)))
  runDenominator := 4
  runNumerator := fun x act o => let d := runInputs6 (image m.assignment) x.1
    if enabled6 d x.2 then mass6 d x.2.factor act o else 0
  runUpdate := fun x act o => (x.1,update6 (runInputs6 (image m.assignment) x.1) x.2 act o)
  runSourceFactor := fun x => if x.1 = .source then
    match x.2.factor with | .inK s => some s | _ => none else none
  runTargetFactor := fun x => if x.1 = .target then
    match x.2.factor with | .inK s => some s | _ => none else none
  runSourceOutcome := fun s => predictive6 (runInputs6 (image m.assignment) .source) (.inK s)
  runTargetOutcome := fun s => predictive6 (runInputs6 (image m.assignment) .target) (.inK s)
  runActionIndex := actions.idxOf
  runEnabled := fun x => enabled6 (runInputs6 (image m.assignment) x.1) x.2
  runCounter := fun x => x.2.counter
  runTicks := fun x => x.2.ticks
  RunPredictive  := CSTTT.POS04.PredictiveNow
  runPredictiveDecEq := inferInstance
  residueDecEq := inferInstance
  maintenanceDecEq := inferInstance
  runPredictive := fun x => predictive6 (runInputs6 (image m.assignment) x.1) x.2.factor
  sourcePredictiveMap  := CSTTT.POS04.PredictiveNow.active
  targetPredictiveMap  := CSTTT.POS04.PredictiveNow.active
  runProgress := fun x => x.2.counter
  runRecordWriter := fun x => writer6 (runInputs6 (image m.assignment) x.1) x.1 x.2.residue
  runResidue := fun x => x.2.residue
  runMaintenance := fun x => x.2.funded
  runOwner := fun x => tagCarrierId (runInputs6 (image m.assignment) x.1).resource.owner
  runRecord := fun x => (observation6 (runInputs6 (image m.assignment) x.1) x.1 x.2).endogenousRecordCount
  runSourceFactorUpdate := fun x act o => if x.1 = .source then
    match (update6 (runInputs6 (image m.assignment) x.1) x.2 act o).factor with
    | .inK s => some s | _ => none else none
  runTargetFactorUpdate := fun x act o => if x.1 = .target then
    match (update6 (runInputs6 (image m.assignment) x.1) x.2 act o).factor with
    | .inK s => some s | _ => none else none
  runPredictiveUpdate := fun x act o => predictive6 (runInputs6 (image m.assignment) x.1)
    (update6 (runInputs6 (image m.assignment) x.1) x.2 act o).factor
  runTickAdvance := fun x act _ => delta6 (runInputs6 (image m.assignment) x.1) x.2.factor act
  runProgressAdvance := fun _ _ _ => 1
  runWriterRule := fun residue owner => let t := if owner = tagCarrierId .source then Tag.source else Tag.target
    writer6 (runInputs6 (image m.assignment) t) t residue
  runResidueUpdate := fun residue _ _ => residue
  runMaintenanceUpdate := fun funded _ _ => funded && decide
    (budgetAfter6 (runInputs6 (image m.assignment) .source) > 0)
  runOwnerUpdate := fun owner _ _ => owner
  runEnabledRule := fun funded owner => let t := if owner = tagCarrierId .source then Tag.source else Tag.target
    let d := runInputs6 (image m.assignment) t
    funded && d.resource.rechargeAvailable && decide (budget6 d ≥ d.ledger.actionCost)
  runTickPeriod := 2
  AuditIndex := SnapshotIndex
  auditFrontier := acquisitionSnapshotIndices
  auditHistory := fun i => assignedRouteHistory (image m.assignment) i.1
  auditState := fun i => (acquisitionHistory (image m.assignment) .source i.1).getD (snapshotOccurrence i.2) .p0w0
  auditOccurrence := fun i => snapshotOccurrence i.2
  auditEvent := fun i => snapshotEvent i.2
  auditRoute := Prod.fst
  makeSourceRun := fun s count ticks residue funded => (.source,⟨.inK s,count,ticks,residue,funded⟩)
  makeTargetRun := fun s count ticks residue funded => (.target,⟨.inK s,count,ticks,residue,funded⟩)

/-- Exact step/observer equations for the bridge's owned run fields. -/
theorem assignment_bridge_update (m : RawLaneModel) (t : Tag) (x : Run6) (act : Action) (o : CSTTT.POS04.PredictiveNow) :
    (assignmentRawBridge m).runUpdate (t,x) act o =
      (t,update6 (runInputs6 (image m.assignment) t) x act o) := rfl

theorem assignment_bridge_observation (m : RawLaneModel) (t : Tag) (x : Run6) :
    bridgeRunObservation (assignmentRawBridge m) (t,x) =
      frozenObservation6 ((future6 (image m.assignment) t).observe x) := rfl

/-- Finite action checks use the actual raw rows; the unbounded natural action
index in RawBridge maps out-of-domain indices to a zero row on both sides. -/
def FiniteActionBisim (m : RawLaneModel) : Prop :=
  let ds := runInputs6 (image m.assignment) .source
  ∀ s t : KState, predictive ds.base.base s = predictive ds.base.base t →
    ∀ act : Action, ∀ u : KState, rowWeight (ds.base.base.rows s act) u =
      rowWeight (ds.base.base.rows t act) u

def FiniteActionMap (m : RawLaneModel) : Prop :=
  ∀ s u : KState, ∀ act : Action,
    rowWeight ((runInputs6 (image m.assignment) .target).base.base.rows s act) u =
    rowWeight ((runInputs6 (image m.assignment) .source).base.base.rows s act) u

def FiniteStrictSteps (m : RawLaneModel) : Prop :=
  let b := assignmentRawBridge m
  ∀ h : HistoryId, h ∈ b.frontier → ∀ i : Fin (b.sourceHistory h).length,
    i.val + 1 < (b.sourceHistory h).length →
      (b.sourceOrder h).getD (i.val+1) 0 = (b.sourceOrder h).getD i.val 0 + 1 ∧
      b.sourceProgressAt h (i.val+1) = b.sourceProgressAt h i.val + 1 ∧
      b.targetProgressAt h i.val = b.sourceProgressAt h i.val ∧
      b.targetProgressAt h (i.val+1) = b.sourceProgressAt h (i.val+1) ∧
      ∃ x : KState, (b.sourceHistory h)[i.val]? = some x ∧ 0 < b.sourceTick x

instance (m : RawLaneModel) : Decidable (FiniteActionBisim m) := by
  unfold FiniteActionBisim; infer_instance
instance (m : RawLaneModel) : Decidable (FiniteActionMap m) := by
  unfold FiniteActionMap; infer_instance
instance (m : RawLaneModel) : Decidable (FiniteStrictSteps m) := by
  unfold FiniteStrictSteps; infer_instance
instance (m : RawLaneModel) : Decidable (BridgeAdmissible (assignmentRawBridge m)) := by
  unfold BridgeAdmissible
  dsimp only [assignmentRawBridge]
  infer_instance
instance (m : RawLaneModel) : Decidable (BridgeCoreLaws (assignmentRawBridge m)) := by
  unfold BridgeCoreLaws RecordMapStepLaw PositiveRecordIncrement SourceArrow
  dsimp only [assignmentRawBridge]
  infer_instance
instance (m : RawLaneModel) : Decidable (RouteComparisonNonempty (assignmentRawBridge m)) := by
  unfold RouteComparisonNonempty RoutePairDomain
  dsimp only [assignmentRawBridge]
  infer_instance

/-- Completeness rejects before any default lookup can enter the certificate.
All other inputs here are independently computed map/table equations. -/
def acquisitionFactorBridgeCheck (m : RawLaneModel) : Bool :=
  match checkedAcquisition m with
  | none => false
  | some _ => decide (BridgeAdmissible (assignmentRawBridge m) ∧
      BridgeCoreLaws (assignmentRawBridge m) ∧ FiniteActionBisim m ∧
      FiniteActionMap m ∧ FiniteStrictSteps m ∧
      RouteComparisonNonempty (assignmentRawBridge m))

def AcquisitionFactorBridgePass (m : RawLaneModel) := acquisitionFactorBridgeCheck m = true

theorem finite_action_bisim_raw (m : RawLaneModel) (h : FiniteActionBisim m) :
    SourceActionBisim (assignmentRawBridge m) := by
  intro s t hc i u _
  change assignedActionStep (image m.assignment) .source s i u =
    assignedActionStep (image m.assignment) .source t i u
  unfold assignedActionStep
  cases he : actions[i]? with
  | none => rfl
  | some act => exact h s t hc act u

theorem finite_action_map_raw (m : RawLaneModel) (h : FiniteActionMap m) :
    FutureMapLaws (assignmentRawBridge m) := by
  refine ⟨by simp [assignmentRawBridge],?_⟩
  intro s u i
  change assignedActionStep (image m.assignment) .target s i u =
    assignedActionStep (image m.assignment) .source s i u
  unfold assignedActionStep
  cases he : actions[i]? with
  | none => rfl
  | some act => exact h s u act

theorem finite_strict_steps_raw (m : RawLaneModel) (h : FiniteStrictSteps m) :
    BridgeStrictStepLaws (assignmentRawBridge m) := by
  intro hist hh i hi
  exact h hist hh ⟨i,by omega⟩ hi

theorem acquisition_factor_bridge_laws (m : RawLaneModel) (h : AcquisitionFactorBridgePass m) :
    BridgeAdmissible (assignmentRawBridge m) ∧ BridgePrimitiveLaws (assignmentRawBridge m) := by
  unfold AcquisitionFactorBridgePass acquisitionFactorBridgeCheck at h
  split at h
  · contradiction
  · have hp : BridgeAdmissible (assignmentRawBridge m) ∧
        BridgeCoreLaws (assignmentRawBridge m) ∧ FiniteActionBisim m ∧
        FiniteActionMap m ∧ FiniteStrictSteps m ∧
        RouteComparisonNonempty (assignmentRawBridge m) := of_decide_eq_true h
    exact ⟨hp.1,hp.2.1,finite_action_bisim_raw m hp.2.2.1,
      finite_action_map_raw m hp.2.2.2.1,fun _ _ he => he,
      finite_strict_steps_raw m hp.2.2.2.2.1,hp.2.2.2.2.2⟩

theorem acquisition_factor_bridge_transport (m : RawLaneModel) (h : AcquisitionFactorBridgePass m) :
    RepresentativeIndependent (Reachable (assignmentRawBridge m))
      (SourceHistoryClass (assignmentRawBridge m)) (TargetHistoryClass (assignmentRawBridge m)) ∧
    (∀ hist, Reachable (assignmentRawBridge m) hist →
      TemporalSignatureAgreementAt (assignmentRawBridge m) hist ∧
      StrictSuccessorPreserved (assignmentRawBridge m) hist) ∧
    StrictRecordArrowPreserved (assignmentRawBridge m) ∧
    RouteStatusPreserved (assignmentRawBridge m) ∧
    TargetFutureSufficientOnImage (assignmentRawBridge m) ∧
    (∀ hist, Reachable (assignmentRawBridge m) hist →
      StrictOrderTickProgressAt (assignmentRawBridge m) hist) := by
  obtain ⟨ha,hp⟩ := acquisition_factor_bridge_laws m h
  exact bundledHeterogeneousTemporalTransport_generic _ ha hp

theorem acquisition_factor_bridge_missing_dependency (m : RawLaneModel) (k : Cell)
    (hk : k ∈ acquisitionDependencies) :
    ¬ AcquisitionFactorBridgePass {m with assignment := put m.assignment (swapCell k) none} := by
  simp [AcquisitionFactorBridgePass,acquisitionFactorBridgeCheck,acquisition_missing_dependency m k hk]

theorem baseline_factor_bridge : AcquisitionFactorBridgePass baseline := by
  unfold AcquisitionFactorBridgePass acquisitionFactorBridgeCheck
  rw [baseline_acquisition]
  decide +kernel

theorem package_deletion_factor_bridge : AcquisitionFactorBridgePass packageDeletion := by
  unfold AcquisitionFactorBridgePass acquisitionFactorBridgeCheck
  rw [package_deletion_acquisition]
  decide +kernel

theorem lineage_deletion_factor_bridge : AcquisitionFactorBridgePass lineageDeletion := by
  unfold AcquisitionFactorBridgePass acquisitionFactorBridgeCheck
  have hc : checkedAcquisition lineageDeletion = some (image lineageDeletion.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image lineageDeletion.assignment) := by decide
    simp [h]
  rw [hc]
  decide +kernel

theorem withdrawal_deletion_factor_bridge : AcquisitionFactorBridgePass withdrawalDeletion := by
  unfold AcquisitionFactorBridgePass acquisitionFactorBridgeCheck
  rw [withdrawal_deletion_acquisition]
  decide +kernel

theorem reversed_histories_factor_bridge : AcquisitionFactorBridgePass reversedHistories := by
  unfold AcquisitionFactorBridgePass acquisitionFactorBridgeCheck
  have hc : checkedAcquisition reversedHistories = some (image reversedHistories.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image reversedHistories.assignment) := by decide
    simp [h]
  rw [hc]
  decide +kernel

end CSTTT.TargetTheory.ComputedFIACH
