import CSTTT.Targets.GenericHandoff.AcquisitionEndpoint
import CSTTT.Targets.GenericHandoff.POS04TemporalEquivalence
import CSTTT.Targets.GenericHandoff.POS04ExecutionFrontier

/-! Exact endpoint extraction on every partial POS-04 assignment. Missing
inputs reject before any fixed-table decoder can totalize a value. The raw
coordinate receiver is deliberately near-automatic, as in the declaration.
This is an endpoint seam, not the final cross-component RawHandoff theorem. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04AcquisitionEndpoint
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def eventMap (e : CSTTT.POS04.Event) : AcquisitionEndpoint.SupportedEvent CSTTT.POS04.Stage EventId :=
  ⟨e.id,e.fromStage,e.toStage,e.atomic,e.strictStep,e.sourceSupport,e.targetSupport⟩
def cfg : AcquisitionEndpoint.Schema KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag :=
  ⟨POS04TemporalFactor.schema .source,POS04TemporalFactor.schema .target,
    .sourceLive,.targetExit,.exit,.p0w0,4,id⟩
def bindings : AcquisitionEndpoint.Bindings Cell Value KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag :=
  ⟨POS04TemporalFactor.bindings .source,POS04TemporalFactor.bindings .target,
    ⟨.eventTable,fun es => es.map eventMap⟩,POS04ExecutionFrontier.receiverView⟩
def data (a : CSTTT.POS04.Assigned.Assignment) :
    AcquisitionEndpoint.Data KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag :=
  ⟨POS04TemporalFactor.raw (runInputs6 a .source) .source,
    POS04TemporalFactor.raw (runInputs6 a .target) .target,
    ((runInputs6 a .target).base.events).map eventMap,
    ⟨(runInputs6 a .target).base.receiver.sourcePresent,
      (runInputs6 a .target).base.receiver.targetReceiverFunded,
      (runInputs6 a .target).base.receiver.funded,
      (runInputs6 a .target).base.receiver.mixedEventRequired⟩⟩

theorem scope_iff (k : Cell) : k ∈ bindings.scope ↔ k ∈ acquisitionDependencies := by
  cases k
  all_goals try (rename_i t; cases t)
  all_goals decide

theorem decoded_eq (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete acquisitionDependencies a) : AcquisitionEndpoint.decoded bindings a = some (data a) := by
  have hs := POS04TemporalFactor.decoded_complete a .source
    (fun k hk => hc k (List.mem_append_left _ (List.mem_append_right _ hk)))
  have ht := POS04TemporalFactor.decoded_complete a .target
    (fun k hk => hc k (List.mem_append_right _ hk))
  have he := POS04RegisterDynamics.cell_value (hc .eventTable (by simp [acquisitionDependencies,phase2Dependencies]))
  have hr := POS04RegisterDynamics.cell_value (hc .receiverInput (by simp [acquisitionDependencies,phase2Dependencies]))
  simp only [AcquisitionEndpoint.decoded,bindings,hs,ht,CellView.read,POS04ExecutionFrontier.receiverView]
  rw [he,hr]
  rfl

theorem tuple_eq (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (r : RouteId) :
    AcquisitionEndpoint.tuple (POS04TemporalFactor.raw (runInputs6 a t) t) r =
      routeTuple (runInputs6 a t).base r := by
  simp only [AcquisitionEndpoint.tuple,POS04TemporalFactor.route_eq,routeTuple,Option.map_map]
  rfl

theorem event_eq (a : CSTTT.POS04.Assigned.Assignment) (eid : EventId) :
    AcquisitionEndpoint.event (data a) eid = (event6 (runInputs6 a .target) eid).map eventMap := by
  simp only [AcquisitionEndpoint.event,data,List.find?_map,Function.comp_def,eventMap,event6]

theorem active_eq (a : CSTTT.POS04.Assigned.Assignment) :
    AcquisitionEndpoint.active cfg (data a) = active7 (runInputs6 a .target).base := by
  simp only [AcquisitionEndpoint.active,AcquisitionEndpoint.mixed,cfg,data,active7,mixed7,
    List.any_map,Function.comp_def,eventMap]
  simp only [bne,Bool.beq_eq_decide_eq,decide_not]
  rfl

theorem supported_eq (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (hist : List KState) :
    AcquisitionEndpoint.supported (POS04TemporalFactor.schema t)
      (POS04TemporalFactor.raw (runInputs6 a t) t) hist = pathSupported (runInputs6 a t).base hist := by
  simp only [AcquisitionEndpoint.supported,pathSupported,POS04TemporalFactor.policy_weight_eq]

theorem strict_eq (a : CSTTT.POS04.Assigned.Assignment) (e : CSTTT.POS04.Event) :
    AcquisitionEndpoint.strict cfg (data a) (eventMap e) = strictEvent6 (runInputs6 a .target) e := rfl

theorem path_eq (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId) :
    AcquisitionEndpoint.path cfg (data a) r = path6 (runInputs6 a .target) r := by
  simp only [AcquisitionEndpoint.path,show (data a).target = POS04TemporalFactor.raw (runInputs6 a .target) .target from rfl,tuple_eq,show cfg.target = POS04TemporalFactor.schema .target from rfl,supported_eq,path6]
  cases hr : routeTuple (runInputs6 a .target).base r with
  | none => rfl
  | some v =>
    rcases v with ⟨hist,ids⟩
    simp only [event_eq,Option.any_map,strict_eq]
    congr 1
    apply List.all_congr
    · rfl
    · intro p
      cases he : event6 (runInputs6 a .target) p.1 <;>
        cases hf : event6 (runInputs6 a .target) p.2 <;> rfl

theorem available_eq (a : CSTTT.POS04.Assigned.Assignment) :
    AcquisitionEndpoint.available cfg (data a) = available8 (clause8 a .target) .target := by
  rfl

theorem phase2_eq (m : RawLaneModel)
    (hc : Complete acquisitionDependencies (image m.assignment)) (r : RouteId) :
    AcquisitionEndpoint.phase2 cfg (data (image m.assignment)) r = phase2Check m r := by
  have hp : phase2Complete m = true := by
    apply decide_eq_true
    exact fun k hk => hc k (List.mem_append_left _ (List.mem_append_left _ hk))
  unfold AcquisitionEndpoint.phase2
  rw [active_eq,path_eq]
  change _ = phase2Check m r
  simp only [phase2Check,hp,Bool.not_true,Bool.false_eq_true,if_false,arrivalInputs]
  simp only [show (data (image m.assignment)).target = POS04TemporalFactor.raw (runInputs6 (image m.assignment) .target) .target from rfl,
    show (data (image m.assignment)).source = POS04TemporalFactor.raw (runInputs6 (image m.assignment) .source) .source from rfl,
    tuple_eq,show cfg.source = POS04TemporalFactor.schema .source from rfl,supported_eq]
  cases hr : routeTuple (runInputs6 (image m.assignment) .target).base r with
  | none => rfl
  | some v =>
    rcases v with ⟨hist,ids⟩
    simp only [event_eq]
    cases hh : ids.head? <;> cases hl : ids.getLast?
    all_goals try simp only [Bool.and_false]; try rfl
    rename_i first last
    cases hf : event6 (runInputs6 (image m.assignment) .target) first <;>
      cases he : event6 (runInputs6 (image m.assignment) .target) last
    all_goals rfl

theorem received_eq (a : CSTTT.POS04.Assigned.Assignment) (h : HistoryId) :
    AcquisitionEndpoint.received cfg (data a) h = acquisitionReceiver a h := by
  unfold AcquisitionEndpoint.received acquisitionReceiver
  rw [active_eq]
  cases he : (runInputs6 a .target).base.receiver.contentRule <;>
    simp [cfg,data,POS04TemporalFactor.raw]

theorem target_history_eq (a : CSTTT.POS04.Assigned.Assignment) (h : HistoryId) :
    AcquisitionEndpoint.targetHistory cfg (data a) h = acquisitionTargetHistory a h := by
  unfold AcquisitionEndpoint.targetHistory acquisitionTargetHistory
  rw [received_eq]
  cases he : acquisitionReceiver a h <;> rfl

/-- These three equalities follow from the leg constructor itself. No
precomputed endpoint or independent positive-leg adapter enters extraction. -/
theorem constructed_atomic_endpoint (m : RawLaneModel) (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId) :
    (acquisitionAtomicLeg m a r).target = atomicCarrierCode .target ∧
    (acquisitionAtomicLeg m a r).source = atomicCarrierCode .source ∧
    (acquisitionAtomicLeg m a r).stages.getLast?.map (fun v => v.frontier.predictive) =
      some (acquisitionClass a r) := by
  exact ⟨rfl,rfl,rfl⟩

theorem at_route_eq (m : RawLaneModel)
    (hc : Complete acquisitionDependencies (image m.assignment)) (r : RouteId) :
    AcquisitionEndpoint.atRoute cfg (data (image m.assignment)) r =
      typedAcquisitionEndpointAt m (image m.assignment) r := by
  unfold AcquisitionEndpoint.atRoute
  simp only [show (data (image m.assignment)).source =
      POS04TemporalFactor.raw (runInputs6 (image m.assignment) .source) .source from rfl,
    show (data (image m.assignment)).target =
      POS04TemporalFactor.raw (runInputs6 (image m.assignment) .target) .target from rfl,
    tuple_eq,POS04TemporalFactor.route_eq,active_eq,phase2_eq m hc,received_eq,target_history_eq]
  unfold typedAcquisitionEndpointAt
  simp only [(constructed_atomic_endpoint m (image m.assignment) r).1,
    (constructed_atomic_endpoint m (image m.assignment) r).2.1,
    (constructed_atomic_endpoint m (image m.assignment) r).2.2,decide_true,Bool.and_true]
  cases hs : (runInputs6 (image m.assignment) .source).base.routes.find? (fun v => v.id == r) with
  | none => simp [routeTuple,hs]
  | some route =>
    simp only [routeTuple,hs,Option.map_some,POS04TemporalFactor.routeMap,assignedRouteHistory,
      Option.getD_some]
    cases ht : (runInputs6 (image m.assignment) .target).base.routes.find? (fun v => v.id == r) with
    | none => rfl
    | some target =>
      simp only [Option.map_some]
      cases hh : ((runInputs6 (image m.assignment) .source).base.histories route.sourceHistory).getLast? <;>
        cases hp : route.eventPath.getLast?
      all_goals try rfl
      rename_i state eid
      dsimp only
      rw [event_eq]
      cases he : event6 (runInputs6 (image m.assignment) .target) eid
      · rfl
      · simp only [Option.map_some,strict_eq]
        rfl

theorem decoded_complete_iff (a : CSTTT.POS04.Assigned.Assignment) :
    (∃ d, AcquisitionEndpoint.decoded bindings a = some d) ↔ Complete acquisitionDependencies a := by
  constructor
  · rintro ⟨d,hd⟩ k hk
    cases he : a k with
    | some v => rfl
    | none =>
      rw [AcquisitionEndpoint.missing_input bindings a k ((scope_iff k).mpr hk) he] at hd
      contradiction
  · intro hc
    exact ⟨_,decoded_eq a hc⟩

/-- Exact biconditional on EVERY partial assignment, including missing inputs. -/
theorem pass_iff (m : RawLaneModel) :
    AcquisitionEndpoint.Pass cfg bindings (image m.assignment) ↔ TypedAcquisitionEndpointPass m := by
  by_cases hc : Complete acquisitionDependencies (image m.assignment)
  · change CSTTT.POS04.Assigned.Complete acquisitionDependencies (image m.assignment) at hc
    have he : checkedAcquisition m = some (image m.assignment) := by
      simp [checkedAcquisition,hc]
    simp only [TypedAcquisitionEndpointPass,typedAcquisitionEndpointCheck,he]
    constructor
    · rintro ⟨d,hd,_,hall⟩
      have hd' := Option.some.inj (hd.symm.trans (decoded_eq _ hc))
      subst d
      apply List.all_eq_true.mpr
      intro r hr
      rw [← at_route_eq m hc]
      exact List.all_eq_true.mp hall r hr
    · intro hall
      refine ⟨_,decoded_eq _ hc,by decide,List.all_eq_true.mpr ?_⟩
      intro r hr
      rw [at_route_eq m hc]
      exact List.all_eq_true.mp hall r hr
  · change ¬ CSTTT.POS04.Assigned.Complete acquisitionDependencies (image m.assignment) at hc
    have he : checkedAcquisition m = none := by simp [checkedAcquisition,hc]
    simp only [TypedAcquisitionEndpointPass,typedAcquisitionEndpointCheck,he,Bool.false_eq_true,iff_false]
    rintro ⟨d,hd,_⟩
    exact hc ((decoded_complete_iff _).mp ⟨d,hd⟩)

def interface : AcquisitionEndpoint.Interface Cell Value where
  State := KState
  Action := CSTTT.Objecthood.T1Audit.Action
  Outcome := Ambient
  History := HistoryId
  Route := RouteId
  Stage := CSTTT.POS04.Stage
  Id := EventId
  Owner := Tag
  stateEq := inferInstance
  outcomeEq := inferInstance
  routeEq := inferInstance
  stageEq := inferInstance
  idEq := inferInstance
  ownerEq := inferInstance
  schema := cfg
  bindings := bindings

theorem readout_iff (m : RawLaneModel) :
    AcquisitionEndpoint.Readout interface (image m.assignment) ↔ TypedAcquisitionEndpointPass m :=
  pass_iff m

theorem positive : AcquisitionEndpoint.Readout interface canonical := by
  have h := (readout_iff baseline).mpr (lineage_checked_parts _ baseline_lineage_lane).2.2
  simpa only [show baseline.assignment = canonical from rfl,image_canonical] using h

/-- Every consumed cell is guarded, including the actual terminal event cell. -/
theorem missing_endpoint_rejected (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ acquisitionDependencies) :
    ¬ AcquisitionEndpoint.Readout interface (put a k none) :=
  AcquisitionEndpoint.missing_no_readout _ _ _ ((scope_iff k).mpr hk) (put_same _ _ _)

theorem endpoint_deletion_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ AcquisitionEndpoint.Readout interface (put a .eventTable none) :=
  missing_endpoint_rejected a .eventTable (by simp [acquisitionDependencies,phase2Dependencies])

/-- A raw constant coordinate operation loses the received terminal. -/
def constantReceiver : AcquisitionEndpoint.Interface Cell Value :=
  {interface with schema := {cfg with transfer := fun _ => .p0w0}}

theorem constant_receiver_rejected : ¬ AcquisitionEndpoint.Readout constantReceiver canonical := by
  change ¬ AcquisitionEndpoint.Pass {cfg with transfer := fun _ => .p0w0} bindings canonical
  rintro ⟨d,hd,_,hall⟩
  have he := Option.some.inj (hd.symm.trans (decoded_eq canonical (canonical_complete _)))
  subst d
  have ha := List.all_eq_true.mp hall RouteId.a (by decide)
  exact (show AcquisitionEndpoint.atRoute {cfg with transfer := fun _ => .p0w0} (data canonical) RouteId.a ≠ true
    from by decide +kernel) ha

/-- Delete only the referenced exit record; all primitive cells stay present. -/
def deleteExit : CSTTT.POS04.Assigned.Assignment :=
  mapCell canonical .eventTable (fun es => es.filter (fun e => e.id != .exit))

theorem exit_deleted_complete : Complete acquisitionDependencies deleteExit := by
  intro k _
  cases k
  all_goals try (rename_i t; cases t)
  all_goals rfl

theorem exit_deleted_no_endpoint : ¬ AcquisitionEndpoint.Readout interface deleteExit := by
  change ¬ AcquisitionEndpoint.Pass cfg bindings deleteExit
  rintro ⟨d,hd,_,hall⟩
  have he := Option.some.inj (hd.symm.trans (decoded_eq deleteExit exit_deleted_complete))
  subst d
  exact (show AcquisitionEndpoint.atRoute cfg (data deleteExit) RouteId.a ≠ true
    from by decide +kernel) (List.all_eq_true.mp hall RouteId.a (by decide))

end CSTTT.TargetTheory.GenericHandoff.POS04AcquisitionEndpoint
