import CSTTT.Targets.GenericHandoff.NominalProtocol
import CSTTT.Targets.GenericHandoff.POS04ReceiverIntervention

namespace CSTTT.TargetTheory.GenericHandoff.POS04NominalProtocol
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH NominalProtocol
open POS04ResourceRuntime
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def specification : Specification KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag Resource :=
  ⟨(POS04OperationalViability.schema .source).destination,POS04OperationalViability.schema .target,
    ambientStates,routeIds,stages,.sourceLive,.targetExit,.exit,1,1,[.recharge]⟩

def legacyData (m : RawLaneModel) : Data KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag :=
  let src := clauseExtra (image m.assignment) .source .c6
  let dst := arrivalInputs m
  ⟨src.base.rows,dst.base.base.rows,src.base.policy,dst.base.base.policy,dst.ticks,
    ⟨dst.resource.owner,dst.resource.rechargeAvailable⟩,
    ⟨dst.ledger.initialBudget,dst.ledger.actionCost,dst.ledger.rechargePerAction⟩,
    dst.base.histories,dst.base.events.map POS04AcquisitionEndpoint.eventMap,dst.base.realized,
    POS04ExecutionFrontier.receiverView.project dst.base.receiver,
    dst.base.routes.map POS04TemporalFactor.routeMap,dst.base.writers .target⟩

def tableViews : Views Cell Value KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag :=
  views POS04PresentationCoherence.frames

def withdrawalData (m : RawLaneModel) : Metadata Resource :=
  ⟨(withdrawal (protocol m)).removedRoles,(withdrawal (protocol m)).retained,(protocol m).sourcePresent⟩

theorem retained_eq (m : RawLaneModel) :
    specification.required.all (fun r => decide (r ∈ (withdrawalData m).retained)) =
      m.retained.contains .targetRecharge := by
  cases hr : m.retained with
  | nil => simp [specification,withdrawalData,withdrawal,protocol,hr]
  | cons r rs => cases r; simp [specification,withdrawalData,withdrawal,protocol,hr]

theorem role_image_injective : Function.Injective roleImage := by
  intro x y h
  cases x <;> cases y <;> simp_all [roleImage]

theorem role_mem (m : RawLaneModel) (r : RemovedRole) :
    roleImage r ∈ (withdrawalData m).removedRoles ↔ r ∈ m.removed := by
  change roleImage r ∈ m.removed.map roleImage ↔ r ∈ m.removed
  constructor
  · intro h
    obtain ⟨s,hs,equal⟩ := List.mem_map.mp h
    exact role_image_injective equal ▸ hs
  · intro h
    exact List.mem_map.mpr ⟨r,h,rfl⟩

theorem withdrawal_iff (m : RawLaneModel) :
    ((∀ role ∈ ResourceRuntime.roles, role ∈ (withdrawalData m).removedRoles) ∧
      (∀ role ∈ (withdrawalData m).removedRoles, role ∈ ResourceRuntime.roles) ∧
      (withdrawalData m).sourcePresent = false) ↔ withdrawalCheck m = true := by
  simp only [withdrawalCheck,Bool.and_eq_true,List.all_eq_true,List.contains_iff_mem,Bool.not_eq_true']
  constructor
  · rintro ⟨allCore,_,absent⟩
    exact ⟨⟨(fun r _ => (role_mem m r).mp (allCore (roleImage r) (by cases r <;> decide))),
      (fun r _ => by cases r <;> decide)⟩,absent⟩
  · rintro ⟨⟨allNative,_⟩,absent⟩
    refine ⟨?_,(fun r _ => by cases r <;> decide),absent⟩
    intro core _
    cases core <;> first
      | exact (role_mem m .source).mpr (allNative .source (by decide))
      | exact (role_mem m .migrationBridge).mpr (allNative .migrationBridge (by decide))
      | exact (role_mem m .migrationController).mpr (allNative .migrationController (by decide))
      | exact (role_mem m .externalDecoder).mpr (allNative .externalDecoder (by decide))
      | exact (role_mem m .externalScheduler).mpr (allNative .externalScheduler (by decide))
      | exact (role_mem m .undeclaredRepair).mpr (allNative .undeclaredRepair (by decide))

theorem withdrawn_eq (m : RawLaneModel)
    (hc : Assigned.Complete phase2Dependencies (image m.assignment)) :
    withdrawn specification (withdrawalData m) (legacyData m) =
      POS04OperationalViability.raw (withdrawnInputs m) := by
  have hres := POS04RegisterDynamics.cell_value (hc (.resources .target) (by decide))
  unfold withdrawn
  rw [retained_eq]
  let before := POS04OperationalViability.raw (clause8 (image m.assignment) .target)
  change {before with resource := {before.resource with rechargeAvailable :=
    before.resource.rechargeAvailable && (m.retained.contains RetainedResource.targetRecharge)}} = _
  simp only [before,POS04OperationalViability.raw,withdrawnInputs,clause8,viabilityInputs,
    Assigned.decode,clauseScope,withdrawnAssignment,mapCell,Assigned.put]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  simp only [reduceCtorEq,or_true,true_or,ite_true]
  rw [hres]
  rfl

theorem dependency_iff (k : Cell) : k ∈ (reader tableViews).dependencies ↔ k ∈ phase2Dependencies := by
  cases k
  all_goals try (rename_i t; cases t)
  all_goals decide

theorem reader_computed (m : RawLaneModel)
    (hc : Assigned.Complete phase2Dependencies (image m.assignment)) :
    (reader tableViews).read (image m.assignment) = some (legacyData m) := by
  have hs := POS04RegisterDynamics.cell_value (hc (.rows .source) (by decide))
  have ht := POS04RegisterDynamics.cell_value (hc (.rows .target) (by decide))
  have hp := POS04RegisterDynamics.cell_value (hc .policy (by decide))
  have htk := POS04RegisterDynamics.cell_value (hc (.ticks .target) (by decide))
  have hr := POS04RegisterDynamics.cell_value (hc (.resources .target) (by decide))
  have hl := POS04RegisterDynamics.cell_value (hc .maintenance (by decide))
  have hh := POS04RegisterDynamics.cell_value (hc .histories (by decide))
  have he := POS04RegisterDynamics.cell_value (hc .eventTable (by decide))
  have hreal := POS04RegisterDynamics.cell_value (hc .realized (by decide))
  have hrecv := POS04RegisterDynamics.cell_value (hc .receiverInput (by decide))
  have hroute := POS04RegisterDynamics.cell_value (hc .routeTable (by decide))
  have hw := POS04RegisterDynamics.cell_value (hc .writers (by decide))
  simp only [reader,StaticView.read,StaticView.ofCell,RegisterInterpreter.Expr.eval,
    tableViews,views,POS04PresentationCoherence.frames,POS04TemporalFactor.bindings,
    POS04AcquisitionEndpoint.bindings,POS04ExecutionFrontier.receiverView]
  rw [hs,ht,hp,htk,hr,hl,hh,he,hreal,hrecv,hroute,hw]
  rfl

theorem tuple_eq (m : RawLaneModel) (rid : RouteId) :
    tuple (legacyData m) rid = routeTuple (arrivalInputs m).base rid := by
  simp only [tuple,legacyData,routeTuple,List.find?_map,Function.comp_def,POS04TemporalFactor.routeMap,
    Bool.beq_eq_decide_eq,Option.map_map]

theorem event_eq (m : RawLaneModel) (id : EventId) :
    event (legacyData m) id = (event6 (arrivalInputs m) id).map POS04AcquisitionEndpoint.eventMap := by
  simp only [event,legacyData,event6,List.find?_map,Function.comp_def,POS04AcquisitionEndpoint.eventMap]

theorem strict_eq (m : RawLaneModel) (e : CSTTT.POS04.Event) :
    strict specification (legacyData m) (POS04AcquisitionEndpoint.eventMap e) = strictEvent6 (arrivalInputs m) e := rfl

theorem active_eq (m : RawLaneModel) : active specification (legacyData m) = active7 (arrivalInputs m).base := by
  simp only [active,mixed,legacyData,specification,POS04ExecutionFrontier.receiverView,
    active7,mixed7,List.any_map,Function.comp_def,POS04AcquisitionEndpoint.eventMap,
    bne,Bool.beq_eq_decide_eq,decide_not]

theorem weight_eq (rows : KState → Action → List (Ambient × Nat)) (policy : KState → Action) (s t : KState) :
    weight (POS04OperationalViability.schema .target).destination rows policy s t = rowWeight (rows s (policy s)) t := by
  rw [POS04ObjecthoodQuotient.rowWeight_sum]
  unfold weight
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  cases e.1 <;> simp [POS04OperationalViability.schema]

theorem source_support_eq (m : RawLaneModel) (history : List KState) :
    supported specification.sourceDestination (legacyData m).sourceRows (legacyData m).sourcePolicy history =
      pathSupported (clauseExtra (image m.assignment) .source .c6) history := by
  change supported (POS04OperationalViability.schema .target).destination
    (clauseExtra (image m.assignment) .source .c6).base.rows
    (clauseExtra (image m.assignment) .source .c6).base.policy history = _
  simp only [supported,pathSupported,weight_eq]

theorem target_support_eq (m : RawLaneModel) (history : List KState) :
    supported specification.viability.destination (legacyData m).rows (legacyData m).policy history =
      pathSupported (arrivalInputs m).base history := by
  change supported (POS04OperationalViability.schema .target).destination
    (arrivalInputs m).base.base.rows (arrivalInputs m).base.base.policy history = _
  simp only [supported,pathSupported,weight_eq]

theorem path_eq (m : RawLaneModel) (rid : RouteId) (history : List KState) (ids : List EventId)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,ids)) :
    path specification (legacyData m) history ids = path6 (arrivalInputs m) rid := by
  have stricts : ids.all (fun id => (event (legacyData m) id).any (strict specification (legacyData m))) =
      ids.all (fun id => (event6 (arrivalInputs m) id).any (strictEvent6 (arrivalInputs m))) := by
    apply congrArg (fun f => ids.all f)
    funext id
    rw [event_eq]
    cases he : event6 (arrivalInputs m) id <;> simp [strict_eq]
  simp only [path,target_support_eq,stricts,path6,ht]
  congr 1
  · cases history <;> simp [pathSupported]
  · apply congrArg (fun f => (ids.zip (ids.drop 1)).all f)
    funext pair
    rw [event_eq,event_eq]
    cases he : event6 (arrivalInputs m) pair.1 <;> cases hf : event6 (arrivalInputs m) pair.2 <;> rfl

theorem available_eq (m : RawLaneModel) :
    OperationalViability.available specification.viability (operational (legacyData m)) =
      available8 (clause8 (image m.assignment) .target) .target := rfl

theorem phase2_eq (m : RawLaneModel) (hc : Assigned.Complete phase2Dependencies (image m.assignment)) (rid : RouteId) :
    phase2 specification (legacyData m) rid = phase2Check m rid := by
  have complete : phase2Complete m = true := decide_eq_true hc
  unfold phase2Check
  rw [complete]
  simp only [Bool.not_true,Bool.false_eq_true,ite_false]
  unfold phase2
  rw [tuple_eq]
  cases ht : routeTuple (arrivalInputs m).base rid with
  | none => rfl
  | some tupleValue =>
    rcases tupleValue with ⟨history,ids⟩
    dsimp only
    cases hterminal : history.getLast? with
    | none =>
      have empty : history = [] := List.getLast?_eq_none_iff.mp hterminal
      subst history
      simp [path6,ht,pathSupported]
    | some terminal =>
      dsimp only
      cases hhead : ids.head? with
      | none => simp
      | some first =>
        dsimp only
        cases hlast : ids.getLast? with
        | none => simp
        | some final =>
          dsimp only
          rw [event_eq,event_eq]
          cases hstart : event6 (arrivalInputs m) first <;> cases hfinish : event6 (arrivalInputs m) final
          all_goals simp only [Option.map_none,Option.map_some]
          all_goals try simp
          simp only [active_eq,path_eq m rid history ids ht,source_support_eq,available_eq]
          simp only [legacyData,specification,POS04AcquisitionEndpoint.eventMap,POS04OperationalViability.schema,
            Bool.and_assoc,hterminal,Option.getD_some]

theorem withdrawn_projections (m : RawLaneModel) :
    (runInputs6 (withdrawnAssignment m) .target).base.base.rows = (legacyData m).rows ∧
    (runInputs6 (withdrawnAssignment m) .target).ticks = (legacyData m).ticks ∧
    (runInputs6 (withdrawnAssignment m) .target).base.writers .target = (legacyData m).writers ∧
    (runInputs6 (withdrawnAssignment m) .target).base.routes.map POS04TemporalFactor.routeMap =
      (legacyData m).routeTable := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem advancement_iff (m : RawLaneModel) (hc : Assigned.Complete phase2Dependencies (image m.assignment)) :
    (OperationalViability.available specification.viability (withdrawn specification (withdrawalData m) (legacyData m)) = true ∧
     OperationalViability.LedgerCheck specification.viability (withdrawn specification (withdrawalData m) (legacyData m)) ∧
     (∀ s ∈ specification.viability.states, ∀ a ∈ specification.viability.actions,
       ((legacyData m).rows s a).isEmpty = false → (legacyData m).ticks s a = specification.tickAdvance) ∧
     specification.routes ≠ [] ∧ (∀ rid ∈ specification.routes, (legacyData m).writers rid = true) ∧
     (legacyData m).routeTable ≠ []) ↔ advancementCheck m = true := by
  rw [withdrawn_eq m hc]
  dsimp only [specification]
  rw [POS04OperationalViability.available_eq]
  have hl : OperationalViability.LedgerCheck (POS04OperationalViability.schema .target)
      (POS04OperationalViability.raw (withdrawnInputs m)) ↔ Ledger8 (withdrawnInputs m) := Iff.rfl
  rw [hl]
  simp only [advancementCheck,Bool.and_eq_true,decide_eq_true_eq,ticks6,writers6,
    (withdrawn_projections m).1,(withdrawn_projections m).2.1,(withdrawn_projections m).2.2.1,
    List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.isEmpty_eq_false_iff,
    POS04OperationalViability.schema]
  have hr : (legacyData m).routeTable ≠ [] ↔ (runInputs6 (withdrawnAssignment m) .target).base.routes ≠ [] := by
    rw [← (withdrawn_projections m).2.2.2]
    simp
  rw [hr]
  have ht : (∀ s ∈ kernel, ∀ a ∈ actions,
      (legacyData m).rows s a ≠ [] → (legacyData m).ticks s a = 1) ↔
      (∀ s ∈ kernel, ∀ a ∈ actions,
        ((legacyData m).rows s a).isEmpty = true ∨ (legacyData m).ticks s a = 1) := by
    apply forall_congr'
    intro s
    apply imp_congr_right
    intro _
    apply forall_congr'
    intro a
    apply imp_congr_right
    intro _
    cases (legacyData m).rows s a <;> simp
  simp only [ht,and_assoc]

theorem unchanged_iff (m : RawLaneModel) (hc : Assigned.Complete phase2Dependencies (image m.assignment)) :
    OperationalViability.PUnchanged specification.viability (withdrawn specification (withdrawalData m) (legacyData m)) ↔
      PUnchanged8 (withdrawnInputs m) := by
  rw [withdrawn_eq m hc]
  change OperationalViability.PUnchanged (POS04OperationalViability.schema .target)
    (POS04OperationalViability.raw (withdrawnInputs m)) ↔ _
  simp only [OperationalViability.PUnchanged,POS04OperationalViability.weight_eq]
  rfl

theorem check_iff (m : RawLaneModel) (hc : Assigned.Complete phase2Dependencies (image m.assignment)) :
    check specification (withdrawalData m) (legacyData m) ↔ POS04OperationalGame.Protocol m := by
  have ha : Assigned.Complete autonomyInputs (image m.assignment) := by
    intro k hk
    apply hc k
    cases k
    all_goals try (rename_i t; cases t)
    all_goals simp_all [autonomyInputs,phase2Dependencies,clauseScope]
  unfold check POS04OperationalGame.Protocol
  rw [and_iff_right ha]
  rw [← withdrawal_iff,← advancement_iff m hc,← unchanged_iff m hc]
  simp only [List.all_eq_true,← phase2_eq m hc]
  simp only [specification,and_assoc]

theorem pass_iff (m : RawLaneModel) :
    Pass specification (withdrawalData m) tableViews (image m.assignment) ↔ POS04OperationalGame.Protocol m := by
  constructor
  · rintro ⟨d,hd,checked⟩
    have hc : Assigned.Complete phase2Dependencies (image m.assignment) := by
      intro k hk
      by_cases hm : image m.assignment k = none
      · have absent := (reader tableViews).missing (image m.assignment) k ((dependency_iff k).mpr hk) hm
        rw [absent] at hd
        contradiction
      · exact Option.isSome_iff_ne_none.mpr hm
    rw [reader_computed m hc] at hd
    have eq := Option.some.inj hd
    subst d
    exact (check_iff m hc).mp checked
  · intro hp
    have hc : Assigned.Complete phase2Dependencies (image m.assignment) :=
      fun k hk => POS04OperationalGame.protocol_complete m hp k (List.mem_append_right _ hk)
    exact ⟨legacyData m,reader_computed m hc,(check_iff m hc).mpr hp⟩

/-- These controls concern the defined nominal protocol, not bare-game rejection. -/
theorem baseline_pass : Pass specification (withdrawalData baseline) tableViews (image baseline.assignment) :=
  (pass_iff _).mpr POS04ExactGames.positive_games.2.1

theorem duplicate_event_pass : Pass specification (withdrawalData POS04HistoricalDuplicateEvents.diagnostic)
    tableViews (image POS04HistoricalDuplicateEvents.diagnostic.assignment) :=
  (pass_iff _).mpr ((POS04HistoricalRuntimeProtocol.check_iff _).mp
    POS04HistoricalRuntimeProtocol.duplicate_event_protocol)

theorem missing_past_ticks_pass : Pass specification (withdrawalData POS04RuntimeEquivalenceBoundary.missingPastTicks)
    tableViews (image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment) :=
  (pass_iff _).mpr POS04RuntimeEquivalenceBoundary.legacy_operational_game_accepts.1

theorem source_recharge_pass : Pass specification (withdrawalData POS04ReceiverResetProjection.sourceRechargeUnavailable)
    tableViews (image POS04ReceiverResetProjection.sourceRechargeUnavailable.assignment) :=
  (pass_iff _).mpr POS04ReceiverResetProjection.diagnostic_legacy_operational_game_accepts.1

theorem zero_ledger_rejected : ¬ Pass specification (withdrawalData POS04HistoricalRuntimeProtocol.zeroLedger)
    tableViews (image POS04HistoricalRuntimeProtocol.zeroLedger.assignment) := by
  intro h
  exact POS04HistoricalRuntimeProtocol.zero_ledger_rejected
    ((POS04HistoricalRuntimeProtocol.check_iff _).mpr ((pass_iff _).mp h))

theorem missing_primitive_rejected (m : RawLaneModel) (k : Cell) (hk : k ∈ phase2Dependencies)
    (hm : image m.assignment k = none) : ¬ Pass specification (withdrawalData m) tableViews (image m.assignment) :=
  missing_no_pass _ _ _ _ k ((dependency_iff k).mpr hk) hm

theorem unused_primitive_locality (m : RawLaneModel) (k : Cell) (hk : k ∉ phase2Dependencies)
    (v : Option (Value k)) :
    Pass specification (withdrawalData m) tableViews (Assigned.put (image m.assignment) k v) ↔
      Pass specification (withdrawalData m) tableViews (image m.assignment) := by
  apply locality
  intro j hj
  have hj' := (dependency_iff j).mp hj
  have neq : j ≠ k := by intro e; subst j; exact hk hj'
  exact Assigned.put_other _ _ _ _ neq

end CSTTT.TargetTheory.GenericHandoff.POS04NominalProtocol
