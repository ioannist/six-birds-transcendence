import CSTTT.Targets.GenericHandoff.POS04HistoricalEntryEquivalence

/-! Nominal-protocol resource readout equations on arbitrary partial POS-04
assignments. Missing consumed inputs reject before decoder totalization.
This component supplies resource interpretation laws, not whole-game soundness. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalResourceEquivalence
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RouteExecution POS04ResourceRuntime POS04HistoricalEntryEquivalence
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

abbrev rawResource (m : RawLaneModel) := HistoricalPackageRuntime.resources (model m)

theorem resource_data (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (POS04OperationalGame.inputs m).viability.resource =
      ⟨((image m.assignment (.resources .target)).getD (canonicalValue _)).owner,
       ((image m.assignment (.resources .target)).getD (canonicalValue _)).rechargeAvailable &&
         m.retained.contains .targetRecharge⟩ := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc (.resources .target) (by decide))
  rw [POS04OperationalGame.viability_eq]
  change ((image m.assignment (.resources .target)).map (fun v =>
    (⟨v.owner,v.rechargeAvailable && m.retained.contains .targetRecharge⟩ : ResourceData))).getD _ = _
  rw [hr]
  rfl

theorem unit_fields (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    ((image m.assignment (.resources .target)).getD (canonicalValue _)).owner = .target ∧
    ((image m.assignment (.resources .target)).getD (canonicalValue _)).rechargeAvailable = true ∧
    m.retained.contains .targetRecharge = true ∧
    (data m).ledger.initialBudget = 1 ∧ (data m).ledger.actionCost = 1 ∧
    (data m).ledger.rechargePerAction = 1 ∧ m.sourcePresentAfterWithdrawal = false := by
  have hav := (POS04OperationalGame.protocol_resources m hp).1
  have hl := (POS04OperationalGame.protocol_resources m hp).2.1
  have hres := resource_data m hp
  simp only [available8,Bool.and_eq_true,decide_eq_true_eq] at hav
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at hl
  rw [hres] at hav hl
  have hs : m.sourcePresentAfterWithdrawal = false := by
    have hw := hp.2.1
    simp only [withdrawalCheck,Bool.and_eq_true] at hw
    cases hs : m.sourcePresentAfterWithdrawal
    · rfl
    · simp [hs] at hw
  exact ⟨hav.2,(Bool.and_eq_true_iff.mp hl.1).1,(Bool.and_eq_true_iff.mp hl.1).2,
    hl.2.1,hl.2.2.1,hl.2.2.2.1,hs⟩

def account (r : Run6) : Resource → ResourceRuntime.Account
  | .recharge => ⟨some (tagCarrierId .target),true,if r.funded then 1 else 0⟩
  | .removed _ => ⟨none,false,0⟩

theorem accounts_eval (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6) :
    (rawResource m).accounts.eval (image m.assignment) (frame .target r) () = some (account r) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc (.resources .target) (by decide))
  have hl := POS04RegisterDynamics.cell_value (hc .maintenance (by decide))
  have hu := unit_fields m hp
  change (accounts (protocol m)).eval _ _ _ = _
  simp only [accounts,Expr.eval,frame,RunFrame.pack]
  rw [hr,hl]
  simp only [Option.map_some]
  apply congrArg some
  funext res
  cases res with
  | removed _ => rfl
  | recharge =>
    change (⟨some (tagCarrierId ((image m.assignment (.resources .target)).getD (canonicalValue _)).owner),
      ((image m.assignment (.resources .target)).getD (canonicalValue _)).rechargeAvailable &&
        m.retained.contains .targetRecharge,
      if r.funded then (data m).ledger.initialBudget else 0⟩ : ResourceRuntime.Account) = _
    rw [hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.1]
    rfl

theorem writer_eval (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6) :
    (rawResource m).writer.eval (image m.assignment) (frame .target r) () =
      some (POS04OperationalGame.writer (POS04OperationalGame.inputs m) r.residue) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc .routeTable (by decide))
  have hh := POS04RegisterDynamics.cell_value (hc .histories (by decide))
  have hw := POS04RegisterDynamics.cell_value (hc .writers (by decide))
  change (lift (POS04RegisterDynamics.writerExpression .target)).eval _ _ _ = _
  rw [POS04RouteExecution.lift,frame,RunFrame.evaluation]
  simp only [POS04RegisterDynamics.writerExpression,Expr.eval]
  rw [hr,hh,hw]
  rfl

theorem record_eval (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6) :
    (rawResource m).record.eval (image m.assignment) (frame .target r) () =
      some (POS04OperationalGame.record m r) := by
  change (lift (POS04RegisterDynamics.recordExpression .target)).eval _ _ _ = _
  rw [POS04RouteExecution.lift,frame,RunFrame.evaluation]
  simp only [POS04RegisterDynamics.recordExpression,Expr.eval]
  have hw := writer_eval m hp r
  change (lift (POS04RegisterDynamics.writerExpression .target)).eval _ _ _ = _ at hw
  rw [POS04RouteExecution.lift,frame,RunFrame.evaluation] at hw
  rw [hw]
  rfl

theorem withdrawal_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (rawResource m).withdrawal.read (image m.assignment) = some (withdrawal (protocol m)) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hl := POS04RegisterDynamics.cell_value (hc .maintenance (by decide))
  change (image m.assignment .maintenance).map (fun _ => withdrawal (protocol m)) = _
  rw [hl]
  rfl

theorem resource_closed_iff (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6) :
    ResourceRuntime.ResourceClosed (model m).resourceSchema (rawResource m)
      (image m.assignment) (frame .target r) ↔
      POS04OperationalGame.ResourceClosed m r := by
  have hu := unit_fields m hp
  have hres := POS04OperationalGame.protocol_resources m hp
  have hw := withdrawal_read m hp
  constructor
  · rintro ⟨ac,req,w,ha,hreq,hwithdraw,hsrc,hwriter,_,hret,hsafe,_⟩
    have heac := Option.some.inj ((accounts_eval m hp r).symm.trans ha)
    have hereq : req = [.recharge] := (Option.some.inj hreq).symm
    subst ac; subst req
    have hwriter' : POS04OperationalGame.writer (POS04OperationalGame.inputs m) r.residue = true :=
      Option.some.inj ((writer_eval m hp r).symm.trans hwriter)
    have hbalance := (hsafe .recharge (by simp)).2.2
    have funded : r.funded = true := by
      change (if r.funded then 1 else 0) > 0 at hbalance
      cases hf : r.funded
      · simp [hf] at hbalance
      · rfl
    exact ⟨hres.1,hres.2.1,funded,hwriter'⟩
  · rintro ⟨_,_,hf,hwriter⟩
    refine ⟨account r,[.recharge],withdrawal (protocol m),accounts_eval m hp r,rfl,hw,
      ?_,?_,by simp,?_,?_,?_⟩
    · change some m.sourcePresentAfterWithdrawal = some false
      rw [hu.2.2.2.2.2.2]
    · rw [writer_eval m hp r,hwriter]
    · intro res hr
      have heq := List.mem_singleton.mp hr
      subst res
      exact List.mem_map.mpr ⟨.targetRecharge,List.contains_iff_mem.mp hu.2.2.1,rfl⟩
    · intro res hr
      have heq := List.mem_singleton.mp hr
      subst res
      refine ⟨rfl,rfl,?_⟩
      simp [account,hf]
    · intro res hr
      obtain ⟨role,_,heq⟩ := List.mem_map.mp hr
      subst res
      rfl

/-- In the nominal funded protocol, withdrawal leaves the TARGET primitive
assignment unchanged. This equality preserves missing values, too; it is not
an assumption that acquisition support remains available. -/
theorem withdrawn_eq_image (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    withdrawnAssignment m = image m.assignment := by
  have hr := (unit_fields m hp).2.2.1
  funext k
  by_cases hk : k = Cell.resources .target
  · subst k
    change ((image m.assignment (.resources .target)).map (fun r =>
      (⟨r.owner,r.rechargeAvailable && m.retained.contains .targetRecharge⟩ : ResourceData))) = _
    cases hv : image m.assignment (.resources .target) with
    | none => rfl
    | some r => simp only [Option.map_some]; rw [hr]; simp only [Bool.and_true]; cases r; rfl
  · exact mapCell_other_cell _ _ _ _ hk

theorem response_rows_eq (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (r : Run6) (hr : POS04OperationalGame.ResourceClosed m r) (d : LaneDisturbance) (act : Action) :
    ResourceRuntime.rows (rawResource m) (image m.assignment) (frame .target r) d act =
      POS04OperationalGame.rows m r d act := by
  change HistoricalAcquisition.rows (raw m) (image m.assignment) (frame .target r) d act = _
  calc
    _ = actualRows6 (runInputs6 (image m.assignment) .target) r act :=
      POS04HistoricalRuntime.rows_eq _ _ (rawReady m hp) r d act
    _ = actualRows6 (runInputs6 (withdrawnAssignment m) .target) r act :=
      congrArg (fun a => actualRows6 (runInputs6 a .target) r act) (withdrawn_eq_image m hp).symm
    _ = _ := (POS04HistoricalAutonomy.responses_are_actual_rows m hp r hr d act).symm

theorem update_eq (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (h : HistoricalPackageRuntime.ResourceReady (model m) m.assignment)
    (r : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    ResourceRuntime.update (rawResource m) (HistoricalPackageRuntime.target (model m) m.assignment) h
      (frame .target r) d act o = frame .target (POS04OperationalGame.update m r d act o) := by
  have hu : actualUpdate6 (runInputs6 (image m.assignment) .target) r act o =
      POS04OperationalGame.update m r d act o :=
    (congrArg (fun a => actualUpdate6 (runInputs6 a .target) r act o)
      (withdrawn_eq_image m hp).symm).trans (POS04OperationalGame.actual_update_eq m r d act o).symm
  calc
    _ = HistoricalAcquisition.update (raw m) (HistoricalPackageRuntime.target (model m) m.assignment)
        (ready m hp) (frame .target r) d act o :=
      (HistoricalPackageRuntime.acquisition_resource_update (model m) m.assignment (ready m hp) h
        (frame .target r) d act o).symm
    _ = frame .target (actualUpdate6
        (runInputs6 (HistoricalPackageRuntime.target (model m) m.assignment) .target) r act o) :=
      POS04HistoricalRuntime.update_eq (protocol m) _ (ready m hp) r d act o
    _ = frame .target (actualUpdate6 (runInputs6 (image m.assignment) .target) r act o) :=
      congrArg (fun a => frame .target (actualUpdate6 (runInputs6 a .target) r act o))
        (POS04HistoricalRuntime.target_eq (protocol m) m.assignment)
    _ = _ := congrArg (frame Tag.target) hu

/-- The displayed unit charge is derived from the declared ledger equations
in unit_fields; it is not a new price or an independent ownership verdict. -/
def unitCharge : ResourceRuntime.Charge Resource :=
  ⟨tagCarrierId .target,[.recharge],
    (fun res => match res with | .recharge => 1 | _ => 0),
    (fun res => match res with | .recharge => 1 | _ => 0)⟩

theorem charge_eval (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (r : Run6) (d : LaneDisturbance) (act : Action) :
    (rawResource m).charge.eval (image m.assignment) (frame .target r) (d,act) = some unitCharge := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc (.resources .target) (by decide))
  have hl := POS04RegisterDynamics.cell_value (hc .maintenance (by decide))
  have hu := unit_fields m hp
  change (charge (protocol m)).eval _ _ _ = _
  simp only [charge,Expr.eval,frame,RunFrame.pack]
  rw [hr,hl]
  change some (⟨tagCarrierId ((image m.assignment (.resources .target)).getD (canonicalValue _)).owner,
    [.recharge],(fun res => match res with | .recharge => (data m).ledger.actionCost | _ => 0),
    (fun res => match res with
      | .recharge =>
        if ((image m.assignment (.resources .target)).getD (canonicalValue _)).rechargeAvailable &&
          m.retained.contains .targetRecharge then (data m).ledger.rechargePerAction else 0
      | _ => 0)⟩ : ResourceRuntime.Charge Resource) = _
  rw [hu.1,hu.2.1,hu.2.2.1,hu.2.2.2.2.1,hu.2.2.2.2.2.1]
  rfl

/-- Legal resource expenditure alone does not assert support closure. The
whole-game adapter must derive that from its normalized response and invariant. -/
theorem legal_of_resource_closed (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (r : Run6) (hr : POS04OperationalGame.ResourceClosed m r) (d : LaneDisturbance) (act : Action) :
    ResourceRuntime.Legal (model m).resourceSchema (rawResource m) (image m.assignment)
      (frame .target r) d act := by
  have hu := unit_fields m hp
  refine ⟨(by change d ∈ [LaneDisturbance.nominal]; cases d; decide),
    (by change act ∈ actions; cases act <;> decide),
    account r,[.recharge],unitCharge,withdrawal (protocol m),accounts_eval m hp r,rfl,
    charge_eval m hp r d act,withdrawal_read m hp,rfl,by simp [unitCharge],by simp [unitCharge],?_,?_,?_⟩
  · intro res hm
    have heq := List.mem_singleton.mp hm
    subst res
    exact List.mem_map.mpr ⟨.targetRecharge,List.contains_iff_mem.mp hu.2.2.1,rfl⟩
  · intro res hm
    have heq := List.mem_singleton.mp hm
    subst res
    change Resource.recharge ∈ resources
    simp [resources]
  · intro res hm
    have heq := List.mem_singleton.mp hm
    subst res
    refine ⟨rfl,rfl,?_,?_⟩
    all_goals simp [account,unitCharge,hr.2.2.1]

theorem wrong_owner_rejected (m : RawLaneModel)
    (bad : ((image m.assignment (.resources .target)).getD (canonicalValue _)).owner ≠ .target) :
    (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) ≠ some true := by
  intro hc
  exact bad (unit_fields m ((POS04HistoricalRuntimeProtocol.check_iff m).mp hc)).1

theorem nonunit_ledger_rejected (m : RawLaneModel)
    (bad : (data m).ledger.initialBudget ≠ 1 ∨ (data m).ledger.actionCost ≠ 1 ∨
      (data m).ledger.rechargePerAction ≠ 1) :
    (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) ≠ some true := by
  intro hc
  have hu := unit_fields m ((POS04HistoricalRuntimeProtocol.check_iff m).mp hc)
  rcases bad with hb | hc | hr
  · exact hb hu.2.2.2.1
  · exact hc hu.2.2.2.2.1
  · exact hr hu.2.2.2.2.2.1

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalResourceEquivalence
