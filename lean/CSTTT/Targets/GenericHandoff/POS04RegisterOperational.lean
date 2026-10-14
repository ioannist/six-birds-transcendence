import CSTTT.Targets.GenericHandoff.RegisterOperational
import CSTTT.Targets.GenericHandoff.POS04RegisterDynamics

/-! Exact POS-04 operational-component interpretation. Rows, priced resource,
writer, current factor and advancement are read from the SAME assignment.
Partial assignments are allowed; consumed cells must be present. The operational
scope has no hazards. The outer acquisition/withdrawal protocol remains G6c's
computed family protocol until G6d-4 extraction; it is not a supplied raw verdict.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RegisterOperational
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04RegisterDynamics


-- Numerical parameters are the declared M3/G6 unit ledger and response scale,
-- not generic constants. The underlying component schema does not fix them.
def schema : RegisterOperational.Schema KState Action LaneDisturbance Ambient :=
  ⟨kernel,actions,[.nominal],(fun o => match o with | .inK s => some s | _ => none),
    tagCarrierId .target,1,1,1,4,1,1,1⟩

def rawRow : E (LaneDisturbance × Action) (List (Ambient × Nat)) :=
  .map (fun (p : (KState → Action → List (Ambient × Nat)) × Ambient × Action) =>
    match p.2.1 with | .inK s => p.1 s p.2.2 | _ => [])
    (.pair (.cell (Cell.rows .target)) (.pair (.register Register.factor) (.environment Prod.snd)))

def finance : E Unit RegisterOperational.Finance :=
  .map (fun (p : ResourceData × Ledger) =>
    ⟨tagCarrierId p.1.owner,p.1.rechargeAvailable,p.2.initialBudget,p.2.actionCost,p.2.rechargePerAction⟩)
    (.pair (.cell (Cell.resources .target)) (.cell Cell.maintenance))

def raw : RegisterOperational.Raw Cell Value Register RegisterValue
    KState Action LaneDisturbance Ambient (List KState × List EventId) :=
  ⟨rawRow,program .target,finance,
    .map (fun (s : Ambient) => match s with | .inK s => some s | _ => none) (.register Register.factor),
    .register Register.counter,.register Register.ticks,writerExpression .target,
    recordExpression .target,.register Register.residue,.register Register.funded⟩

def dependencies : List Cell :=
  coreDependencies .target ++ [.resources .target,.routeTable,.histories,.writers]

theorem ready_of_complete (a : CSTTT.POS04.Assigned.Assignment)
    (h : Complete dependencies a) : RegisterOperational.Ready raw a := by
  refine ⟨?_,program_ready a .target (fun k hk => h k (List.mem_append_left _ hk)),?_⟩
  · intro k hk
    simp only [raw,rawRow,Expr.dependencies,List.mem_append,List.mem_singleton,List.not_mem_nil,or_false] at hk
    subst k
    exact h _ (by simp [dependencies,coreDependencies])
  · intro k hk
    simp [raw,finance,writerExpression,recordExpression,Expr.dependencies] at hk
    rcases hk with hk | hk | hk | hk | hk | hk | hk | hk
    all_goals subst k; exact h _ (by simp [dependencies,coreDependencies])

theorem raw_row_eval (a : CSTTT.POS04.Assigned.Assignment)
    (h : Complete dependencies a) (r : Run6) (d : LaneDisturbance) (act : Action) :
    raw.row.eval a (encode r) (d,act) = some (row6 (runInputs6 a .target) r.factor act) := by
  have hv := cell_value (h (.rows .target) (by simp [dependencies,coreDependencies]))
  simp only [raw,rawRow,Expr.eval,encode]
  rw [hv]
  cases r.factor <;> simp only [row6] <;> rfl

theorem finance_eval (a : CSTTT.POS04.Assigned.Assignment)
    (h : Complete dependencies a) (r : Run6) :
    raw.finance.eval a (encode r) () = some
      (⟨tagCarrierId (clause8 a .target).resource.owner,(clause8 a .target).resource.rechargeAvailable,
       (clause8 a .target).budget.initialBudget,(clause8 a .target).budget.actionCost,
       (clause8 a .target).budget.rechargePerAction⟩ : RegisterOperational.Finance) := by
  have hr := cell_value (h (.resources .target) (by simp [dependencies]))
  have hl := cell_value (h .maintenance (by simp [dependencies,coreDependencies]))
  simp only [raw,finance,Expr.eval]
  rw [hr,hl]
  rfl

-- Writer instructions use no predictive/class/health readouts.
theorem writer_eval_operational (a : CSTTT.POS04.Assigned.Assignment)
    (h : Complete dependencies a) (r : Run6) :
    raw.writer.eval a (encode r) () = some (writer6 (runInputs6 a .target) .target r.residue) := by
  have hr := cell_value (h .routeTable (by simp [dependencies]))
  have hh := cell_value (h .histories (by simp [dependencies]))
  have hw := cell_value (h .writers (by simp [dependencies]))
  simp only [raw,writerExpression,Expr.eval,encode]
  rw [hr,hh,hw]
  rfl

theorem record_eval_operational (a : CSTTT.POS04.Assigned.Assignment)
    (h : Complete dependencies a) (r : Run6) :
    raw.record.eval a (encode r) () = some
      ((observation6 (runInputs6 a .target) .target r).endogenousRecordCount) := by
  change (recordExpression .target).eval a (encode r) () = _
  simp only [recordExpression,Expr.eval,encode]
  have hw := writer_eval_operational a h r
  change (writerExpression .target).eval a (encode r) () = _ at hw
  rw [hw]
  rfl

/-- Withdrawal only changes a present value, never fills a missing cell. -/
theorem withdrawn_present (m : RawLaneModel) (k : Cell) :
    ((withdrawnAssignment m) k).isSome = ((image m.assignment) k).isSome := by
  unfold withdrawnAssignment
  by_cases he : k = Cell.resources .target
  · subst k
    simp only [mapCell,Assigned.put_same]
    cases ((image m.assignment) (.resources .target)) <;> rfl
  · rw [mapCell_other_cell _ _ _ _ he]

theorem complete_of_protocol (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    Complete dependencies (withdrawnAssignment m) := by
  intro k hk
  rw [withdrawn_present]
  apply POS04OperationalGame.protocol_complete m hp k
  simp [dependencies,coreDependencies] at hk
  rcases hk with hk | hk | hk | hk | hk | hk | hk <;> subst k <;> decide

theorem update_eq (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6)
    (d : LaneDisturbance) (act : Action) (o : Ambient) :
    RegisterOperational.update raw (withdrawnAssignment m)
      (ready_of_complete _ (complete_of_protocol m hp)) (encode r) d act o =
      encode (POS04OperationalGame.update m r d act o) := by
  rw [POS04OperationalGame.actual_update_eq]
  exact checked_actual _ .target
    (fun k hk => complete_of_protocol m hp k (List.mem_append_left _ hk)) r d act o

theorem rows_eq (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6)
    (d : LaneDisturbance) (act : Action) :
    RegisterOperational.rows schema raw (withdrawnAssignment m) (encode r) d act = POS04OperationalGame.rows m r d act := by
  simp only [RegisterOperational.rows,raw_row_eval _ (complete_of_protocol m hp),Option.getD_some]
  simp only [POS04OperationalGame.rows,if_pos (POS04OperationalGame.protocol_complete m hp)]
  congr 1
  cases r.factor <;> rfl

theorem inside_iff (m : RawLaneModel) (r : Run6) :
    RegisterOperational.Inside schema raw (withdrawnAssignment m) (encode r) ↔ POS04OperationalGame.Inside m r := by
  have hk (s : KState) : s ∈ kernel := by cases s <;> decide
  cases hf : r.factor <;> simp [RegisterOperational.Inside,raw,Expr.eval,encode,schema,POS04OperationalGame.Inside,hf,hk]


theorem resource_iff (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6) :
    RegisterOperational.ResourceClosed schema raw (withdrawnAssignment m) (encode r) ↔ POS04OperationalGame.ResourceClosed m r := by
  unfold RegisterOperational.ResourceClosed
  rw [finance_eval _ (complete_of_protocol m hp),writer_eval_operational _ (complete_of_protocol m hp)]
  simp only [Option.some.injEq,exists_eq_left']
  change _ ∧ (some r.funded : Option Bool) = some true ∧ _ ↔ _
  simp only [Option.some.injEq]
  have hr := POS04OperationalGame.protocol_resources m hp
  have hav := hr.1
  rw [POS04OperationalGame.viability_eq] at hav
  have hl := hr.2.1
  rw [POS04OperationalGame.viability_eq] at hl
  have ho : (withdrawnInputs m).resource.owner = Tag.target :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hav).2
  have hf : RegisterOperational.FinanceValid schema
      ⟨tagCarrierId (withdrawnInputs m).resource.owner,(withdrawnInputs m).resource.rechargeAvailable,
       (withdrawnInputs m).budget.initialBudget,(withdrawnInputs m).budget.actionCost,
       (withdrawnInputs m).budget.rechargePerAction⟩ := by
    simp only [RegisterOperational.FinanceValid,schema]
    rw [ho,hl.1,hl.2.1,hl.2.2.1,hl.2.2.2.1]
    decide
  change RegisterOperational.FinanceValid schema
      ⟨tagCarrierId (withdrawnInputs m).resource.owner,(withdrawnInputs m).resource.rechargeAvailable,
       (withdrawnInputs m).budget.initialBudget,(withdrawnInputs m).budget.actionCost,
       (withdrawnInputs m).budget.rechargePerAction⟩ ∧
    r.funded = true ∧ writer6 (runInputs6 (withdrawnAssignment m) .target) .target r.residue = true ↔ _
  rw [← POS04OperationalGame.writer_eq]
  unfold POS04OperationalGame.ResourceClosed
  rw [POS04OperationalGame.viability_eq]
  simp only [hf,hav,hl,true_and]

theorem legal_iff (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6)
    (d : LaneDisturbance) (act : Action) :
    RegisterOperational.Legal schema raw (withdrawnAssignment m) (encode r) d act ↔
      POS04OperationalGame.Legal m r d act := by
  unfold RegisterOperational.Legal
  rw [raw_row_eval _ (complete_of_protocol m hp)]
  simp only [Option.some.injEq,exists_eq_left']
  have hd : d ∈ schema.disturbances := by cases d; decide
  rw [and_iff_right hd]
  cases hf : r.factor with
  | p2w0 => simp [row6,hf,POS04OperationalGame.Legal]
  | p5w1 => simp [row6,hf,POS04OperationalGame.Legal]
  | inK s =>
    change act ∈ actions ∧ _ ↔ _
    constructor
    · rintro ⟨ha,hn,hs,he⟩
      refine ⟨ha,s,hf,?_⟩
      have hrows : row6 (runInputs6 (withdrawnAssignment m) .target) (.inK s) act =
          (POS04OperationalGame.inputs m).viability.rows s act := rfl
      rw [hrows] at hn hs he
      simp only [rowClosed8,Bool.and_eq_true,List.all_eq_true]
      refine ⟨⟨by simpa using List.isEmpty_eq_false_iff.mpr hn,decide_eq_true hs⟩,?_⟩
      intro e hm
      obtain ⟨hpos,t,ht,hout⟩ := he e hm
      cases ho : e.1 with
      | inK u =>
        have hut : u = t := Option.some.inj (by simpa [schema,ho] using hout)
        subst t
        simp only [decide_eq_true_eq]
        exact ⟨hpos,ht⟩
      | p2w0 => simp [schema,ho] at hout
      | p5w1 => simp [schema,ho] at hout
    · rintro ⟨ha,t,ht,hr⟩
      have heq : t = s := by injection (ht.symm.trans hf)
      subst t
      have hfields := POS04OperationalGame.closed_fields _ _ _ _ hr
      refine ⟨ha,?_,?_,?_⟩
      · exact hfields.1
      · exact hfields.2.1
      · intro e he
        obtain ⟨hp,t,ht,hm⟩ := hfields.2.2 e he
        exact ⟨hp,t,hm,by simp [schema,ht]⟩

theorem step_iff (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6)
    (d : LaneDisturbance) (act : Action) (o : Ambient) :
    RegisterOperational.StepLaw schema raw (withdrawnAssignment m)
      (ready_of_complete _ (complete_of_protocol m hp)) (encode r) d act o ↔
      POS04OperationalGame.StepLaw m r d act o := by
  unfold RegisterOperational.StepLaw
  dsimp only
  rw [update_eq m hp]
  rw [record_eval_operational _ (complete_of_protocol m hp) r,
    record_eval_operational _ (complete_of_protocol m hp) (POS04OperationalGame.update m r d act o),
    finance_eval _ (complete_of_protocol m hp) (POS04OperationalGame.update m r d act o)]
  simp only [raw,Expr.eval,encode,Option.some.injEq,exists_eq_left',schema,
    show (1 : Nat) > 0 from by decide,true_and]
  rw [← POS04OperationalGame.record_actual_observer,← POS04OperationalGame.record_actual_observer]
  have ownerLink (t : Tag) : tagCarrierId t = tagCarrierId Tag.target ↔ t = Tag.target := by
    cases t <;> decide
  rw [ownerLink]
  rfl

theorem no_hazard_dependency : Cell.hazards ∉ dependencies := by decide

theorem canonical_ready : RegisterOperational.Ready raw canonical :=
  ready_of_complete _ (by intro k hk; rfl)

-- All three registered games remain accessible through the committed exact
-- game equivalences; this module changes only their raw component interpreter.
theorem registered_components :
    POS04OperationalGame.Autonomy baseline ∧ POS04FullGame.Autonomy baseline ∧
      POS04OperationalGame.Autonomy packageDeletion ∧
      ¬ POS04FullGame.Autonomy packageDeletion ∧
      ¬ POS04OperationalGame.Autonomy withdrawalDeletion :=
  ⟨POS04ExactGames.positive_games.2,POS04ExactGames.positive_games.1,
    POS04ExactGames.registered_game_vectors.1.2,POS04ExactGames.registered_game_vectors.1.1,
    POS04ExactGames.registered_game_vectors.2.2.2⟩

end CSTTT.TargetTheory.GenericHandoff.POS04RegisterOperational
