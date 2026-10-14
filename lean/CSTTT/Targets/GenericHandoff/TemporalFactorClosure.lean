import CSTTT.Targets.GenericHandoff.TemporalFactorWords
import CSTTT.POS04.FutureDynamics

/-! Closure-wide laws for the defined finite constructor. The closure is
computed from raw route tuples, initial funding and actual outcome updates.
Counter/readout laws hold on every run; acceptance derives strictly positive
conserved maintenance and endogenous record growth throughout this closure.
The unrestricted hybrid interpreter still needs its own proved per-instance
simulation; this constructor does not assume arbitrary recipes factor. -/
namespace CSTTT.TargetTheory.GenericHandoff.TemporalFactorRules
open CSTTT.TransportTheory
variable {S A O H RouteId Stage Id Owner : Type}
  [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner]

def roots (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : List (Run O S Id) :=
  cfg.routes.flatMap fun rid => match registerTuple d rid with
  | none => []
  | some residue => (cfg.base.outcomes.filter (fun o => (cfg.base.destination o).isSome)).map
      (fun o => ⟨o,0,0,residue,d.receiverFunded⟩)

def dynamics (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : RawFutureDynamics (Run O S Id) A O :=
  ⟨cfg.base.outcomes,weight cfg d,update cfg d⟩
abbrev Closure (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) :=
  FutureClosure (dynamics cfg d) (roots cfg d)

/-- Every evolving field has an independent raw update equation. Progress,
record and maintenance growth are derived below from acceptance, not merely
from these unconditional algebraic identities. -/
structure UpdateLaws (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (period : Nat) (x : Run O S Id) (a : A) (o : O) : Prop where
  factor : (update cfg d x a o).factor = o
  predictive : (observe cfg d period (update cfg d x a o)).predictive = prediction cfg d o
  order : (observe cfg d period (update cfg d x a o)).order = x.counter + cfg.stageAdvance
  tick : (observe cfg d period (update cfg d x a o)).tickPhase = (x.ticks + delta cfg d x.factor a) % period
  progress : (observe cfg d period (update cfg d x a o)).progress = x.counter + cfg.stageAdvance
  writer : writer cfg d (update cfg d x a o).residue = writer cfg d x.residue
  record : (observe cfg d period (update cfg d x a o)).record =
    if (x.funded && decide (budgetAfter d > 0)) && TemporalFactorRules.writer cfg d x.residue then x.counter + cfg.stageAdvance else 0
  residue : (update cfg d x a o).residue = x.residue
  maintenance : (update cfg d x a o).funded = (x.funded && decide (budgetAfter d > 0))
  owner : (observe cfg d period (update cfg d x a o)).owner = d.resource.owner
  enabled : enabled d (update cfg d x a o) =
    ((x.funded && decide (budgetAfter d > 0)) && d.resource.rechargeAvailable && decide (d.ledger.initial ≥ d.ledger.cost))

omit [DecidableEq O] [DecidableEq Stage] [DecidableEq Owner] in
theorem update_laws (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (period : Nat) (x : Run O S Id) (a : A) (o : O) : UpdateLaws cfg d period x a o :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def ClosureLaws (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) (period : Nat) : Prop :=
  ∀ x, Closure cfg d x → ∀ a o, UpdateLaws cfg d period x a o

omit [DecidableEq Stage] [DecidableEq Owner] in
theorem closure_laws (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (period : Nat) : ClosureLaws cfg d period := fun x _ a o => update_laws cfg d period x a o

omit [DecidableEq Owner] in
theorem accepted_writer (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (h : Accept cfg d) (rid : RouteId) (hr : rid ∈ cfg.routes) (residue : List S × List Id)
    (ht : registerTuple d rid = some residue) : writer cfg d residue = true := by
  have hall := (Bool.and_eq_true_iff.mp h.2.2.2.2.2.1.2.2.2.2.1).2
  have hsome : (cfg.routes.find? (fun r => decide (registerTuple d r = some residue))).isSome = true :=
    List.find?_isSome.mpr ⟨rid,hr,by simp [ht]⟩
  cases he : cfg.routes.find? (fun r => decide (registerTuple d r = some residue)) with
  | none => simp [he] at hsome
  | some r =>
    change Option.any d.writers (cfg.routes.find? _) = true
    rw [he]
    exact List.all_eq_true.mp hall r (List.mem_of_find?_eq_some he)

omit [DecidableEq Owner] in
theorem accepted_funded_writer (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (h : Accept cfg d) (x : Run O S Id) (hx : Closure cfg d x) :
    x.funded = true ∧ writer cfg d x.residue = true := by
  have hfund := h.2.2.2.2.2.2.1
  have hbudget : budgetAfter d > 0 := by unfold budgetAfter; rw [hfund.2.2.2.2]; exact hfund.2.2.2.1
  induction hx with
  | root x hm =>
    obtain ⟨rid,hr,hx⟩ := List.mem_flatMap.mp hm
    cases ht : registerTuple d rid with
    | none => simp [ht] at hx
    | some residue =>
      simp only [ht] at hx
      obtain ⟨o,_,ho⟩ := List.mem_map.mp hx
      subst x
      exact ⟨h.2.2.2.2.2.1.1,accepted_writer cfg d h rid hr residue ht⟩
  | step hx a o ho ih =>
    refine ⟨?_,ih.2⟩
    simp only [dynamics,update,ih.1,decide_eq_true hbudget,Bool.true_and]

omit [DecidableEq Owner] in
theorem accepted_advancement (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (period : Nat) (h : Accept cfg d) (x : Run O S Id) (hx : Closure cfg d x) (a : A) (o : O) :
    budgetAfter d = d.ledger.initial ∧ budgetAfter d > 0 ∧
    (update cfg d x a o).funded = true ∧
    (observe cfg d period (update cfg d x a o)).progress > (observe cfg d period x).progress ∧
    (observe cfg d period (update cfg d x a o)).record = (observe cfg d period x).record + cfg.stageAdvance := by
  have hf := accepted_funded_writer cfg d h x hx
  have hc := h.2.2.2.2.2.2.1
  have hp : budgetAfter d > 0 := by unfold budgetAfter; rw [hc.2.2.2.2]; exact hc.2.2.2.1
  refine ⟨hc.2.2.2.2,hp,?_,?_,?_⟩
  · simp only [update,hf.1,decide_eq_true hp,Bool.true_and]
  · change x.counter + cfg.stageAdvance > x.counter
    exact Nat.lt_add_of_pos_right h.2.1
  · simp only [observe,update,hf.1,hf.2,decide_eq_true hp,Bool.true_and,if_true]

omit [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner] in
/-- A strict predictive merge cannot consist of two external, fully exposed
outcomes. Both raw destinations must be active. -/
theorem coarse_active (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (h : Coarser cfg d) : (cfg.base.destination cfg.coarsePair.1).isSome = true ∧
      (cfg.base.destination cfg.coarsePair.2).isSome = true := by
  have hp := h.2
  cases he : cfg.base.destination cfg.coarsePair.1 <;> cases hf : cfg.base.destination cfg.coarsePair.2
  all_goals simp only [prediction,he,hf] at hp
  all_goals first | exact ⟨rfl,rfl⟩ | contradiction | exact (h.1 (Sum.inr.inj hp)).elim

omit [DecidableEq Owner] in
/-- The coarseness witness is realized at genuine decoded roots, so neither
future sufficiency nor the closure law is justified by an empty audit domain. -/
theorem accepted_coarse_roots (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (period : Nat) (h : Accept cfg d) :
    ∃ x ∈ roots cfg d, ∃ y ∈ roots cfg d, x ≠ y ∧ code cfg d period x = code cfg d period y := by
  have hw := Bool.and_eq_true_iff.mp h.2.2.2.2.2.1.2.2.2.2.1
  obtain ⟨rid,hr⟩ : ∃ rid, rid ∈ cfg.routes := by
    cases he : cfg.routes with
    | nil => simp [he] at hw
    | cons r rs => exact ⟨r,by simp⟩
  have hp := h.2.2.2.2.2.1.2.2.2.2.2.1
  have hrp : path cfg d rid = true :=
    List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hp).1).1).2 rid hr
  cases he : route d rid with
  | none => simp [path,he] at hrp
  | some r =>
    let res := (d.histories r.history,r.eventPath)
    have ht : registerTuple d rid = some res := by simp [registerTuple,he,res]
    have hco := h.2.2.2.2.2.2.2.2.2
    have hd := coarse_active cfg d hco
    let x : Run O S Id := ⟨cfg.coarsePair.1,0,0,res,d.receiverFunded⟩
    let y : Run O S Id := ⟨cfg.coarsePair.2,0,0,res,d.receiverFunded⟩
    have root (o : O) (ha : (cfg.base.destination o).isSome = true) :
        (⟨o,0,0,res,d.receiverFunded⟩ : Run O S Id) ∈ roots cfg d := by
      apply List.mem_flatMap.mpr
      refine ⟨rid,hr,?_⟩
      simp only [ht]
      apply List.mem_map.mpr
      exact ⟨o,List.mem_filter.mpr ⟨h.1.2.2.2.2.2 o,ha⟩,rfl⟩
    refine ⟨x,root _ hd.1,y,root _ hd.2,?_,?_⟩
    · intro heq; exact hco.1 (congrArg Run.factor heq)
    · simp only [code,x,y,hco.2]

omit [DecidableEq S] [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner] in
/-- Candidate updaters are proposals only: an actual closure-state mismatch
in ANY projection rejects equality with the defined updater. They are never
arguments of the accepted constructor or of its future-sufficiency theorem. -/
theorem update_proposal_guard {X : Type}
    (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (proposed : Run O S Id → A → O → Run O S Id) (field : Run O S Id → X)
    (x : Run O S Id) (hx : Closure cfg d x) (a : A) (o : O)
    (bad : field (proposed x a o) ≠ field (update cfg d x a o)) :
    ¬ (∀ y, Closure cfg d y → ∀ act outcome, proposed y act outcome = update cfg d y act outcome) :=
  fun h => bad (congrArg field (h x hx a o))

end CSTTT.TargetTheory.GenericHandoff.TemporalFactorRules
