import CSTTT.Targets.GenericHandoff.RegisterInterpreter
import CSTTT.Targets.GenericHandoff.StrategyGame

/-! Polymorphic operational game COMPONENT, read from shared typed cells.
No semantic predicate, aggregate updater, safe set, or verdict is a raw field.
The response/resource/advancement predicates below interpret concrete raw
numbers, identifiers and rows. Context-dependent operations remain unrestricted.
Acquisition entries, six-role withdrawal, graded package rules and finite lift
are separate components; this is not yet an assembled RawHandoff certificate.
-/
namespace CSTTT.TargetTheory.GenericHandoff.RegisterOperational
open RegisterInterpreter

structure Finance where
  owner : CarrierId
  rechargeAvailable : Bool
  budget : Nat
  cost : Nat
  recharge : Nat

structure Schema (S A D O : Type) where
  factors : List S
  actions : List A
  disturbances : List D
  destination : O → Option S
  target : CarrierId
  budget : Nat
  cost : Nat
  recharge : Nat
  scale : Nat
  orderAdvance : Nat
  tickAdvance : Nat
  recordAdvance : Nat

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (S A D O Residue : Type) where
  row : Expr Cell Value R RV (D × A) (List (O × Nat))
  program : Program Cell Value R RV (D × A × O)
  finance : Expr Cell Value R RV Unit Finance
  factor : Expr Cell Value R RV Unit (Option S)
  order : Expr Cell Value R RV Unit Nat
  ticks : Expr Cell Value R RV Unit Nat
  writer : Expr Cell Value R RV Unit Bool
  record : Expr Cell Value R RV Unit Nat
  residue : Expr Cell Value R RV Unit Residue
  funded : Expr Cell Value R RV Unit Bool

variable {Cell R S A D O Residue : Type} {Value : Cell → Type} {RV : R → Type}

/-- Every consumed operation, including all update registers. No temporal
predictive/hazard dependency is smuggled into the operational schema. -/
def Ready (raw : Raw Cell Value R RV S A D O Residue) (a : Assignment Cell Value) : Prop :=
  Complete raw.row.dependencies a ∧ ProgramReady raw.program a ∧
  Complete (raw.finance.dependencies ++ raw.factor.dependencies ++ raw.order.dependencies ++
    raw.ticks.dependencies ++ raw.writer.dependencies ++ raw.record.dependencies ++
    raw.residue.dependencies ++ raw.funded.dependencies) a

noncomputable def update (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (h : Ready raw a)
    (r : Registers R RV) (d : D) (act : A) (o : O) : Registers R RV :=
  checkedExecute raw.program a h.2.1 r (d,act,o)

/-- A missing row is empty at the total helper level; the raw Ready gate
rejects it BEFORE this helper can support certification. -/
def rows (cfg : Schema S A D O) (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (r : Registers R RV) (d : D) (act : A) : List (O × Rat) :=
  ((raw.row.eval a r (d,act)).getD []).map fun e => (e.1,(e.2 : Rat)/(cfg.scale : Rat))

/-- Same-package-independent operational state safety. A named declared exit
is not hidden by a total projection or replaced by a representative. -/
def Inside (cfg : Schema S A D O) (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (r : Registers R RV) : Prop :=
  ∃ s ∈ cfg.factors, raw.factor.eval a r () = some (some s)

def FinanceValid (cfg : Schema S A D O) (f : Finance) : Prop :=
  f.owner = cfg.target ∧ f.rechargeAvailable = true ∧ f.budget ≥ f.cost ∧
  f.budget - f.cost + f.recharge > 0 ∧
  f.budget = cfg.budget ∧ f.cost = cfg.cost ∧ f.recharge = cfg.recharge ∧
  f.budget - f.cost + f.recharge = f.budget

/-- This prices ONE raw maintained ledger. Multiple ledger/resources can be
checked by conjunction of such decoded components; this module does not claim
that all generic resource interfaces have one ledger. -/
def ResourceClosed (cfg : Schema S A D O) (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (r : Registers R RV) : Prop :=
  (∃ f, raw.finance.eval a r () = some f ∧ FinanceValid cfg f) ∧
    raw.funded.eval a r () = some true ∧ raw.writer.eval a r () = some true

variable [DecidableEq S]
/-- Actual support, not a preferred branch. Normalization is also checked
separately by the strategy engine; no stored acceptance bit is consumed. -/
def Legal (cfg : Schema S A D O) (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (r : Registers R RV) (d : D) (act : A) : Prop :=
  d ∈ cfg.disturbances ∧ act ∈ cfg.actions ∧
  ∃ row, raw.row.eval a r (d,act) = some row ∧ row ≠ [] ∧
    (row.map Prod.snd).sum = cfg.scale ∧
    ∀ e ∈ row, e.2 > 0 ∧ ∃ s ∈ cfg.factors, cfg.destination e.1 = some s

/-- Interpreted step law: numeric increments are independent raw schema
parameters; the actual update is computed by the shared instruction program. -/
def StepLaw (cfg : Schema S A D O) (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (h : Ready raw a)
    (r : Registers R RV) (d : D) (act : A) (o : O) : Prop :=
  let next := update raw a h r d act o
  raw.funded.eval a next () = some true ∧
  cfg.orderAdvance > 0 ∧ cfg.tickAdvance > 0 ∧ cfg.recordAdvance > 0 ∧
  (∃ n, raw.order.eval a r () = some n ∧ raw.order.eval a next () = some (n + cfg.orderAdvance)) ∧
  (∃ n, raw.ticks.eval a r () = some n ∧ raw.ticks.eval a next () = some (n + cfg.tickAdvance)) ∧
  (∃ n, raw.record.eval a r () = some n ∧ raw.record.eval a next () = some (n + cfg.recordAdvance)) ∧
  raw.residue.eval a next () = raw.residue.eval a r () ∧
  (∃ f, raw.finance.eval a next () = some f ∧ f.owner = cfg.target)

/-- These arguments are internal interpretations for the game engine. The
RawHandoff boundary must DEFINE entries and withdrawal from its acquisition
and withdrawal cells. Neither is a field of `Raw`. -/
abbrev Certificate (cfg : Schema S A D O) (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (h : Ready raw a)
    (entries : Registers R RV → Prop) (withdrawal : Prop) :=
  StrategyGame.InvariantCertificate (rows cfg raw a) (update raw a h) entries withdrawal
    (Inside cfg raw a) (ResourceClosed cfg raw a) (Legal cfg raw a) (StepLaw cfg raw a h)

def OperationalReadout (cfg : Schema S A D O) (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (h : Ready raw a)
    (entries : Registers R RV → Prop) (withdrawal : Prop) : Prop :=
  cfg.disturbances ≠ [] ∧
  StrategyGame.GameReadout (rows cfg raw a) (update raw a h) entries withdrawal
    (Inside cfg raw a) (ResourceClosed cfg raw a) (Legal cfg raw a) (StepLaw cfg raw a h)

omit [DecidableEq S] in
theorem invariant_soundness (cfg : Schema S A D O) (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (h : Ready raw a)
    (entries : Registers R RV → Prop) (withdrawal : Prop) (hd : cfg.disturbances ≠ [])
    (cert : Certificate cfg raw a h entries withdrawal) :
    OperationalReadout cfg raw a h entries withdrawal :=
  ⟨hd,StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert⟩

omit [DecidableEq S] in
theorem empty_disturbance_rejected (cfg : Schema S A D O) (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (h : Ready raw a)
    (entries : Registers R RV → Prop) (withdrawal : Prop) (hd : cfg.disturbances = []) :
    ¬ OperationalReadout cfg raw a h entries withdrawal := fun ha => ha.1 hd

omit [DecidableEq S] in
theorem missing_row_rejected (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.row.dependencies) (hm : a k = none) :
    ¬ Ready raw a := by
  intro h
  have hc := h.1 k hk
  rw [hm] at hc
  contradiction

omit [DecidableEq S] in
theorem missing_update_rejected (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (r : R) (k : Cell) (hk : k ∈ (raw.program r).dependencies)
    (hm : a k = none) : ¬ Ready raw a := fun h => missing_program_rejected raw.program a r k hk hm h.2.1

omit [DecidableEq S] in
theorem missing_resource_rejected (raw : Raw Cell Value R RV S A D O Residue)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.finance.dependencies) (hm : a k = none)
    (r : Registers R RV) : ¬ ResourceClosed cfg raw a r := by
  rintro ⟨⟨f,hf,_⟩,_⟩
  rw [raw.finance.missing a k hk hm r ()] at hf
  contradiction

end CSTTT.TargetTheory.GenericHandoff.RegisterOperational
