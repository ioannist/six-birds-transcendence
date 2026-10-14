import CSTTT.Targets.GenericHandoff.RegisterInterpreter
import CSTTT.Targets.GenericHandoff.StrategyGame

/-! G6d resource extraction, design §1.5 and hybrid addendum.
Resources, prices, credits, required support and advancement may depend on the
entire unbounded run. There is no conserved-budget or finite-context premise.
Every semantic relation interprets raw instructions on one shared assignment.
Only auxiliary invariant/strategy evidence is supplied. Acquisition and package
interpretation are separate components, not predicate fields of Raw below. -/
namespace CSTTT.TargetTheory.GenericHandoff.ResourceRuntime
open RegisterInterpreter

inductive Role where
  | source | migrationBridge | migrationController | externalDecoder
  | externalScheduler | undeclaredRepair
  deriving DecidableEq

def roles : List Role := [.source,.migrationBridge,.migrationController,
  .externalDecoder,.externalScheduler,.undeclaredRepair]

structure Account where
  owner : Option CarrierId
  retained : Bool
  balance : Nat

structure Charge (Resource : Type) where
  owner : CarrierId
  used : List Resource
  debit : Resource → Nat
  credit : Resource → Nat

structure Advances where
  order : Nat
  ticks : Nat
  progress : Nat
  record : Nat

structure Withdrawal (Resource : Type) where
  removedRoles : List Role
  roleResources : Role → List Resource
  removed : List Resource
  retained : List Resource

/-- One shared execution table and instruction program. Temporal and resource
interpretations must refer to this SAME object at the enclosing boundary. -/
structure Execution (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O : Type) where
  disturbances : List D
  actions : List A
  outcomes : List O
  row : Expr Cell Value R RV (D × A) (List (O × Rat))
  program : Program Cell Value R RV (D × A × O)

structure Schema (Factor Resource : Type) where
  factors : List Factor
  resources : List Resource
  source : CarrierId
  target : CarrierId

structure Bindings (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O Factor Resource Residue : Type) where
  accounts : Expr Cell Value R RV Unit (Resource → Account)
  required : Expr Cell Value R RV Unit (List Resource)
  charge : Expr Cell Value R RV (D × A) (Charge Resource)
  advances : Expr Cell Value R RV (D × A × O) Advances
  factor : Expr Cell Value R RV Unit (Option Factor)
  order : Expr Cell Value R RV Unit Nat
  ticks : Expr Cell Value R RV Unit Nat
  progress : Expr Cell Value R RV Unit Nat
  record : Expr Cell Value R RV Unit Nat
  writer : Expr Cell Value R RV Unit Bool
  residue : Expr Cell Value R RV Unit Residue
  sourcePresent : Expr Cell Value R RV Unit Bool
  withdrawal : CellView Cell Value (Withdrawal Resource)

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O Factor Resource Residue : Type)
    extends Bindings Cell Value R RV D A O Factor Resource Residue where
  execution : Execution Cell Value R RV D A O

variable {Cell R D A O Factor Resource Residue : Type}
    {Value : Cell → Type} {RV : R → Type}

def Raw.readDependencies (raw : Raw Cell Value R RV D A O Factor Resource Residue) : List Cell :=
  raw.accounts.dependencies ++ raw.required.dependencies ++ raw.charge.dependencies ++
  raw.advances.dependencies ++ raw.factor.dependencies ++ raw.order.dependencies ++
  raw.ticks.dependencies ++ raw.progress.dependencies ++ raw.record.dependencies ++
  raw.writer.dependencies ++ raw.residue.dependencies ++ raw.sourcePresent.dependencies ++
  [raw.withdrawal.cell]

def Ready (raw : Raw Cell Value R RV D A O Factor Resource Residue) (a : Assignment Cell Value) : Prop :=
  Complete raw.execution.row.dependencies a ∧ ProgramReady raw.execution.program a ∧
  Complete raw.readDependencies a

noncomputable def update (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (r : Registers R RV) (d : D) (act : A) (o : O) : Registers R RV :=
  checkedExecute raw.execution.program a h.2.1 r (d,act,o)

/-- Empty helper rows cannot bypass Ready; there is no arbitrary probability
scale or restriction to the POS-04 quarters. -/
def rows (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : Registers R RV) (d : D) (act : A) : List (O × Rat) :=
  (raw.execution.row.eval a r (d,act)).getD []

def Inside (cfg : Schema Factor Resource) (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : Registers R RV) : Prop :=
  ∃ s ∈ cfg.factors, raw.factor.eval a r () = some (some s)

def DomainCheck (cfg : Schema Factor Resource) (raw : Raw Cell Value R RV D A O Factor Resource Residue) : Prop :=
  cfg.factors ≠ [] ∧ cfg.resources ≠ [] ∧
  raw.execution.disturbances ≠ [] ∧
  (∀ d, d ∈ raw.execution.disturbances) ∧ (∀ act, act ∈ raw.execution.actions) ∧
  (∀ o, o ∈ raw.execution.outcomes) ∧ (∀ s, s ∈ cfg.factors) ∧ (∀ res, res ∈ cfg.resources)

/-- All six declared roles, actual removed/retained disjointness, and source
absence. Removed accounts are inspected again at EACH state by ResourceClosed. -/
def WithdrawalCheck (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) : Prop :=
  ∃ w, raw.withdrawal.read a = some w ∧
    (∀ role ∈ roles, role ∈ w.removedRoles) ∧
    (∀ role ∈ w.removedRoles, role ∈ roles) ∧
    (∀ role ∈ roles, w.roleResources role ⊆ w.removed) ∧
    w.removed ⊆ cfg.resources ∧ w.retained ⊆ cfg.resources ∧
    (∀ res ∈ w.removed, res ∉ w.retained)

/-- Needed resources and their prices are interpreted, not certificates.
The removed role accounts stay absent on the run space. Package resources
remain target-owned; historical acquisition is not post-withdrawal support. -/
def ResourceClosed (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : Registers R RV) : Prop :=
  ∃ accounts required w,
    raw.accounts.eval a r () = some accounts ∧ raw.required.eval a r () = some required ∧
    raw.withdrawal.read a = some w ∧ raw.sourcePresent.eval a r () = some false ∧
    raw.writer.eval a r () = some true ∧ required ≠ [] ∧ required ⊆ w.retained ∧
    (∀ res ∈ required, (accounts res).owner = some cfg.target ∧
      (accounts res).retained = true ∧ (accounts res).balance > 0) ∧
    (∀ res ∈ w.removed, (accounts res).retained = false)

def Legal (cfg : Schema Factor Resource) (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : Registers R RV) (d : D) (act : A) : Prop :=
  d ∈ raw.execution.disturbances ∧ act ∈ raw.execution.actions ∧
  ∃ accounts needed charge w,
    raw.accounts.eval a r () = some accounts ∧ raw.required.eval a r () = some needed ∧
    raw.charge.eval a r (d,act) = some charge ∧ raw.withdrawal.read a = some w ∧ charge.owner = cfg.target ∧
    charge.used ≠ [] ∧ needed ⊆ charge.used ∧ charge.used ⊆ w.retained ∧ charge.used ⊆ cfg.resources ∧
    (∀ res ∈ charge.used, (accounts res).owner = some cfg.target ∧
      (accounts res).retained = true ∧ charge.debit res ≤ (accounts res).balance ∧
      (accounts res).balance - charge.debit res + charge.credit res > 0)

/-- Solvency and growth are checked against the ACTUAL updater. Neither
ledger conservation nor independence from omitted run context is assumed. -/
def StepLaw (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (r : Registers R RV) (d : D) (act : A) (o : O) : Prop :=
  let next := update raw a h r d act o
  ResourceClosed cfg raw a next ∧
  ∃ before after charge advance order ticks progress record,
    raw.accounts.eval a r () = some before ∧ raw.accounts.eval a next () = some after ∧
    raw.charge.eval a r (d,act) = some charge ∧ raw.advances.eval a r (d,act,o) = some advance ∧
    advance.order > 0 ∧ advance.ticks > 0 ∧ advance.progress > 0 ∧ advance.record > 0 ∧
    (∀ res ∈ charge.used, (after res).balance = (before res).balance - charge.debit res + charge.credit res) ∧
    raw.order.eval a r () = some order ∧ raw.order.eval a next () = some (order + advance.order) ∧
    raw.ticks.eval a r () = some ticks ∧ raw.ticks.eval a next () = some (ticks + advance.ticks) ∧
    raw.progress.eval a r () = some progress ∧ raw.progress.eval a next () = some (progress + advance.progress) ∧
    raw.record.eval a r () = some record ∧ raw.record.eval a next () = some (record + advance.record) ∧
    raw.residue.eval a next () = raw.residue.eval a r ()

/-- Internal strategy-engine interpretation: the enclosing acquisition
component MUST DEFINE entries. Package parameters here are internal engine
relations, not fields of Raw or supplied verdicts at a RawHandoff boundary. -/
abbrev Certificate (cfg : Schema Factor Resource) (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (entries : Registers R RV → Prop) :=
  StrategyGame.InvariantCertificate (rows raw a) (update raw a h) entries
    (DomainCheck cfg raw ∧ WithdrawalCheck cfg raw a) (Inside cfg raw a)
    (ResourceClosed cfg raw a) (Legal cfg raw a) (StepLaw cfg raw a h)

def OperationalReadout (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (entries : Registers R RV → Prop) : Prop :=
  StrategyGame.GameReadout (rows raw a) (update raw a h) entries
    (DomainCheck cfg raw ∧ WithdrawalCheck cfg raw a) (Inside cfg raw a)
    (ResourceClosed cfg raw a) (Legal cfg raw a) (StepLaw cfg raw a h)

theorem soundness (cfg : Schema Factor Resource) (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (entries : Registers R RV → Prop)
    (cert : Certificate cfg raw a h entries) : OperationalReadout cfg raw a h entries :=
  StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert

/-- Per-field missing-input rejection, BEFORE decoder totalization. -/
theorem missing_read_rejected (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.readDependencies) (hm : a k = none) : ¬ Ready raw a := by
  intro h
  have hp := h.2.2 k hk
  rw [hm] at hp
  contradiction

theorem missing_row_rejected (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.execution.row.dependencies) (hm : a k = none) : ¬ Ready raw a := by
  intro h
  have hp := h.1 k hk
  rw [hm] at hp
  contradiction

theorem missing_update_rejected (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : R) (k : Cell) (hk : k ∈ (raw.execution.program r).dependencies)
    (hm : a k = none) : ¬ Ready raw a :=
  fun h => missing_program_rejected raw.execution.program a r k hk hm h.2.1

theorem rows_locality (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    {a b : Assignment Cell Value} (he : Agrees raw.execution.row.dependencies a b)
    (r : Registers R RV) (d : D) (act : A) : rows raw a r d act = rows raw b r d act := by
  simp only [rows,raw.execution.row.locality he r (d,act)]

theorem update_locality (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    {a b : Assignment Cell Value} (ha : Ready raw a) (hb : Ready raw b)
    (he : ∀ reg, Agrees (raw.execution.program reg).dependencies a b)
    (r : Registers R RV) (d : D) (act : A) (o : O) :
    update raw a ha r d act o = update raw b hb r d act o := by
  funext reg
  apply Option.some.inj
  unfold update
  rw [← checked_execute_eq raw.execution.program a ha.2.1 r (d,act,o) reg,
      ← checked_execute_eq raw.execution.program b hb.2.1 r (d,act,o) reg]
  exact congrFun (execute_locality raw.execution.program he r (d,act,o)) reg

theorem resource_locality (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    {a b : Assignment Cell Value} (he : Agrees raw.readDependencies a b) (r : Registers R RV) :
    ResourceClosed cfg raw a r ↔ ResourceClosed cfg raw b r := by
  have accounts := raw.accounts.locality (fun k hk => he k (by simp [Raw.readDependencies,hk])) r ()
  have required := raw.required.locality (fun k hk => he k (by simp [Raw.readDependencies,hk])) r ()
  have withdrawn := view_locality raw.withdrawal (he _ (by simp [Raw.readDependencies]))
  have source := raw.sourcePresent.locality (fun k hk => he k (by simp [Raw.readDependencies,hk])) r ()
  have writer := raw.writer.locality (fun k hk => he k (by simp [Raw.readDependencies,hk])) r ()
  simp only [ResourceClosed,accounts,required,withdrawn,source,writer]

theorem source_present_rejected (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : Registers R RV) (he : raw.sourcePresent.eval a r () = some true) :
    ¬ ResourceClosed cfg raw a r := by
  rintro ⟨_,_,_,_,_,_,hn,_⟩
  rw [he] at hn
  contradiction

theorem missing_required_rejected (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : Registers R RV) (he : raw.required.eval a r () = some []) :
    ¬ ResourceClosed cfg raw a r := by
  rintro ⟨_,required,_,_,hh,_,_,_,hn,_⟩
  have hreq : required = [] := Option.some.inj (hh.symm.trans he)
  exact hn hreq

theorem empty_disturbances_rejected (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (entries : Registers R RV → Prop)
    (he : raw.execution.disturbances = []) : ¬ OperationalReadout cfg raw a h entries :=
  fun ha => ha.1.1.2.2.1 he

inductive GrowthField where | order | ticks | progress | record
  deriving DecidableEq

def growthRead (raw : Raw Cell Value R RV D A O Factor Resource Residue) :
    GrowthField → Expr Cell Value R RV Unit Nat
  | .order => raw.order
  | .ticks => raw.ticks
  | .progress => raw.progress
  | .record => raw.record

/-- Advancement is a CONSEQUENCE of the exact updater/price equations, not
an independent strictness field or a caller's claimed game result. -/
theorem step_advances (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (r : Registers R RV) (d : D) (act : A) (o : O)
    (hs : StepLaw cfg raw a h r d act o) (f : GrowthField) :
    ∃ before after : Nat, (growthRead raw f).eval a r () = some before ∧
      (growthRead raw f).eval a (update raw a h r d act o) () = some after ∧ before < after := by
  rcases hs with ⟨_,before,after,charge,advance,ord,ticks,progress,record,
    _,_,_,_,ho,ht,hp,hr,_,heo,hen,het,hetn,hep,hepn,her,hern,_⟩
  cases f with
  | order => exact ⟨ord,ord+advance.order,heo,hen,by omega⟩
  | ticks => exact ⟨ticks,ticks+advance.ticks,het,hetn,by omega⟩
  | progress => exact ⟨progress,progress+advance.progress,hep,hepn,by omega⟩
  | record => exact ⟨record,record+advance.record,her,hern,by omega⟩

/-- Per-field constant/capped guard for ALL four evolving counters. This
applies at any reached run: a capped progress or record readout cannot hide
behind equal-code bisimulation. -/
theorem nonadvancing_field_rejected (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (r : Registers R RV) (d : D) (act : A) (o : O)
    (f : GrowthField) (before after : Nat)
    (hb : (growthRead raw f).eval a r () = some before)
    (hn : (growthRead raw f).eval a (update raw a h r d act o) () = some after)
    (bad : after ≤ before) : ¬ StepLaw cfg raw a h r d act o := by
  intro hs
  obtain ⟨old,new,he,he',hlt⟩ := step_advances cfg raw a h r d act o hs f
  have hx := Option.some.inj (he.symm.trans hb)
  have hy := Option.some.inj (he'.symm.trans hn)
  omega

theorem wrong_response_owner_rejected (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : Registers R RV) (d : D) (act : A)
    (charge : Charge Resource) (hc : raw.charge.eval a r (d,act) = some charge)
    (bad : charge.owner ≠ cfg.target) : ¬ Legal cfg raw a r d act := by
  rintro ⟨_,_,_,_,c,_,_,_,he,_,ho,_⟩
  have hce := Option.some.inj (he.symm.trans hc)
  subst c
  exact bad ho

theorem depleted_required_rejected (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : Registers R RV)
    (accounts : Resource → Account) (required : List Resource)
    (ha : raw.accounts.eval a r () = some accounts) (hr : raw.required.eval a r () = some required)
    (res : Resource) (hin : res ∈ required) (bad : (accounts res).balance = 0) :
    ¬ ResourceClosed cfg raw a r := by
  rintro ⟨acs,req,_,he,he',_,_,_,_,_,hs,_⟩
  have hx := Option.some.inj (he.symm.trans ha)
  have hy := Option.some.inj (he'.symm.trans hr)
  subst acs; subst req
  have hp := (hs res hin).2.2
  omega

theorem writer_unavailable_rejected (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (r : Registers R RV)
    (bad : raw.writer.eval a r () = some false) : ¬ ResourceClosed cfg raw a r := by
  rintro ⟨_,_,_,_,_,_,_,he,_⟩
  rw [bad] at he
  contradiction

theorem changed_residue_rejected (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (r : Registers R RV) (d : D) (act : A) (o : O)
    (bad : raw.residue.eval a (update raw a h r d act o) () ≠ raw.residue.eval a r ()) :
    ¬ StepLaw cfg raw a h r d act o := by
  intro hs
  rcases hs.2 with ⟨_,_,_,_,_,_,_,_,hf⟩
  exact bad hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Every generated play meets the raw resource and advancement laws; the
closure here is the actual strategy closure, not an audited-prefix bound. -/
theorem game_growth (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    (a : Assignment Cell Value) (h : Ready raw a) (entries : Registers R RV → Prop)
    (hg : OperationalReadout cfg raw a h entries) :
    ∃ strategy : StrategyGame.Strategy (Registers R RV) D A,
      ∀ entry, entries entry → ∀ r past,
        StrategyGame.Play (rows raw a) (update raw a h) strategy entry (r::past) →
        ∀ d o, StrategyGame.PositiveSupport (rows raw a) r d (strategy (r::past) d) o →
          ∀ f : GrowthField, ∃ before after : Nat,
            (growthRead raw f).eval a r () = some before ∧
            (growthRead raw f).eval a (update raw a h r d (strategy (r::past) d) o) () = some after ∧
            before < after := by
  obtain ⟨_,_,strategy,hs⟩ := hg
  refine ⟨strategy,?_⟩
  intro entry he r past hp d o ho f
  exact step_advances cfg raw a h r d _ o (((hs entry he r past hp).2.2 d).2.2 o ho) f

end CSTTT.TargetTheory.GenericHandoff.ResourceRuntime
