import CSTTT.Targets.GenericHandoff.RegisterFuture
import CSTTT.Targets.GenericHandoff.StrategyGame

/-! Every evolving readout is checked against its separately declared raw
step instruction throughout the computed closure. Positive advancement is
checked on the numerical RIGHT-HAND-SIDE recipes, and transported through the
update equations. No strictness proof is stored in raw data. The raw equations
and unrestricted recipe operations are semantic checks, not finite decidability
or an automatic finite-context assertion. -/
namespace CSTTT.TargetTheory.GenericHandoff.RegisterFuture
open RegisterInterpreter CSTTT.TransportTheory

inductive Field where
  | predictive | order | ticks | progress | writer | record | residue | maintenance | owner
  deriving DecidableEq

def FieldValue (P Residue Maintenance : Type) : Field → Type
  | .predictive => P
  | .order | .ticks | .progress | .record => Nat
  | .writer => Bool
  | .residue => Residue
  | .maintenance => Maintenance
  | .owner => CarrierId

variable {Cell R D A O P Residue Maintenance : Type}
  {Value : Cell → Type} {RV : R → Type}

def fieldExpr (r : Readouts Cell Value R RV P Residue Maintenance) :
    (f : Field) → Expr Cell Value R RV Unit (FieldValue P Residue Maintenance f)
  | .predictive => r.predictive
  | .order => r.order
  | .ticks => r.ticks
  | .progress => r.progress
  | .writer => r.writer
  | .record => r.record
  | .residue => r.residue
  | .maintenance => r.maintenance
  | .owner => r.owner

/-- Raw step-law instruction syntax, independent of the actual readout
instruction. These are typed arithmetic/table instructions, not Prop fields. -/
abbrev StepRecipes (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O P Residue Maintenance : Type) :=
  (f : Field) → Expr Cell Value R RV (D × A × O) (FieldValue P Residue Maintenance f)

variable [DecidableEq O]

def FieldLaw (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a)
    (run : Registers R RV) (da : D × A) (o : O) (f : Field) : Prop :=
  (fieldExpr raw.readouts f).eval a (next raw a h run da o) () =
    (law f).eval a run (da.1,da.2,o)

/-- Inspect the independent numeric recipes, before deriving growth of the
actual readouts. Missing RHS inputs cannot supply a growth witness. -/
def PositiveRecipes (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a)
    (run : Registers R RV) (da : D × A) (o : O) : Prop :=
  ∃ order ticks progress record : Nat,
    (law .order).eval a run (da.1,da.2,o) = some order ∧
    (law .ticks).eval a run (da.1,da.2,o) = some ticks ∧
    (law .progress).eval a run (da.1,da.2,o) = some progress ∧
    (law .record).eval a run (da.1,da.2,o) = some record ∧
    (observation raw a h run).order < order ∧
    (raw.readouts.ticks.eval a run ()).any (· < ticks) = true ∧
    (observation raw a h run).progress < progress ∧
    (observation raw a h run).record < record

/-- Read raw listed support, not only weights summed over the advertised
outcome domain. An omitted positive branch must not truncate the closure. -/
def ReadoutSupportCoverage (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV)) : Prop :=
  ∀ run, Closure raw a h roots run → ∀ d ∈ raw.disturbances, ∀ act ∈ raw.actions,
    ∀ o, StrategyGame.PositiveSupport (fun r d act => row raw a h r (d,act)) run d act o →
      o ∈ raw.outcomes

def ReadoutLawGate (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV)) : Prop :=
  raw.disturbances ≠ [] ∧ raw.actions ≠ [] ∧ raw.outcomes.Nodup ∧ raw.tickPeriod > 0 ∧ roots ≠ [] ∧
  (∀ run, Closure raw a h roots run → ∀ d ∈ raw.disturbances, ∀ act ∈ raw.actions,
    ∀ o ∈ raw.outcomes,
      (∀ f, FieldLaw raw law a h run (d,act) o f) ∧
      (weight raw a h run (d,act) o > 0 → PositiveRecipes raw law a h run (d,act) o)) ∧
  ReadoutSupportCoverage raw a h roots

theorem omitted_support_rejects_readout_gate (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV))
    (run : Registers R RV) (hr : Closure raw a h roots run)
    (d : D) (hd : d ∈ raw.disturbances) (act : A) (ha : act ∈ raw.actions) (o : O)
    (hp : StrategyGame.PositiveSupport (fun r d act => row raw a h r (d,act)) run d act o)
    (missing : o ∉ raw.outcomes) : ¬ ReadoutLawGate raw law a h roots :=
  fun gate => missing (gate.2.2.2.2.2.2 run hr d hd act ha o hp)

/-- Closure coverage now follows for every actual positive raw branch. The
declared list is a checked cover, not a filter that can discard successors. -/
theorem positive_branch_in_closure (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV))
    (gate : ReadoutLawGate raw law a h roots) (run : Registers R RV)
    (hr : Closure raw a h roots run) (d : D) (hd : d ∈ raw.disturbances)
    (act : A) (ha : act ∈ raw.actions) (o : O)
    (hp : StrategyGame.PositiveSupport (fun r d act => row raw a h r (d,act)) run d act o) :
    Closure raw a h roots (next raw a h run (d,act) o) :=
  FutureClosure.step hr (d,act) o (gate.2.2.2.2.2.2 run hr d hd act ha o hp)

/-- Uniform per-field sensitivity guard, including writer/owner/resource and
residue fields. A law mismatch on ANY reached state rejects the gate. -/
theorem field_guard (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV))
    (run : Registers R RV) (hr : Closure raw a h roots run)
    (d : D) (hd : d ∈ raw.disturbances) (act : A) (ha : act ∈ raw.actions)
    (o : O) (ho : o ∈ raw.outcomes) (f : Field)
    (bad : ¬ FieldLaw raw law a h run (d,act) o f) : ¬ ReadoutLawGate raw law a h roots :=
  fun gate => bad ((gate.2.2.2.2.2.1 run hr d hd act ha o ho).1 f)

/-- A consumed RHS primitive cannot be missing while its readout is present. -/
theorem missing_rhs_guard (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV))
    (run : Registers R RV) (hr : Closure raw a h roots run)
    (d : D) (hd : d ∈ raw.disturbances) (act : A) (ha : act ∈ raw.actions)
    (o : O) (ho : o ∈ raw.outcomes) (f : Field) (k : Cell)
    (hk : k ∈ (law f).dependencies) (hm : a k = none) : ¬ ReadoutLawGate raw law a h roots := by
  apply field_guard raw law a h roots run hr d hd act ha o ho f
  intro he
  have hn := (law f).missing a k hk hm run (d,act,o)
  have hf : Complete (fieldExpr raw.readouts f).dependencies a := by
    apply subready h.2.2
    intro j hj
    cases f <;> simp only [fieldExpr] at hj <;> simp [Readouts.dependencies,hj]
  obtain ⟨v,hv⟩ := (fieldExpr raw.readouts f).present_of_complete a hf (next raw a h run (d,act) o) ()
  unfold FieldLaw at he
  rw [hv,hn] at he
  contradiction

/-- Only one readout instruction changes; rows and the entire register updater
remain byte-for-byte the same raw instructions. -/
def Readouts.replace (r : Readouts Cell Value R RV P Residue Maintenance) (f : Field)
    (e : Expr Cell Value R RV Unit (FieldValue P Residue Maintenance f)) :
    Readouts Cell Value R RV P Residue Maintenance := match f with
  | .predictive => {r with predictive := e}
  | .order => {r with order := e}
  | .ticks => {r with ticks := e}
  | .progress => {r with progress := e}
  | .writer => {r with writer := e}
  | .record => {r with record := e}
  | .residue => {r with residue := e}
  | .maintenance => {r with maintenance := e}
  | .owner => {r with owner := e}

theorem replacement_field (r : Readouts Cell Value R RV P Residue Maintenance) (f : Field)
    (e : Expr Cell Value R RV Unit (FieldValue P Residue Maintenance f)) :
    fieldExpr (r.replace f e) f = e := by cases f <;> rfl

def replaceReadout (raw : Raw Cell Value R RV D A O P Residue Maintenance) (f : Field)
    (e : Expr Cell Value R RV Unit (FieldValue P Residue Maintenance f)) :=
  {raw with readouts := raw.readouts.replace f e}

/-- A genuine one-field perturbation leaves EVERY supported branch, updater
and closure unchanged. No candidate future is accepted beside these data. -/
theorem readout_closure_eq (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (f : Field)
    (e : Expr Cell Value R RV Unit (FieldValue P Residue Maintenance f))
    (hnew : RawReady (replaceReadout raw f e) a) (roots : List (Registers R RV)) (r : Registers R RV) :
    Closure (replaceReadout raw f e) a hnew roots r ↔ Closure raw a h roots r := Iff.rfl

/-- Parameterized constant guard for EVERY readout field. Its premise identifies
an independently computed RHS value that the proposed constant gets wrong.
No claim is made that an intrinsically constant lawful owner must vary. -/
theorem constant_field_guard (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV))
    (run : Registers R RV) (hr : Closure raw a h roots run)
    (d : D) (hd : d ∈ raw.disturbances) (act : A) (ha : act ∈ raw.actions)
    (o : O) (ho : o ∈ raw.outcomes) (f : Field)
    (expected wrong : FieldValue P Residue Maintenance f)
    (rhs : (law f).eval a run (d,act,o) = some expected) (hne : wrong ≠ expected)
    (hnew : RawReady (replaceReadout raw f (.literal wrong)) a) :
    ¬ ReadoutLawGate (replaceReadout raw f (.literal wrong)) law a hnew roots := by
  apply field_guard _ law a hnew roots run hr d hd act ha o ho f
  intro he
  unfold FieldLaw at he
  rw [show (replaceReadout raw f (.literal wrong)).readouts =
    raw.readouts.replace f (.literal wrong) from rfl,replacement_field,rhs] at he
  exact hne (Option.some.inj he)

omit [DecidableEq O] in
theorem observation_order_eval (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (r : Registers R RV) :
    raw.readouts.order.eval a r () = some (observation raw a h r).order := by
  have hc : Complete raw.readouts.order.dependencies a :=
    subready h.2.2 (by intro k hk; simp [Readouts.dependencies,hk])
  exact read_eq raw.readouts.order a hc r

omit [DecidableEq O] in
theorem observation_progress_eval (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (r : Registers R RV) :
    raw.readouts.progress.eval a r () = some (observation raw a h r).progress := by
  have hc : Complete raw.readouts.progress.dependencies a :=
    subready h.2.2 (by intro k hk; simp [Readouts.dependencies,hk])
  exact read_eq raw.readouts.progress a hc r

omit [DecidableEq O] in
theorem observation_record_eval (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (r : Registers R RV) :
    raw.readouts.record.eval a r () = some (observation raw a h r).record := by
  have hc : Complete raw.readouts.record.dependencies a :=
    subready h.2.2 (by intro k hk; simp [Readouts.dependencies,hk])
  exact read_eq raw.readouts.record a hc r

/-- Strictness is DERIVED from independent positive numeric recipes and update
coherence, for every supported advancing step throughout the closure. -/
theorem supported_advancement (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV))
    (gate : ReadoutLawGate raw law a h roots)
    (run : Registers R RV) (hr : Closure raw a h roots run)
    (d : D) (hd : d ∈ raw.disturbances) (act : A) (ha : act ∈ raw.actions)
    (o : O) (ho : o ∈ raw.outcomes) (hp : weight raw a h run (d,act) o > 0) :
    (observation raw a h (next raw a h run (d,act) o)).order > (observation raw a h run).order ∧
    (observation raw a h (next raw a h run (d,act) o)).progress > (observation raw a h run).progress ∧
    (observation raw a h (next raw a h run (d,act) o)).record > (observation raw a h run).record := by
  have checks := gate.2.2.2.2.2.1 run hr d hd act ha o ho
  obtain ⟨ord,tick,prog,rec,hord,_,hprog,hrec,hordLt,_,hprogLt,hrecLt⟩ := checks.2 hp
  have orderLaw := checks.1 .order
  have progressLaw := checks.1 .progress
  have recordLaw := checks.1 .record
  change raw.readouts.order.eval a (next raw a h run (d,act) o) () = _ at orderLaw
  change raw.readouts.progress.eval a (next raw a h run (d,act) o) () = _ at progressLaw
  change raw.readouts.record.eval a (next raw a h run (d,act) o) () = _ at recordLaw
  rw [observation_order_eval raw a h (next raw a h run (d,act) o),hord] at orderLaw
  rw [observation_progress_eval raw a h (next raw a h run (d,act) o),hprog] at progressLaw
  rw [observation_record_eval raw a h (next raw a h run (d,act) o),hrec] at recordLaw
  rw [Option.some.inj orderLaw,Option.some.inj progressLaw,Option.some.inj recordLaw]
  exact ⟨hordLt,hprogLt,hrecLt⟩

theorem empty_roots_rejected (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) :
    ¬ ReadoutLawGate raw law a h [] := fun gate => gate.2.2.2.2.1 rfl

end CSTTT.TargetTheory.GenericHandoff.RegisterFuture
