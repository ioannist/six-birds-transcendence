import CSTTT.Robustness.RawRationalMargin
import CSTTT.Targets.GenericHandoff.RegisterSubstitution
/-! Class (b): actual partial initializer/updater readouts and exact every-partial decoders. -/
namespace CSTTT.RobustnessTheory.PartialEventReadout
open CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization RegisterSubstitution
open CSTTT.RobustnessTheory ExactFiveMargins
variable {Cell R H D A O X : Type} {Value : Cell → Type} {RV : R → Type}
-- Class (b): new exact operational construction or derived law.
abbrev Context (H D A O : Type) := H × (D × A × O)
-- Class (b): new exact operational construction or derived law.
def initialContext (p : InitialProgram Cell Value R RV H) : InitialProgram Cell Value R RV (Context H D A O) :=
  fun r => (p r).reenv Prod.fst
-- Class (b): new exact operational construction or derived law.
def stepContext (p : Program Cell Value R RV (D × A × O)) : Program Cell Value R RV (Context H D A O) :=
  fun r => (p r).reenv Prod.snd
-- Class (b): new exact operational construction or derived law.
def beforeExpr (p : InitialProgram Cell Value R RV H) (e : Expr Cell Value R RV Unit X) :
    Expr Cell Value Empty NoValue (Context H D A O) X :=
  substitute (initialContext p) (e.reenv (fun _ => ()))
-- Class (b): new exact operational construction or derived law.
def afterExpr (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV (D × A × O))
    (e : Expr Cell Value R RV Unit X) : Expr Cell Value Empty NoValue (Context H D A O) X :=
  substitute (initialContext p) (substitute (stepContext q) (e.reenv (fun _ => ())))
-- Class (b): new exact operational construction or derived law.
theorem before_eq (p : InitialProgram Cell Value R RV H) (e : Expr Cell Value R RV Unit X)
    (a : Assignment Cell Value) (hp : RegisterInitialization.Ready p a) (h : H) (d : D) (act : A) (o : O) :
    (beforeExpr p e).eval a noRegisters (h,d,act,o)= e.eval a (initial p a hp h) () := by
  rw [beforeExpr,evaluation]
  have hi : evaluateTranslation (initialContext p) a noRegisters (h,d,act,o)=fun r => some (initial p a hp h r) := by
    funext r
    simp only [evaluateTranslation,initialContext,Expr.reenv_eval]
    exact initial_eq p a hp h r
  rw [hi,total_registers,Expr.reenv_eval]
-- Class (b): new exact operational construction or derived law.
theorem after_eq (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV (D × A × O))
    (e : Expr Cell Value R RV Unit X) (a : Assignment Cell Value)
    (hp : RegisterInitialization.Ready p a) (hq : ProgramReady q a) (h : H) (d : D) (act : A) (o : O) :
    (afterExpr p q e).eval a noRegisters (h,d,act,o)=
      e.eval a (checkedExecute q a hq (initial p a hp h) (d,act,o)) () := by
  rw [afterExpr,evaluation]
  have hi : evaluateTranslation (initialContext p) a noRegisters (h,d,act,o)=fun r => some (initial p a hp h r) := by
    funext r
    simp only [evaluateTranslation,initialContext,Expr.reenv_eval]
    exact initial_eq p a hp h r
  rw [hi,total_registers,evaluation]
  have hu : evaluateTranslation (stepContext q) a (initial p a hp h) (h,d,act,o)=
      fun r => some (checkedExecute q a hq (initial p a hp h) (d,act,o) r) := by
    funext r
    simp only [evaluateTranslation,stepContext,Expr.reenv_eval]
    exact checked_execute_eq q a hq (initial p a hp h) (d,act,o) r
  rw [hu,total_registers,Expr.reenv_eval]
-- Class (b): new exact operational construction or derived law.
def partialAdvance (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV (D × A × O))
    (read : Coordinate → Expr Cell Value R RV Unit Rat) (a : Assignment Cell Value)
    (h : H) (d : D) (act : A) (o : O) : Option Vector := do
  let before ← RawRationalMargin.readVector (fun i => (beforeExpr p (read i)).eval a noRegisters (h,d,act,o))
  let after ← RawRationalMargin.readVector (fun i => (afterExpr p q (read i)).eval a noRegisters (h,d,act,o))
  pure fun i => after i-before i
-- Class (b): new exact operational construction or derived law.
theorem partial_advance_eq (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV (D × A × O))
    (read : Coordinate → Expr Cell Value R RV Unit Rat) (a : Assignment Cell Value)
    (hp : RegisterInitialization.Ready p a) (hq : ProgramReady q a) (h : H) (d : D) (act : A) (o : O) :
    partialAdvance p q read a h d act o=(do
      let before ← RawRationalMargin.readVector (fun i => (read i).eval a (initial p a hp h) ())
      let after ← RawRationalMargin.readVector (fun i => (read i).eval a
        (checkedExecute q a hq (initial p a hp h) (d,act,o)) ())
      pure fun i => after i-before i) := by
  simp only [partialAdvance,before_eq p _ a hp h d act o,after_eq p q _ a hp hq h d act o]
-- Class (b): new exact operational construction or derived law.
theorem missing_after_rejects (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV (D × A × O))
    (read : Coordinate → Expr Cell Value R RV Unit Rat) (a : Assignment Cell Value)
    (h : H) (d : D) (act : A) (o : O) (i : Coordinate)
    (missing : (afterExpr p q (read i)).eval a noRegisters (h,d,act,o)=none) :
    partialAdvance p q read a h d act o=none := by
  have hn := RawRationalMargin.read_vector_missing
    (fun j => (afterExpr p q (read j)).eval a noRegisters (h,d,act,o)) i missing
  simp only [partialAdvance,hn]
  cases RawRationalMargin.readVector (fun j => (beforeExpr p (read j)).eval a noRegisters (h,d,act,o)) <;> rfl

-- Class (b): exact vector decoding for every partial coordinate assignment.
theorem read_vector_some_iff (read : Coordinate → Option Rat) (v : Vector) :
    RawRationalMargin.readVector read=some v ↔ ∀ i, read i=some (v i) := by
  constructor
  · intro hv
    cases hp : read .predictive <;> cases ho : read .order <;>
      cases ht : read .tick <;> cases hg : read .progress <;> cases hr : read .record <;>
      simp only [RawRationalMargin.readVector,hp,ho,ht,hg,hr,Option.bind_eq_bind] at hv
    all_goals try contradiction
    case some.some.some.some.some predictive order tick progress record =>
      have eq := Option.some.inj hv
      intro i
      have heq := congrArg (fun f : Vector => some (f i)) eq
      cases i <;> simpa only [hp,ho,ht,hg,hr] using heq
  · exact RawRationalMargin.read_vector_some read v
end CSTTT.RobustnessTheory.PartialEventReadout
namespace CSTTT.RobustnessTheory.RawRationalMargin
open CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open ExactFiveMargins RationalRegisters
variable {Cell R SC SR TR S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type}
  {Value : Cell → Type} {SourceValue : SC → Type} {RV : R → Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => FinalHandoff.Raw SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint
variable [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route]
  [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner]
-- Class (b): a partial expression exists independently of checked readiness.
def partialEventAdvance (m : Model) (input : Input SC SourceValue)
    (hist : H) (d : D) (act : A) (outcome : O) : Option Vector :=
  PartialEventReadout.partialAdvance (initializer m) (program m) (observer m)
    (target m input) hist d act outcome
-- Class (b): exact equality with the actual checked event, no numeric hypothesis.
theorem partial_event_advance_eq (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (hist : H) (d : D) (act : A) (outcome : O) :
    partialEventAdvance m input hist d act outcome=eventAdvance m input ready hist d act outcome := by
  unfold partialEventAdvance eventAdvance initialRun updateRun
  exact PartialEventReadout.partial_advance_eq _ _ _ _ _ _ hist d act outcome
end CSTTT.RobustnessTheory.RawRationalMargin


namespace CSTTT.RobustnessTheory.PartialEventReadout
open ExactFiveMargins
-- Class (b): missing-vector equivalence for every partial coordinate read.
theorem read_vector_none_iff (read : Coordinate → Option Rat) :
    RawRationalMargin.readVector read=none ↔ ∃ i, read i=none := by
  constructor
  · intro h
    cases hp : read .predictive
    · exact ⟨.predictive,hp⟩
    cases ho : read .order
    · exact ⟨.order,ho⟩
    cases ht : read .tick
    · exact ⟨.tick,ht⟩
    cases hg : read .progress
    · exact ⟨.progress,hg⟩
    cases hr : read .record
    · exact ⟨.record,hr⟩
    simp [RawRationalMargin.readVector,hp,ho,ht,hg,hr] at h
  · rintro ⟨i,hi⟩
    exact RawRationalMargin.read_vector_missing read i hi
end CSTTT.RobustnessTheory.PartialEventReadout
