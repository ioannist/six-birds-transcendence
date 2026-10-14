import CSTTT.Targets.GenericHandoff.RegisterSubstitution
import CSTTT.Targets.GenericHandoff.RegisterInitialization

namespace CSTTT.TargetTheory.GenericHandoff.InitialProgramComposition
open RegisterInterpreter RegisterInitialization RegisterSubstitution
variable {Cell R H E : Type} {Value : Cell → Type} {RV : R → Type}
-- Class (b): compose the actual raw initializer and selected actual program.
def after (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV E) (event : H → E) :
    InitialProgram Cell Value R RV H := fun r => substitute p ((q r).reenv event)
-- Class (b): exact composition readiness for every partial assignment.
theorem after_ready_iff (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV E)
    (event : H → E) (a : Assignment Cell Value) :
    RegisterInitialization.Ready (after p q event) a ↔ ProgramReady q a ∧
      ∀ r t, t∈reads ((q r).reenv event) → Complete (p t).dependencies a := by
  change RegisterSubstitution.Ready (RegisterSubstitution.program p (fun r => (q r).reenv event)) a ↔ _
  rw [RegisterSubstitution.program_ready_iff]
  simp only [RegisterSubstitution.Ready,ProgramReady,Expr.reenv_dependencies]
-- Class (b): independently established source and program readiness imply composition readiness.
theorem after_ready (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV E)
    (event : H → E) (a : Assignment Cell Value)
    (hp : RegisterInitialization.Ready p a) (hq : ProgramReady q a) :
    RegisterInitialization.Ready (after p q event) a :=
  (after_ready_iff p q event a).mpr ⟨hq,fun _ t _ => hp t⟩
-- Class (b): actual optional composed readout equals the same actual initialized update.
theorem after_evaluation (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV E)
    (event : H → E) (a : Assignment Cell Value)
    (hp : RegisterInitialization.Ready p a) (hq : ProgramReady q a) (hist : H) (r : R) :
    (after p q event r).eval a noRegisters hist=
      some (checkedExecute q a hq (initial p a hp hist) (event hist) r) := by
  unfold after
  rw [evaluation]
  have hi : evaluateTranslation p a noRegisters hist=fun r => some (initial p a hp hist r) := by
    funext r
    exact initial_eq p a hp hist r
  rw [hi,total_registers,Expr.reenv_eval]
  exact checked_execute_eq q a hq (initial p a hp hist) (event hist) r
-- Class (b): actual total initialization of the composed raw program, no supplied derived run.
theorem initial_after_eq (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV E)
    (event : H → E) (a : Assignment Cell Value)
    (hp : RegisterInitialization.Ready p a) (hq : ProgramReady q a)
    (hc : RegisterInitialization.Ready (after p q event) a) (hist : H) :
    initial (after p q event) a hc hist=checkedExecute q a hq (initial p a hp hist) (event hist) := by
  funext r
  exact Option.some.inj ((initial_eq (after p q event) a hc hist r).symm.trans
    (after_evaluation p q event a hp hq hist r))
-- Class (b): raw iteration of the same selected program, before any initialized run exists.
def iterate (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV E)
    (event : H → E) : Nat → InitialProgram Cell Value R RV H
  | 0 => p
  | n+1 => after (iterate p q event n) q event
-- Class (b): syntactic initializer readiness derived for every iteration and partial assignment.
theorem iterate_ready (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV E)
    (event : H → E) (a : Assignment Cell Value)
    (hp : RegisterInitialization.Ready p a) (hq : ProgramReady q a) :
    ∀ n, RegisterInitialization.Ready (iterate p q event n) a := by
  intro n
  induction n with
  | zero => exact hp
  | succ n ih => exact after_ready _ q event a ih hq
-- Class (b): actual repeated checked updates, used only as an execution readout.
noncomputable def checkedIteration (q : Program Cell Value R RV E) (a : Assignment Cell Value)
    (hq : ProgramReady q a) (run : Registers R RV) (event : E) : Nat → Registers R RV
  | 0 => run
  | n+1 => checkedExecute q a hq (checkedIteration q a hq run event n) event
-- Class (b): raw iterated initialization exactly returns repeated actual native program execution.
theorem initial_iterate_eq (p : InitialProgram Cell Value R RV H) (q : Program Cell Value R RV E)
    (event : H → E) (a : Assignment Cell Value)
    (hp : RegisterInitialization.Ready p a) (hq : ProgramReady q a) (hist : H) :
    ∀ n, initial (iterate p q event n) a (iterate_ready p q event a hp hq n) hist=
      checkedIteration q a hq (initial p a hp hist) (event hist) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := initial_after_eq (iterate p q event n) q event a
      (iterate_ready p q event a hp hq n) hq (iterate_ready p q event a hp hq (n+1)) hist
    exact he.trans (congrArg (fun run => checkedExecute q a hq run (event hist)) ih)
end CSTTT.TargetTheory.GenericHandoff.InitialProgramComposition
