import CSTTT.Targets.GenericHandoff.StaticView

/-! Raw typed cell namespace translation. The translated assignment is the
actual pullback of a supplied primitive assignment; register and environment
coordinates stay independent. Cell value operations are total raw operations,
while missing primitive inputs remain missing. No injectivity is assumed. -/
namespace CSTTT.TargetTheory.GenericHandoff.CellReindex
open RegisterInterpreter RegisterInitialization
variable {SC TC R Env X Selector : Type} {SV : SC → Type} {TV : TC → Type} {RV : R → Type}

def pullback (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (a : Assignment TC TV) : Assignment SC SV :=
  fun k => (a (cell k)).map (value k)

def expression (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    {X : Type} (e : Expr SC SV R RV Env X) : Expr TC TV R RV Env X :=
  match e with
  | .literal x => .literal x
  | .cell k => .map (value k) (.cell (cell k))
  | .register r => .register r
  | .environment f => .environment f
  | .map f arg => .map f (expression cell value arg)
  | .pair x y => .pair (expression cell value x) (expression cell value y)
  | .choose c x y => .choose (expression cell value c) (expression cell value x) (expression cell value y)

theorem evaluation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (e : Expr SC SV R RV Env X) (a : Assignment TC TV) (run : Registers R RV) (env : Env) :
    (expression cell value e).eval a run env = e.eval (pullback cell value a) run env := by
  induction e <;> simp_all [expression,Expr.eval,pullback]

theorem dependencies (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (e : Expr SC SV R RV Env X) :
    (expression cell value e).dependencies = e.dependencies.map cell := by
  induction e <;> simp_all [expression,Expr.dependencies,List.map_append]

theorem complete_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (keys : List SC) (a : Assignment TC TV) :
    Complete (keys.map cell) a ↔ Complete keys (pullback cell value a) := by
  constructor
  · intro h k hk
    have hp := h (cell k) (List.mem_map.mpr ⟨k,hk,rfl⟩)
    simpa [pullback] using hp
  · intro h t ht
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ht
    have hp := h k hk
    simpa [pullback] using hp

theorem ready_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (e : Expr SC SV R RV Env X) (a : Assignment TC TV) :
    Complete (expression cell value e).dependencies a ↔ Complete e.dependencies (pullback cell value a) := by
  rw [dependencies]
  exact complete_iff cell value e.dependencies a

def program (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (p : Program SC SV R RV Env) : Program TC TV R RV Env :=
  fun r => expression cell value (p r)

theorem execute_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (p : Program SC SV R RV Env) (a : Assignment TC TV) (run : Registers R RV) (env : Env) :
    execute (program cell value p) a run env = execute p (pullback cell value a) run env :=
  funext (fun r => evaluation cell value (p r) a run env)

theorem program_ready_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (p : Program SC SV R RV Env) (a : Assignment TC TV) :
    ProgramReady (program cell value p) a ↔ ProgramReady p (pullback cell value a) := by
  exact forall_congr' (fun r => ready_iff cell value (p r) a)

theorem checked_execute_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (p : Program SC SV R RV Env) (a : Assignment TC TV)
    (h : ProgramReady (program cell value p) a) (j : ProgramReady p (pullback cell value a))
    (run : Registers R RV) (env : Env) :
    checkedExecute (program cell value p) a h run env =
      checkedExecute p (pullback cell value a) j run env := by
  funext r
  have he := congrFun (execute_equation cell value p a run env) r
  rw [checked_execute_eq _ a h,checked_execute_eq _ _ j] at he
  exact Option.some.inj he

def initializer (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (p : InitialProgram SC SV R RV Selector) : InitialProgram TC TV R RV Selector :=
  fun r => expression cell value (p r)

theorem initializer_ready_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (p : InitialProgram SC SV R RV Selector) (a : Assignment TC TV) :
    RegisterInitialization.Ready (initializer cell value p) a ↔
      RegisterInitialization.Ready p (pullback cell value a) :=
  forall_congr' (fun r => ready_iff cell value (p r) a)

theorem initialize_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (p : InitialProgram SC SV R RV Selector) (a : Assignment TC TV)
    (h : RegisterInitialization.Ready (initializer cell value p) a)
    (j : RegisterInitialization.Ready p (pullback cell value a)) (selector : Selector) :
    initial (initializer cell value p) a h selector = initial p (pullback cell value a) j selector := by
  funext r
  have he := evaluation cell value (p r) a noRegisters selector
  change evaluate (initializer cell value p) a selector r = evaluate p (pullback cell value a) selector r at he
  rw [initial_eq _ a h,initial_eq _ _ j] at he
  exact Option.some.inj he

def view (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (v : StaticView SC SV X) : StaticView TC TV X := ⟨expression cell value v.instruction⟩
def cellView (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (v : CellView SC SV X) : CellView TC TV X :=
  ⟨cell v.cell,fun x => v.project (value v.cell x)⟩

theorem view_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (v : StaticView SC SV X) (a : Assignment TC TV) :
    (view cell value v).read a = v.read (pullback cell value a) :=
  evaluation cell value v.instruction a noRegisters ()

theorem cell_view_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (v : CellView SC SV X) (a : Assignment TC TV) :
    (cellView cell value v).read a = v.read (pullback cell value a) := by
  simp [CellView.read,cellView,pullback,Option.map_map,Function.comp_def]

theorem view_dependencies (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (v : StaticView SC SV X) :
    (view cell value v).dependencies = v.dependencies.map cell :=
  dependencies cell value v.instruction

theorem missing_evaluation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (e : Expr SC SV R RV Env X) (a : Assignment TC TV) (k : SC)
    (hk : k ∈ e.dependencies) (hm : a (cell k) = none) (run : Registers R RV) (env : Env) :
    (expression cell value e).eval a run env = none := by
  apply Expr.missing _ a (cell k) _ hm run env
  rw [dependencies]
  exact List.mem_map.mpr ⟨k,hk,rfl⟩

end CSTTT.TargetTheory.GenericHandoff.CellReindex
