import CSTTT.Targets.GenericHandoff.Substrate

/-! Typed, immutable run registers and raw instruction interpretation.

This is a component of RawHandoff, not its assembled validity predicate.
Static cells, run registers and the disturbance/action/outcome environment are
independent namespaces. Expressions are raw instructions, not supplied future
models, observers, transition functions or propositions. Pure operations may
inspect unbounded values: the hybrid contract does not impose finite context.
The finite-factor engine therefore still needs an instance-specific proved lift.

`map` is a pure value operation, like the existing TranslationLanguage's value
instructions. No model-level predicate callback is introduced. Missing static
reads propagate through eager evaluation, including BOTH conditional branches.
Thus an unselected branch cannot conceal a missing required primitive. -/
namespace CSTTT.TargetTheory.GenericHandoff.RegisterInterpreter

abbrev Registers (R : Type) (V : R → Type) := (r : R) → V r

inductive Expr (Cell : Type) (Value : Cell → Type)
    (Register : Type) (RegisterValue : Register → Type) (Env : Type) : Type → Type 1 where
  | literal {X : Type} (value : X) : Expr Cell Value Register RegisterValue Env X
  | cell (k : Cell) : Expr Cell Value Register RegisterValue Env (Value k)
  | register (r : Register) : Expr Cell Value Register RegisterValue Env (RegisterValue r)
  | environment {X : Type} (read : Env → X) : Expr Cell Value Register RegisterValue Env X
  | map {X Y : Type} (operation : X → Y)
      (arg : Expr Cell Value Register RegisterValue Env X) :
      Expr Cell Value Register RegisterValue Env Y
  | pair {X Y : Type} (left : Expr Cell Value Register RegisterValue Env X)
      (right : Expr Cell Value Register RegisterValue Env Y) :
      Expr Cell Value Register RegisterValue Env (X × Y)
  | choose {X : Type} (condition : Expr Cell Value Register RegisterValue Env Bool)
      (yes no : Expr Cell Value Register RegisterValue Env X) :
      Expr Cell Value Register RegisterValue Env X

variable {Cell Register Env X : Type} {Value : Cell → Type}
  {RegisterValue : Register → Type}

def Expr.dependencies {X : Type} (e : Expr Cell Value Register RegisterValue Env X) : List Cell :=
  match e with
  | .literal _ | .register _ | .environment _ => []
  | .cell k => [k]
  | .map _ arg => arg.dependencies
  | .pair left right => left.dependencies ++ right.dependencies
  | .choose condition yes no => condition.dependencies ++ yes.dependencies ++ no.dependencies

def Expr.eval (a : Assignment Cell Value) (run : Registers Register RegisterValue) (env : Env)
    {X : Type} (e : Expr Cell Value Register RegisterValue Env X) : Option X :=
  match e with
  | .literal x => some x
  | .cell k => a k
  | .register r => some (run r)
  | .environment f => some (f env)
  | .map f arg => (arg.eval a run env).map f
  | .pair left right => do
      let x ← left.eval a run env
      let y ← right.eval a run env
      pure (x,y)
  | .choose condition yes no => do
      let c ← condition.eval a run env
      let y ← yes.eval a run env
      let n ← no.eval a run env
      pure (if c then y else n)

theorem Expr.locality (e : Expr Cell Value Register RegisterValue Env X)
    {a b : Assignment Cell Value} (h : Agrees e.dependencies a b)
    (run : Registers Register RegisterValue) (env : Env) : e.eval a run env = e.eval b run env := by
  induction e with
  | literal => rfl
  | cell k => exact h k (by simp [Expr.dependencies])
  | register => rfl
  | environment => rfl
  | map f e ih => simp only [Expr.eval,ih h]
  | pair e f ih jh =>
    have he := ih (fun k hk => h k (List.mem_append_left _ hk))
    have hf := jh (fun k hk => h k (List.mem_append_right _ hk))
    simp only [Expr.eval,he,hf]
  | choose c e f ih jh kh =>
    have hc := ih (fun k hk => h k (List.mem_append_left _ (List.mem_append_left _ hk)))
    have he := jh (fun k hk => h k (List.mem_append_left _ (List.mem_append_right _ hk)))
    have hf := kh (fun k hk => h k (List.mem_append_right _ hk))
    simp only [Expr.eval,hc,he,hf]

theorem Expr.missing (e : Expr Cell Value Register RegisterValue Env X)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ e.dependencies) (hm : a k = none)
    (run : Registers Register RegisterValue) (env : Env) : e.eval a run env = none := by
  induction e with
  | literal => simp [Expr.dependencies] at hk
  | cell j =>
    have he : k = j := by simpa [Expr.dependencies] using hk
    subst j
    exact hm
  | register => simp [Expr.dependencies] at hk
  | environment => simp [Expr.dependencies] at hk
  | map f e ih => simp [Expr.eval,ih hk]
  | pair e f ih jh =>
    rcases List.mem_append.mp hk with he | hf
    · simp [Expr.eval,ih he]
    · simp [Expr.eval,jh hf]
  | choose c e f ih jh kh =>
    rcases List.mem_append.mp hk with hce | hf
    · rcases List.mem_append.mp hce with hc | he
      · simp [Expr.eval,ih hc]
      · simp [Expr.eval,jh he]
    · simp [Expr.eval,kh hf]

theorem Expr.present_of_complete (e : Expr Cell Value Register RegisterValue Env X)
    (a : Assignment Cell Value) (hc : Complete e.dependencies a)
    (run : Registers Register RegisterValue) (env : Env) :
    ∃ x, e.eval a run env = some x := by
  induction e with
  | literal x => exact ⟨x,rfl⟩
  | cell k =>
    have hs := hc k (by simp [Expr.dependencies])
    cases he : a k with
    | none => simp [he] at hs
    | some v => exact ⟨v,he⟩
  | register r => exact ⟨run r,rfl⟩
  | environment f => exact ⟨f env,rfl⟩
  | map f e ih =>
    obtain ⟨x,hx⟩ := ih hc
    exact ⟨f x,by simp [Expr.eval,hx]⟩
  | pair e f ih jh =>
    obtain ⟨x,hx⟩ := ih (fun k hk => hc k (List.mem_append_left _ hk))
    obtain ⟨y,hy⟩ := jh (fun k hk => hc k (List.mem_append_right _ hk))
    exact ⟨(x,y),by simp [Expr.eval,hx,hy]⟩
  | choose c e f ih jh kh =>
    obtain ⟨c,hc'⟩ := ih (fun k hk => hc k (List.mem_append_left _ (List.mem_append_left _ hk)))
    obtain ⟨x,hx⟩ := jh (fun k hk => hc k (List.mem_append_left _ (List.mem_append_right _ hk)))
    obtain ⟨y,hy⟩ := kh (fun k hk => hc k (List.mem_append_right _ hk))
    exact ⟨if c then x else y,by simp [Expr.eval,hc',hx,hy]⟩

/-- Simultaneous update: every instruction reads the SAME old register state.
There is no sequential overwrite or secondary mutable namespace. -/
abbrev Program (Cell : Type) (Value : Cell → Type) (Register : Type)
    (RegisterValue : Register → Type) (Env : Type) :=
  (r : Register) → Expr Cell Value Register RegisterValue Env (RegisterValue r)

def execute (p : Program Cell Value Register RegisterValue Env)
    (a : Assignment Cell Value) (run : Registers Register RegisterValue) (env : Env) :
    (r : Register) → Option (RegisterValue r) := fun r => (p r).eval a run env

def ProgramReady (p : Program Cell Value Register RegisterValue Env)
    (a : Assignment Cell Value) : Prop := ∀ r, Complete (p r).dependencies a

theorem execute_locality (p : Program Cell Value Register RegisterValue Env)
    {a b : Assignment Cell Value} (h : ∀ r, Agrees (p r).dependencies a b)
    (run : Registers Register RegisterValue) (env : Env) : execute p a run env = execute p b run env := by
  funext r
  exact (p r).locality (h r) run env

theorem execute_missing (p : Program Cell Value Register RegisterValue Env)
    (a : Assignment Cell Value) (r : Register) (k : Cell) (hk : k ∈ (p r).dependencies)
    (hm : a k = none) (run : Registers Register RegisterValue) (env : Env) :
    execute p a run env r = none := (p r).missing a k hk hm run env

theorem execute_present (p : Program Cell Value Register RegisterValue Env)
    (a : Assignment Cell Value) (h : ProgramReady p a)
    (run : Registers Register RegisterValue) (env : Env) (r : Register) :
    ∃ v, execute p a run env r = some v := (p r).present_of_complete a (h r) run env

/-- A total helper exists only downstream of readiness evidence. No fallback
value, default updater, or default observer can justify a successful decode. -/
noncomputable def checkedExecute (p : Program Cell Value Register RegisterValue Env)
    (a : Assignment Cell Value) (h : ProgramReady p a)
    (run : Registers Register RegisterValue) (env : Env) : Registers Register RegisterValue :=
  fun r => Classical.choose (execute_present p a h run env r)

theorem checked_execute_eq (p : Program Cell Value Register RegisterValue Env)
    (a : Assignment Cell Value) (h : ProgramReady p a)
    (run : Registers Register RegisterValue) (env : Env) (r : Register) :
    execute p a run env r = some (checkedExecute p a h run env r) :=
  Classical.choose_spec (execute_present p a h run env r)

theorem missing_program_rejected (p : Program Cell Value Register RegisterValue Env)
    (a : Assignment Cell Value) (r : Register) (k : Cell) (hk : k ∈ (p r).dependencies)
    (hm : a k = none) : ¬ ProgramReady p a := by
  intro h
  have hp := h r k hk
  rw [hm] at hp
  contradiction

/-- Reindex the explicit event environment only. Cell and register namespaces
are unchanged; locality and missing-input rejection are preserved. -/
def Expr.reenv {E' : Type} (f : E' → Env) {X : Type}
    (e : Expr Cell Value Register RegisterValue Env X) :
    Expr Cell Value Register RegisterValue E' X := match e with
  | .literal x => .literal x
  | .cell k => .cell k
  | .register r => .register r
  | .environment g => .environment (fun env => g (f env))
  | .map g e => .map g (e.reenv f)
  | .pair e g => .pair (e.reenv f) (g.reenv f)
  | .choose c e g => .choose (c.reenv f) (e.reenv f) (g.reenv f)

theorem Expr.reenv_eval {E' : Type} (f : E' → Env)
    (e : Expr Cell Value Register RegisterValue Env X)
    (a : Assignment Cell Value) (r : Registers Register RegisterValue) (env : E') :
    (e.reenv f).eval a r env = e.eval a r (f env) := by
  induction e <;> simp_all [Expr.reenv,Expr.eval]

theorem Expr.reenv_dependencies {E' : Type} (f : E' → Env)
    (e : Expr Cell Value Register RegisterValue Env X) : (e.reenv f).dependencies = e.dependencies := by
  induction e <;> simp_all [Expr.reenv,Expr.dependencies]

end CSTTT.TargetTheory.GenericHandoff.RegisterInterpreter
