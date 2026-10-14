import CSTTT.Targets.GenericHandoff.RegisterInterpreter

/-! Typed register-program composition. Raw expressions substitute the first
program's register instructions into the second, with eager static reads.
The internal partial-register interpreter makes the all-partial equation
explicit; no intermediate run or successful translation is supplied. -/
namespace CSTTT.TargetTheory.GenericHandoff.RegisterSubstitution
open RegisterInterpreter
variable {Cell S M T Env X : Type} {Value : Cell → Type}
  {SV : S → Type} {MV : M → Type} {TV : T → Type}

def reads {X : Type} (e : Expr Cell Value M MV Env X) : List M :=
  match e with
  | .literal _ | .cell _ | .environment _ => []
  | .register r => [r]
  | .map _ arg => reads arg
  | .pair a b => reads a ++ reads b
  | .choose c a b => reads c ++ reads a ++ reads b

def substitute {X : Type} (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (e : Expr Cell Value M MV Env X) : Expr Cell Value S SV Env X :=
  match e with
  | .literal v => .literal v
  | .cell k => .cell k
  | .register r => first r
  | .environment f => .environment f
  | .map f arg => .map f (substitute first arg)
  | .pair a b => .pair (substitute first a) (substitute first b)
  | .choose c a b => .choose (substitute first c) (substitute first a) (substitute first b)

/-- Interpretation argument only: the sequencing theorem supplies these
optional registers by evaluating the first raw translation instruction. -/
def evalPartial {X : Type} (a : Assignment Cell Value) (run : (r : M) → Option (MV r)) (env : Env)
    (e : Expr Cell Value M MV Env X) : Option X :=
  match e with
  | .literal v => some v
  | .cell k => a k
  | .register r => run r
  | .environment f => some (f env)
  | .map f arg => (evalPartial a run env arg).map f
  | .pair x y => do
      let u ← evalPartial a run env x
      let v ← evalPartial a run env y
      pure (u,v)
  | .choose c x y => do
      let b ← evalPartial a run env c
      let u ← evalPartial a run env x
      let v ← evalPartial a run env y
      pure (if b then u else v)

def program (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (second : (r : T) → Expr Cell Value M MV Env (TV r)) :
    (r : T) → Expr Cell Value S SV Env (TV r) :=
  fun r => substitute first (second r)

def evaluateTranslation (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (a : Assignment Cell Value) (run : Registers S SV) (env : Env) : (r : M) → Option (MV r) :=
  fun r => (first r).eval a run env

theorem evaluation (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (e : Expr Cell Value M MV Env X) (a : Assignment Cell Value)
    (run : Registers S SV) (env : Env) :
    (substitute first e).eval a run env = evalPartial a (evaluateTranslation first a run env) env e := by
  induction e with
  | literal => rfl
  | cell => rfl
  | register => rfl
  | environment => rfl
  | map f arg ih => simp only [substitute,Expr.eval,evalPartial,ih]
  | pair x y ih jh => simp only [substitute,Expr.eval,evalPartial,ih,jh]
  | choose c x y ih jh kh => simp only [substitute,Expr.eval,evalPartial,ih,jh,kh]

theorem total_registers (e : Expr Cell Value M MV Env X)
    (a : Assignment Cell Value) (run : Registers M MV) (env : Env) :
    evalPartial a (fun r => some (run r)) env e = e.eval a run env := by
  induction e with
  | literal => rfl
  | cell => rfl
  | register => rfl
  | environment => rfl
  | map f arg ih => simp only [evalPartial,Expr.eval,ih]
  | pair x y ih jh => simp only [evalPartial,Expr.eval,ih,jh]
  | choose c x y ih jh kh => simp only [evalPartial,Expr.eval,ih,jh,kh]

theorem dependencies (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (e : Expr Cell Value M MV Env X) (k : Cell) :
    k ∈ (substitute first e).dependencies ↔
      k ∈ e.dependencies ∨ ∃ r ∈ reads e, k ∈ (first r).dependencies := by
  induction e with
  | literal => simp [substitute,Expr.dependencies,reads]
  | cell => simp [substitute,Expr.dependencies,reads]
  | register => simp [substitute,Expr.dependencies,reads]
  | environment => simp [substitute,Expr.dependencies,reads]
  | map f arg ih => simpa only [substitute,Expr.dependencies,reads] using ih
  | pair x y ih jh =>
      simp only [substitute,Expr.dependencies,reads,List.mem_append,ih,jh]
      constructor
      · rintro (hx | hy)
        · rcases hx with hx | ⟨r,hr,hk⟩
          · exact Or.inl (Or.inl hx)
          · exact Or.inr ⟨r,Or.inl hr,hk⟩
        · rcases hy with hy | ⟨r,hr,hk⟩
          · exact Or.inl (Or.inr hy)
          · exact Or.inr ⟨r,Or.inr hr,hk⟩
      · rintro ((hx | hy) | ⟨r,(hr | hr),hk⟩)
        · exact Or.inl (Or.inl hx)
        · exact Or.inr (Or.inl hy)
        · exact Or.inl (Or.inr ⟨r,hr,hk⟩)
        · exact Or.inr (Or.inr ⟨r,hr,hk⟩)
  | choose c x y ih jh kh =>
      simp only [substitute,Expr.dependencies,reads,List.mem_append,ih,jh,kh]
      constructor
      · rintro ((hc | hx) | hy)
        · rcases hc with hc | ⟨r,hr,hk⟩
          · exact Or.inl (Or.inl (Or.inl hc))
          · exact Or.inr ⟨r,Or.inl (Or.inl hr),hk⟩
        · rcases hx with hx | ⟨r,hr,hk⟩
          · exact Or.inl (Or.inl (Or.inr hx))
          · exact Or.inr ⟨r,Or.inl (Or.inr hr),hk⟩
        · rcases hy with hy | ⟨r,hr,hk⟩
          · exact Or.inl (Or.inr hy)
          · exact Or.inr ⟨r,Or.inr hr,hk⟩
      · rintro (((hc | hx) | hy) | ⟨r,((hr | hr) | hr),hk⟩)
        · exact Or.inl (Or.inl (Or.inl hc))
        · exact Or.inl (Or.inr (Or.inl hx))
        · exact Or.inr (Or.inl hy)
        · exact Or.inl (Or.inl (Or.inr ⟨r,hr,hk⟩))
        · exact Or.inl (Or.inr (Or.inr ⟨r,hr,hk⟩))
        · exact Or.inr (Or.inr ⟨r,hr,hk⟩)

theorem complete_iff (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (e : Expr Cell Value M MV Env X) (a : Assignment Cell Value) :
    Complete (substitute first e).dependencies a ↔
      Complete e.dependencies a ∧ ∀ r ∈ reads e, Complete (first r).dependencies a := by
  constructor
  · intro h
    refine ⟨fun k hk => h k ((dependencies first e k).mpr (Or.inl hk)),?_⟩
    intro r hr k hk
    exact h k ((dependencies first e k).mpr (Or.inr ⟨r,hr,hk⟩))
  · rintro ⟨he,hr⟩ k hk
    rcases (dependencies first e k).mp hk with he' | ⟨r,hm,hf⟩
    · exact he k he'
    · exact hr r hm k hf

def Ready (first : (r : M) → Expr Cell Value S SV Env (MV r)) (a : Assignment Cell Value) : Prop :=
  ∀ r, Complete (first r).dependencies a

noncomputable def translate (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (a : Assignment Cell Value) (h : Ready first a) (run : Registers S SV) (env : Env) : Registers M MV :=
  fun r => Classical.choose ((first r).present_of_complete a (h r) run env)

theorem translation_equation (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (a : Assignment Cell Value) (h : Ready first a) (run : Registers S SV) (env : Env) (r : M) :
    evaluateTranslation first a run env r = some (translate first a h run env r) :=
  Classical.choose_spec ((first r).present_of_complete a (h r) run env)

theorem checked_evaluation (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (e : Expr Cell Value M MV Env X) (a : Assignment Cell Value) (h : Ready first a)
    (run : Registers S SV) (env : Env) :
    (substitute first e).eval a run env = e.eval a (translate first a h run env) env := by
  rw [evaluation]
  have hr := funext (translation_equation first a h run env)
  rw [hr]
  exact total_registers e a _ env

theorem program_evaluation (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (second : (r : T) → Expr Cell Value M MV Env (TV r)) (a : Assignment Cell Value)
    (run : Registers S SV) (env : Env) (r : T) :
    (program first second r).eval a run env =
      evalPartial a (evaluateTranslation first a run env) env (second r) :=
  evaluation first (second r) a run env

theorem program_ready_iff (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (second : (r : T) → Expr Cell Value M MV Env (TV r)) (a : Assignment Cell Value) :
    Ready (program first second) a ↔
      Ready second a ∧ ∀ r t, t ∈ reads (second r) → Complete (first t).dependencies a := by
  constructor
  · intro h
    exact ⟨fun r => ((complete_iff first (second r) a).mp (h r)).1,
      fun r => ((complete_iff first (second r) a).mp (h r)).2⟩
  · rintro ⟨hs,hf⟩ r
    exact (complete_iff first (second r) a).mpr ⟨hs r,hf r⟩

theorem program_ready (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (second : (r : T) → Expr Cell Value M MV Env (TV r)) (a : Assignment Cell Value)
    (hf : Ready first a) (hs : Ready second a) : Ready (program first second) a :=
  (program_ready_iff first second a).mpr ⟨hs,fun _ t _ => hf t⟩

theorem translate_compose (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (second : (r : T) → Expr Cell Value M MV Env (TV r)) (a : Assignment Cell Value)
    (hf : Ready first a) (hs : Ready second a) (hc : Ready (program first second) a)
    (run : Registers S SV) (env : Env) :
    translate (program first second) a hc run env =
      translate second a hs (translate first a hf run env) env := by
  funext r
  have hl := translation_equation (program first second) a hc run env r
  have hr := translation_equation second a hs (translate first a hf run env) env r
  have he := checked_evaluation first (second r) a hf run env
  exact Option.some.inj (hl.symm.trans (he.trans hr))

theorem missing_static (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (e : Expr Cell Value M MV Env X) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ e.dependencies) (hm : a k = none) (run : Registers S SV) (env : Env) :
    (substitute first e).eval a run env = none :=
  (substitute first e).missing a k ((dependencies first e k).mpr (Or.inl hk)) hm run env

theorem missing_consumed_register (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (e : Expr Cell Value M MV Env X) (a : Assignment Cell Value) (r : M) (k : Cell)
    (hr : r ∈ reads e) (hk : k ∈ (first r).dependencies) (hm : a k = none)
    (run : Registers S SV) (env : Env) : (substitute first e).eval a run env = none :=
  (substitute first e).missing a k ((dependencies first e k).mpr (Or.inr ⟨r,hr,hk⟩)) hm run env

theorem associative
    (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (second : (r : T) → Expr Cell Value M MV Env (TV r))
    (e : Expr Cell Value T TV Env X) :
    substitute first (substitute second e) = substitute (program first second) e := by
  induction e with
  | literal => rfl
  | cell => rfl
  | register => rfl
  | environment => rfl
  | map f arg ih => simp only [substitute,ih]
  | pair x y ih jh => simp only [substitute,ih,jh]
  | choose c x y ih jh kh => simp only [substitute,ih,jh,kh]

theorem program_associative {U : Type} {UV : U → Type}
    (first : (r : M) → Expr Cell Value S SV Env (MV r))
    (second : (r : T) → Expr Cell Value M MV Env (TV r))
    (third : (r : U) → Expr Cell Value T TV Env (UV r)) :
    program first (program second third) = program (program first second) third := by
  funext r
  exact associative first second (third r)

end CSTTT.TargetTheory.GenericHandoff.RegisterSubstitution
