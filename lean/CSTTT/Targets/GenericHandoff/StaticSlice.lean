import CSTTT.Targets.GenericHandoff.StaticView

/-! An explicit typed instruction reading a finite dependency slice. The
result is a partial immutable assignment, NOT an acceptance value. All listed
cells are read eagerly; missing inputs reject before any decoder default.
Repeated cell IDs read the same immutable primitive and cause no ambiguity. -/
namespace CSTTT.TargetTheory.GenericHandoff.StaticSlice
open RegisterInterpreter RegisterInitialization
variable {Cell : Type} {Value : Cell → Type} [DecidableEq Cell]

def instruction (scope : List Cell) : Expr Cell Value Empty NoValue Unit (Assignment Cell Value) :=
  match scope with
  | [] => .literal (fun _ => none)
  | k::ks => .map (fun p => put p.2 k (some p.1)) (.pair (.cell k) (instruction ks))

theorem dependencies (scope : List Cell) : (instruction (Value := Value) scope).dependencies = scope := by
  induction scope with
  | nil => rfl
  | cons k ks ih => simp only [instruction,Expr.dependencies,ih]; rfl

theorem decode_cons (k : Cell) (ks : List Cell) (a : Assignment Cell Value) :
    put (decode ks a) k (a k) = decode (k::ks) a := by
  funext j
  by_cases he : j = k
  · subst j; simp [decode]
  · simp [put,decode,he]

/-- Successful evaluation reads exactly the slice; no total candidate
assignment is an input. This holds on arbitrary partial assignments. -/
theorem evaluation (scope : List Cell) (a : Assignment Cell Value)
    (hc : Complete scope a) :
    (instruction scope).eval a noRegisters () = some (decode scope a) := by
  induction scope with
  | nil => rfl
  | cons k ks ih =>
    have hk := hc k (by simp)
    have ht := ih (fun j hj => hc j (by simp [hj]))
    cases hv : a k with
    | none => simp [hv] at hk
    | some v =>
      simp only [instruction,Expr.eval,hv,ht]
      exact congrArg some (by simpa only [hv] using decode_cons k ks a)

def view (scope : List Cell) : StaticView Cell Value (Assignment Cell Value) := ⟨instruction scope⟩

theorem read_iff (scope : List Cell) (a : Assignment Cell Value) (b : Assignment Cell Value) :
    (view scope).read a = some b ↔ Complete scope a ∧ b = decode scope a := by
  constructor
  · intro he
    have hc : Complete scope a := by
      intro k hk
      cases hv : a k with
      | some v => rfl
      | none =>
        have hn := Expr.missing (instruction (Value := Value) scope) a k (by rw [dependencies]; exact hk) hv noRegisters ()
        change (instruction scope).eval a noRegisters () = some b at he
        rw [hn] at he
        contradiction
    have hv := evaluation scope a hc
    exact ⟨hc,(Option.some.inj (he.symm.trans hv))⟩
  · rintro ⟨hc,rfl⟩
    exact evaluation scope a hc

theorem missing_rejected (scope : List Cell) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ scope) (hm : a k = none) : (view scope).read a = none :=
  Expr.missing (instruction scope) a k (by rw [dependencies]; exact hk) hm noRegisters ()

theorem locality (scope : List Cell) {a b : Assignment Cell Value} (he : Agrees scope a b) :
    (view scope).read a = (view scope).read b :=
  (view scope).locality (by simpa [view,StaticView.dependencies,dependencies] using he)

theorem decoded_complete (scope : List Cell) (a : Assignment Cell Value) (hc : Complete scope a) :
    Complete scope (decode scope a) := by
  intro k hk
  simpa [decode,hk] using hc k hk
end CSTTT.TargetTheory.GenericHandoff.StaticSlice
