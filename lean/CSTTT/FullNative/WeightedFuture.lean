import Lean

namespace CSTTT.FullNative.WeightedFuture
set_option autoImplicit false
variable {S A V Q : Type} [DecidableEq V]

/-- Exact rational future law with the initial observation included. Every
actual row entry remains a branch, including duplicate outcome entries. -/
def law (rows : S → A → List (S × Rat)) (observe : S → V) :
    S → List A → List V → Rat
  | s, [], trace => if trace = [observe s] then 1 else 0
  | _, _ :: _, [] => 0
  | s, a :: rest, v :: tail =>
      if v = observe s then
        (rows s a).foldr (fun e acc => e.2 * law rows observe e.1 rest tail + acc) 0
      else 0

def projectedRows (rows : S → A → List (S × Rat)) (project : S → Q)
    (representative : Q → S) (q : Q) (a : A) : List (Q × Rat) :=
  (rows (representative q) a).map (fun e => (project e.1,e.2))

/-- This is a bridge over an explicit raw-row equation, not a supplied future
law. The reduced transition table is computed by projection of raw rows. -/
theorem projected_law (rows : S → A → List (S × Rat)) (observe : Q → V)
    (project : S → Q) (representative : Q → S)
    (aligned : ∀ s a, (rows s a).map (fun e => (project e.1,e.2)) =
      projectedRows rows project representative (project s) a)
    (s : S) (word : List A) (trace : List V) :
    law rows (fun s => observe (project s)) s word trace =
      law (projectedRows rows project representative) observe (project s) word trace := by
  induction word generalizing s trace with
  | nil => rfl
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons v tail =>
      simp only [law]
      by_cases h : v = observe (project s)
      · simp only [h,if_true]
        rw [← aligned s a,List.foldr_map]
        congr 1
        funext e acc
        exact congrArg (fun z => e.2 * z + acc) (ih e.1 tail)
      · simp [h]

theorem equal_projection_all_words (rows : S → A → List (S × Rat))
    (observe : Q → V) (project : S → Q) (representative : Q → S)
    (aligned : ∀ s a, (rows s a).map (fun e => (project e.1,e.2)) =
      projectedRows rows project representative (project s) a)
    (s t : S) (same : project s = project t) (word : List A) (trace : List V) :
    law rows (fun s => observe (project s)) s word trace =
      law rows (fun s => observe (project s)) t word trace := by
  rw [projected_law rows observe project representative aligned,
    projected_law rows observe project representative aligned,same]

end CSTTT.FullNative.WeightedFuture
