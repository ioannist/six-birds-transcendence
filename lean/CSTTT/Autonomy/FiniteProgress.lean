import CSTTT.Core.Finite


/-! Generic finite-state obstruction only; no new concrete fixture evaluated.
Finite controlled factors need an event-indexed lift if strict progress and
record are state readouts on every step of an infinite run. -/
namespace CSTTT.AutonomyTheory.FiniteProgress

-- Class (b): raw operational policy construction or derived law.
def spectralBound {State : Type} (states : List State) (progress : State → Nat) : Nat :=
  states.foldr (fun state bound => max (progress state) bound) 0

-- Class (b): raw operational policy construction or derived law.
theorem member_bounded {State : Type} (states : List State) (progress : State → Nat)
    (state : State) (h : state∈states) : progress state≤spectralBound states progress := by
  induction states with
  | nil => simp at h
  | cons first rest ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

-- Class (b): raw operational policy construction or derived law.
theorem strict_run_lower (progress : Nat → Nat)
    (step : ∀ n, progress n<progress (n+1)) : ∀ n, n≤progress n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih => have hs := step n; omega

-- Class (b): raw operational policy construction or derived law.
theorem no_infinite_strict_finite_state_run {State : Type}
    (states : List State) (progress : State → Nat) :
    ¬ ∃ run : Nat → State, (∀ n, run n∈states) ∧
      (∀ n, progress (run n)<progress (run (n+1))) := by
  rintro ⟨run,member,step⟩
  let bound := spectralBound states progress
  have lower := strict_run_lower (fun n => progress (run n)) step (bound+1)
  have upper := member_bounded states progress (run (bound+1)) (member (bound+1))
  change progress (run (bound+1))≤bound at upper
  omega

end CSTTT.AutonomyTheory.FiniteProgress
