import CSTTT.Temporal.Signature

/-! A generic, weighted, all-word future test. `observe` is the entire declared
observation, rather than an M-class action-word coefficient. Its components
are supplied by a concrete raw model; the bisimulation premise is an equation
on one-step observations, weights, and successors, not a stored future verdict.
The induction proves all finite disturbance words without a horizon bound. -/
namespace CSTTT.TransportTheory

structure FullFutureModel (State Action Outcome Code Observation : Type) where
  outcomes : List Outcome
  code : State → Code
  observe : State → Observation
  weight : State → Action → Outcome → Rat
  next : State → Action → Outcome → State

variable {S A O C V : Type}
variable [DecidableEq V]

def fullFuture (m : FullFutureModel S A O C V) (x : S) :
    List A → List V → Rat
  | [], trace => if trace = [m.observe x] then 1 else 0
  | a :: rest, trace =>
      match trace with
      | [] => 0
      | first :: tail =>
          if first = m.observe x then
            (m.outcomes.map fun c =>
              m.weight x a c * fullFuture m (m.next x a c) rest tail).sum
          else 0

def FullOneStepBisim (m : FullFutureModel S A O C V) : Prop :=
  ∀ x y, m.code x = m.code y →
    m.observe x = m.observe y ∧
    ∀ a c, m.weight x a c = m.weight y a c ∧
      m.code (m.next x a c) = m.code (m.next y a c)

def FullFutureSufficient (m : FullFutureModel S A O C V) : Prop :=
  ∀ x y, m.code x = m.code y →
    ∀ word trace, fullFuture m x word trace = fullFuture m y word trace

theorem full_future_sufficient_of_bisim
    (m : FullFutureModel S A O C V) (hb : FullOneStepBisim m) :
    FullFutureSufficient m := by
  intro x y hcode word
  induction word generalizing x y with
  | nil =>
      intro trace
      simp [fullFuture, (hb x y hcode).1]
  | cons a rest ih =>
      intro trace
      have hobs := (hb x y hcode).1
      cases trace with
      | nil => rfl
      | cons first tail =>
          simp only [fullFuture]
          rw [hobs]
          by_cases hfirst : first = m.observe y
          · simp only [hfirst]
            have hterms :
                (m.outcomes.map fun c =>
                  m.weight x a c * fullFuture m (m.next x a c) rest tail) =
                (m.outcomes.map fun c =>
                  m.weight y a c * fullFuture m (m.next y a c) rest tail) := by
              apply List.map_congr_left
              intro c _
              obtain ⟨hw, hn⟩ := (hb x y hcode).2 a c
              rw [hw, ih (m.next x a c) (m.next y a c) hn tail]
            exact congrArg List.sum hterms
          · simp [hfirst]

end CSTTT.TransportTheory
