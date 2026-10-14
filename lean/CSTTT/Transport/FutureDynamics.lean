import CSTTT.Transport.FullFuture

/-! Raw one-step dynamics and its unbounded future closure. The closure is
computed from the raw dynamics, never from the candidate future model. It
includes all enumerated outcome successors (even zero-weight successors), so
checking it is stronger than checking only supported executions. -/
namespace CSTTT.TransportTheory

structure RawFutureDynamics (X A O : Type) where
  outcomes : List O
  actionRow : X → A → O → Rat
  update : X → A → O → X

inductive FutureClosure (raw : RawFutureDynamics X A O) (roots : List X) : X → Prop where
  | root (x) : x ∈ roots → FutureClosure raw roots x
  | step {x} : FutureClosure raw roots x → ∀ a o, o ∈ raw.outcomes →
      FutureClosure raw roots (raw.update x a o)

/-- Exact one-step equations on the entire raw reachable future closure. -/
def FutureDynamicsCheck (model : FullFutureModel X A O C V)
    (raw : RawFutureDynamics X A O) (roots : List X) : Prop :=
  model.outcomes = raw.outcomes ∧ ∀ x, FutureClosure raw roots x →
    ∀ a o, model.weight x a o = raw.actionRow x a o ∧
      model.next x a o = raw.update x a o

def rawFutureModel (model : FullFutureModel X A O C V)
    (raw : RawFutureDynamics X A O) : FullFutureModel X A O C V :=
  { model with outcomes := raw.outcomes, weight := raw.actionRow, next := raw.update }

/-- No finite horizon: one-step links identify every finite-word trace law
with the raw action rows and counter/ledger update. -/
theorem future_eq_raw_on_closure [DecidableEq V]
    (model : FullFutureModel X A O C V) (raw : RawFutureDynamics X A O)
    (roots : List X) (h : FutureDynamicsCheck model raw roots)
    (x : X) (hx : FutureClosure raw roots x) (word : List A) (trace : List V) :
    fullFuture model x word trace = fullFuture (rawFutureModel model raw) x word trace := by
  induction word generalizing x trace with
  | nil => rfl
  | cons a rest ih =>
      cases trace with
      | nil => rfl
      | cons first tail =>
          simp only [fullFuture, rawFutureModel]
          by_cases ho : first = model.observe x
          · simp only [ho, if_true]
            rw [h.1]
            apply congrArg List.sum
            apply List.map_congr_left
            intro o hm
            obtain ⟨hw, hn⟩ := h.2 x hx a o
            rw [hw, hn, ih (raw.update x a o) (FutureClosure.step hx a o hm) tail]
            rfl
          · simp [ho]

theorem raw_future_sufficient_on_closure [DecidableEq V]
    (model : FullFutureModel X A O C V) (raw : RawFutureDynamics X A O)
    (roots : List X) (h : FutureDynamicsCheck model raw roots)
    (hb : FullOneStepBisim model) (x y : X)
    (hx : FutureClosure raw roots x) (hy : FutureClosure raw roots y)
    (hc : model.code x = model.code y) (word : List A) (trace : List V) :
    fullFuture (rawFutureModel model raw) x word trace =
      fullFuture (rawFutureModel model raw) y word trace := by
  rw [← future_eq_raw_on_closure model raw roots h x hx,
      ← future_eq_raw_on_closure model raw roots h y hy]
  exact full_future_sufficient_of_bisim model hb x y hc word trace

end CSTTT.TransportTheory
