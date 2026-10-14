import CSTTT.Targets.GenericHandoff.OperationalViability

/-! The enclosing package C8 rule also checks raw row well-formedness.
This adds no receiver/source-presence dependency and preserves missing-input
rejection. Outcome enumeration is arbitrary and checked for completeness. -/
namespace CSTTT.TargetTheory.GenericHandoff.OperationalCells
variable {Cell S A O Owner : Type} {Value : Cell → Type}
  [DecidableEq S] [DecidableEq Owner]

def RowsValid (cfg : OperationalViability.Schema S A O Owner) (outcomes : List O)
    (d : OperationalViability.Raw S A O Owner) : Prop :=
  (∀ o, o ∈ outcomes) ∧
  ∀ s ∈ cfg.states, ∀ a ∈ cfg.actions,
    (∀ e ∈ d.rows s a, e.2 > 0 ∧ e.1 ∈ outcomes) ∧
    ((d.rows s a).map Prod.snd).sum = 0 ∨
    (∀ e ∈ d.rows s a, e.2 > 0 ∧ e.1 ∈ outcomes) ∧
    ((d.rows s a).map Prod.snd).sum = cfg.scale

def Accept (cfg : OperationalViability.Schema S A O Owner) (outcomes : List O)
    (v : OperationalViability.Bindings Cell Value S A O Owner) (a : Assignment Cell Value) : Prop :=
  ∃ d, OperationalViability.decoded v a = some d ∧
    OperationalViability.Accept cfg d ∧ RowsValid cfg outcomes d

theorem locality (cfg : OperationalViability.Schema S A O Owner) (outcomes : List O)
    (v : OperationalViability.Bindings Cell Value S A O Owner) {a b : Assignment Cell Value}
    (h : Agrees v.scope a b) : Accept cfg outcomes v a ↔ Accept cfg outcomes v b := by
  simp only [Accept,OperationalViability.decoded_locality v h]

theorem missing_rejected (cfg : OperationalViability.Schema S A O Owner) (outcomes : List O)
    (v : OperationalViability.Bindings Cell Value S A O Owner) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ v.scope) (hm : a k = none) : ¬ Accept cfg outcomes v a := by
  simp [Accept,OperationalViability.missing_consumed v a k hk hm]

end CSTTT.TargetTheory.GenericHandoff.OperationalCells
