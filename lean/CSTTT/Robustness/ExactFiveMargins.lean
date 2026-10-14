import Init.Data.Rat.Lemmas

/-! Exact five-component rational margins (b). The box is numerical;
whole operational gates require the separate raw-erasure bridge. -/
namespace CSTTT.RobustnessTheory.ExactFiveMargins
-- Class (b): new construction or derived law.
inductive Coordinate where
  | predictive | order | tick | progress | record
  deriving DecidableEq, Repr
-- Class (b): new construction or derived law.
abbrev Vector := Coordinate → Rat
-- Class (b): new construction or derived law.
def WithinBox (radius delta : Vector) : Prop :=
  ∀ i, -radius i≤delta i ∧ delta i≤radius i

-- Class (b): new construction or derived law.
def PositiveCertifiedMargin (base radius : Vector) : Prop :=
  ∀ i, 0≤radius i ∧ 0<base i-radius i

-- Class (b): new construction or derived law.
theorem all_five_positive (base radius delta : Vector)
    (margin : PositiveCertifiedMargin base radius) (box : WithinBox radius delta) :
    ∀ i, 0<base i+delta i := by
  intro i
  have bound : base i-radius i≤base i+delta i := by
    simpa [Rat.sub_eq_add_neg] using (Rat.add_le_add_left (c:=base i)).mpr (box i).1
  apply Rat.not_le.mp
  intro failed
  exact (Rat.not_le.mpr (margin i).2) (Rat.le_trans bound failed)

end CSTTT.RobustnessTheory.ExactFiveMargins
