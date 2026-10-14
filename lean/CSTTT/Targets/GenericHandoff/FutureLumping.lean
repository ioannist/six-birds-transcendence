import CSTTT.Targets.GenericHandoff.WeightedFibers
import CSTTT.Transport.FullFuture

/-! Generic all-word sufficiency via computed outcome-code fibers.
This is the semantic induction engine. Raw clause boundaries instantiate m
with their DEFINED dynamics, observer and code, never supplied candidates.
Every actual outcome remains a branch. No representative is chosen, and no
branch-resolving probability equality is demanded. Closure/readout laws and
coarseness remain separate C6 gates; this theorem does not imply them. -/
namespace CSTTT.TargetTheory.GenericHandoff.FutureLumping
open CSTTT.TransportTheory
variable {S A O C V : Type} [DecidableEq C]

def NextCode (m : FullFutureModel S A O C V) (x : S) (a : A) : O → C :=
  fun o => m.code (m.next x a o)

def OneStep (m : FullFutureModel S A O C V) : Prop :=
  ∀ x y, m.code x = m.code y → m.observe x = m.observe y ∧
    ∀ a,
      (∀ o ∈ m.outcomes, NextCode m x a o = NextCode m y a o) ∧
      (∀ o ∈ m.outcomes,
        WeightedFibers.mass m.outcomes (NextCode m x a) (m.weight x a) (NextCode m x a o) =
        WeightedFibers.mass m.outcomes (NextCode m x a) (m.weight y a) (NextCode m x a o))

variable [DecidableEq V]

theorem all_words (m : FullFutureModel S A O C V) (hb : OneStep m) : FullFutureSufficient m := by
  intro x y hcode word
  induction word generalizing x y with
  | nil => intro trace; simp [fullFuture,(hb x y hcode).1]
  | cons act rest ih =>
    intro trace
    cases trace with
    | nil => rfl
    | cons first tail =>
      have hstep := hb x y hcode
      simp only [fullFuture]
      rw [hstep.1]
      by_cases he : first = m.observe y
      · simp only [if_pos he]
        have hsame :
            (m.outcomes.map fun o => m.weight y act o * fullFuture m (m.next y act o) rest tail).sum =
            (m.outcomes.map fun o => m.weight y act o * fullFuture m (m.next x act o) rest tail).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro o ho
          rw [ih (m.next y act o) (m.next x act o) ((hstep.2 act).1 o ho).symm]
        rw [hsame]
        exact WeightedFibers.weighted_congr m.outcomes (NextCode m x act)
          (m.weight x act) (m.weight y act) (fun o => fullFuture m (m.next x act o) rest tail)
          (hstep.2 act).2
          (fun o _ p _ hk => ih _ _ hk tail)
      · simp only [if_neg he]

omit [DecidableEq V] in
theorem mass_guard (m : FullFutureModel S A O C V) (x y : S)
    (hc : m.code x = m.code y) (a : A) (o : O) (ho : o ∈ m.outcomes)
    (bad : WeightedFibers.mass m.outcomes (NextCode m x a) (m.weight x a) (NextCode m x a o) ≠
      WeightedFibers.mass m.outcomes (NextCode m x a) (m.weight y a) (NextCode m x a o)) :
    ¬ OneStep m := fun h => bad ((h x y hc).2 a |>.2 o ho)

omit [DecidableEq V] in
theorem successor_code_guard (m : FullFutureModel S A O C V) (x y : S)
    (hc : m.code x = m.code y) (a : A) (o : O) (ho : o ∈ m.outcomes)
    (bad : NextCode m x a o ≠ NextCode m y a o) : ¬ OneStep m :=
  fun h => bad ((h x y hc).2 a |>.1 o ho)

omit [DecidableEq V] in
theorem observation_guard (m : FullFutureModel S A O C V) (x y : S)
    (hc : m.code x = m.code y) (bad : m.observe x ≠ m.observe y) : ¬ OneStep m :=
  fun h => bad (h x y hc).1

end CSTTT.TargetTheory.GenericHandoff.FutureLumping
