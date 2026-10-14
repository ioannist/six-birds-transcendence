import CSTTT.POS04.GenericTransport
import CSTTT.Transport.FullFuture

/-! The complete POS-04 C6 interface is the eight-component observation in
`C6Observation` (`audit/M3_model_spec.md:22,30-33`). This module instantiates
the generic unbounded-word bisimulation on the raw `actionRow` dynamics. It
does not identify the unbounded event counter with a finite frozen alphabet. -/
namespace CSTTT.POS04

open CSTTT.TransportTheory
open CSTTT.Objecthood.T1Audit

def pos04FullFuture : FullFutureModel C6State Action OutcomeClass C6Code C6Observation where
  outcomes := outcomeClasses
  code := q
  observe := observe .positive
  weight := fun x a c => (effectiveMass x a c : Rat) / 4
  next := c6Next .positive

theorem pos04_full_one_step_bisim : FullOneStepBisim pos04FullFuture := by
  intro x y hcode
  have hb := positive_bisim x y hcode
  refine ⟨hb.1, ?_⟩
  intro a c
  have htag : x.tag = y.tag := code_equal_tags hcode
  have hfunded : x.funded = y.funded := by
    simpa [q] using congrArg C6Code.maintenance hcode
  have hmass := class_mass_of_profile_eq x.tag x.factor y.factor a
    (by simpa [htag] using (hb.2 a).1) c
  rw [htag] at hmass
  have heffective : effectiveMass x a c = effectiveMass y a c := by
    simp [effectiveMass, htag, hfunded, hmass]
  exact ⟨by simp [pos04FullFuture, heffective], (hb.2 a).2 c⟩

theorem pos04_full_future_sufficient : FullFutureSufficient pos04FullFuture :=
  full_future_sufficient_of_bisim pos04FullFuture pos04_full_one_step_bisim

theorem pos04_full_future_eq_c6
    (x : C6State) (word : List Action) (trace : List C6Observation) :
    fullFuture pos04FullFuture x word trace = F .positive x word trace := by
  induction word generalizing x trace with
  | nil =>
      simp [fullFuture, F, pos04FullFuture]
  | cons a rest ih =>
      cases trace with
      | nil => rfl
      | cons first tail =>
          simp only [fullFuture, F, pos04FullFuture]
          by_cases h : first = observe .positive x
          · simp only [h]
            apply congrArg List.sum
            apply List.map_congr_left
            intro c _
            exact congrArg (((effectiveMass x a c : Rat) / 4) * ·)
              (ih (c6Next .positive x a c) tail)
          · simp [h]

theorem pos04_full_future_is_declared_c6
    (x y : C6State) (h : q x = q y)
    (word : List Action) (trace : List C6Observation) :
    F .positive x word trace = F .positive y word trace := by
  rw [← pos04_full_future_eq_c6 x word trace,
    ← pos04_full_future_eq_c6 y word trace]
  exact pos04_full_future_sufficient x y h word trace

end CSTTT.POS04
