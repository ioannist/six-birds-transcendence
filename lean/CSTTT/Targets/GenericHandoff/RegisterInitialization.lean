import CSTTT.Targets.GenericHandoff.RegisterInterpreter

/-! Raw initial-coordinate instructions, before any run exists. The empty
register namespace prevents an initializer from reading a supplied candidate
run. Initial states are defined from assigned primitives and raw selectors.
This is an interpreter component, not an acquisition or package verdict. -/
namespace CSTTT.TargetTheory.GenericHandoff.RegisterInitialization
open RegisterInterpreter

abbrev NoValue : Empty → Type := fun e => nomatch e

def noRegisters : Registers Empty NoValue := fun e => nomatch e
abbrev InitialProgram (Cell : Type) (Value : Cell → Type) (R : Type)
    (RV : R → Type) (Selector : Type) :=
  (r : R) → Expr Cell Value Empty NoValue Selector (RV r)

variable {Cell R Selector : Type} {Value : Cell → Type} {RV : R → Type}

def Ready (p : InitialProgram Cell Value R RV Selector) (a : Assignment Cell Value) : Prop :=
  ∀ r, Complete (p r).dependencies a

def evaluate (p : InitialProgram Cell Value R RV Selector) (a : Assignment Cell Value)
    (selector : Selector) (r : R) : Option (RV r) := (p r).eval a noRegisters selector

noncomputable def initial (p : InitialProgram Cell Value R RV Selector)
    (a : Assignment Cell Value) (h : Ready p a) (selector : Selector) : Registers R RV :=
  fun r => Classical.choose ((p r).present_of_complete a (h r) noRegisters selector)

theorem initial_eq (p : InitialProgram Cell Value R RV Selector)
    (a : Assignment Cell Value) (h : Ready p a) (selector : Selector) (r : R) :
    evaluate p a selector r = some (initial p a h selector r) :=
  Classical.choose_spec ((p r).present_of_complete a (h r) noRegisters selector)

theorem locality (p : InitialProgram Cell Value R RV Selector)
    {a b : Assignment Cell Value} (h : ∀ r, Agrees (p r).dependencies a b)
    (selector : Selector) (r : R) : evaluate p a selector r = evaluate p b selector r :=
  (p r).locality (h r) noRegisters selector

theorem initial_locality (p : InitialProgram Cell Value R RV Selector)
    {a b : Assignment Cell Value} (ha : Ready p a) (hb : Ready p b)
    (h : ∀ r, Agrees (p r).dependencies a b) (selector : Selector) :
    initial p a ha selector = initial p b hb selector := by
  funext r
  apply Option.some.inj
  rw [← initial_eq p a ha selector r, ← initial_eq p b hb selector r]
  exact locality p h selector r

theorem missing_rejected (p : InitialProgram Cell Value R RV Selector)
    (a : Assignment Cell Value) (r : R) (k : Cell) (hk : k ∈ (p r).dependencies)
    (hm : a k = none) : ¬ Ready p a := by
  intro h
  have hp := h r k hk
  rw [hm] at hp
  contradiction

theorem missing_evaluation (p : InitialProgram Cell Value R RV Selector)
    (a : Assignment Cell Value) (r : R) (k : Cell) (hk : k ∈ (p r).dependencies)
    (hm : a k = none) (selector : Selector) : evaluate p a selector r = none :=
  (p r).missing a k hk hm noRegisters selector

end CSTTT.TargetTheory.GenericHandoff.RegisterInitialization
