import CSTTT.Targets.GenericHandoff.NativeComposition.Factor
import CSTTT.Targets.GenericHandoff.ObjecthoodRules

/-! A direct C1 scout tests the actual native safe-policy kernel. This does
not supply a C1 witness: uniqueness forces uniformity and rejects C1. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ObjecthoodScout
open FixedPointVerifier

def prototypes : List Factor :=
  [(false,false,false),(false,true,false),(true,false,false),(true,true,false)]
def raw (operations : List (RowOperation Factor)) : ObjecthoodRules.Raw Factor Bool Factor :=
  ⟨TemporalFactorRules.profile (factorSchema false) (factorData false),
    (factorData false).policy,prototypes,1,1,1/2,factors,(false,false,false),operations,
    (fun s t => if s=t then 1 else 0),
    (fun s k => if labels s=k then 1 else 0),
    (fun k s => if labels s=k then 1/2 else 0),1,0,0,0⟩

theorem uniform_probability (operations : List (RowOperation Factor)) :
    Probability (raw operations).profile.states (ObjecthoodRules.uniform (raw operations)) := by
  change Probability factors (fun _ : Factor => (1:Rat)/8)
  constructor
  · intro s; change (0:Rat)≤1/8; decide +kernel
  · decide +kernel

theorem uniform_fixed (operations : List (RowOperation Factor)) :
    Fixed (raw operations).profile.states (ObjecthoodRules.E (raw operations))
      (ObjecthoodRules.uniform (raw operations)) := by
  intro s
  rcases s with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j
  all_goals change dot factors (fun t => ObjecthoodRules.E (raw []) t _) (fun _ => (1:Rat)/8)=(1:Rat)/8
  all_goals decide +kernel

theorem gate_forces_uniform (operations : List (RowOperation Factor))
    (h : ObjecthoodRules.Gate (raw operations)) :
    ObjecthoodRules.pi (raw operations)=ObjecthoodRules.uniform (raw operations) := by
  have unique := (ObjecthoodRules.checked_probability_fixed_unique (raw operations) h).2.2
  exact (unique _ (uniform_probability operations) (uniform_fixed operations)).symm

theorem actual_c1_rejected (operations : List (RowOperation Factor)) :
    ¬ ObjecthoodRules.Accept (raw operations) := by
  intro h
  exact h.2.1 (gate_forces_uniform operations h.1)

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ObjecthoodScout
