import CSTTT.Targets.GenericHandoff.NativeComposition.ObjecthoodScout
import CSTTT.Targets.GenericHandoff.NativeComposition.Inputs

/-! A declared C1 probe uses existing actual actions and the same raw factor
rows. Its policy selects a phase-reset probe from raw position/hazard fields.
Acquisition continues to use its separately declared safe policy. No accepted
verdict, matrix inverse, stationary vector or uniqueness proof is stored. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ObjecthoodProbe
open FixedPointVerifier

def policy (d : FactorData) (s : Factor) : Bool := decide (d.positions s=0) && d.hazards s

def operations : List (RowOperation Factor) := [
  .add (false,false,true) (false,false,false) ((-5:Rat)/16),
  .add (false,true,false) (false,false,false) ((-1:Rat)/16),
  .add (false,true,true) (false,false,false) ((-1:Rat)/16),
  .add (true,false,false) (false,false,false) ((-1:Rat)/16),
  .add (true,false,true) (false,false,false) ((-1:Rat)/16),
  .add (true,true,false) (false,false,false) ((-1:Rat)/16),
  .add (true,true,true) (false,false,false) ((-1:Rat)/16),
  .scale (false,false,true) (-1),
  .add (false,false,false) (false,false,true) (-1),
  .scale (false,true,false) (-1),
  .add (false,false,false) (false,true,false) ((-3:Rat)/4),
  .add (false,false,true) (false,true,false) ((-1:Rat)/4),
  .add (true,true,false) (false,true,false) ((-1:Rat)/4),
  .add (true,true,true) (false,true,false) ((-1:Rat)/4),
  .scale (false,true,true) (-1),
  .add (false,false,false) (false,true,true) ((-3:Rat)/4),
  .add (false,false,true) (false,true,true) ((-1:Rat)/4),
  .add (true,true,false) (false,true,true) ((-1:Rat)/4),
  .add (true,true,true) (false,true,true) ((-1:Rat)/4),
  .scale (true,false,false) ((-4:Rat)/3),
  .add (false,false,false) (true,false,false) ((-3:Rat)/4),
  .add (false,false,true) (true,false,false) ((-1:Rat)/4),
  .add (true,false,true) (true,false,false) ((-1:Rat)/4),
  .scale (true,false,true) ((-3:Rat)/2),
  .add (false,false,false) (true,false,true) (-1),
  .add (false,false,true) (true,false,true) ((-1:Rat)/3),
  .add (true,false,false) (true,false,true) ((1:Rat)/3),
  .scale (true,true,false) ((-4:Rat)/3),
  .add (false,false,false) (true,true,false) ((-3:Rat)/4),
  .add (false,false,true) (true,true,false) ((-1:Rat)/4),
  .add (true,true,true) (true,true,false) ((-1:Rat)/4),
  .scale (true,true,true) ((-3:Rat)/2),
  .add (false,false,false) (true,true,true) (-1),
  .add (false,false,true) (true,true,true) ((-1:Rat)/3),
  .add (true,true,false) (true,true,true) ((1:Rat)/3)]

def raw : ObjecthoodRules.Raw Factor Bool Factor :=
  {ObjecthoodScout.raw operations with
    policy := policy (factorData false)
    publishedP := fun s t => if (if s.2.1 then (true,s.2) else s)=t then 1 else 0
    expectedTV := 1/8
    expectedDefect := 3/16}

def formula (s t : Factor) : Rat :=
  if labels (destination s (policy (factorData false) s))=labels t then 5/16 else 1/16

def expected (s : Factor) : Rat := if s.2.1 then (if s.1 then 3/16 else 1/16) else 1/8

private theorem forall_factor_iff (p : Factor → Prop) :
    (∀ s, p s) ↔ ∀ a b c : Bool, p (a,b,c) := by
  constructor
  · intro h a b c; exact h (a,b,c)
  · intro h s; rcases s with ⟨a,b,c⟩; exact h a b c
local instance (p : Factor → Prop) [∀ s, Decidable (p s)] : Decidable (∀ s, p s) :=
  decidable_of_iff (∀ a b c : Bool, p (a,b,c)) (forall_factor_iff p).symm

theorem action_declared (s : Factor) : policy (factorData false) s ∈ clauseSchema.actions := by
  rcases s with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> decide +kernel

theorem actual_probe_row (s : Factor) :
    (factorData false).rows s (policy (factorData false) s)=
      [(if s.2.1 then (true,s.2) else s,1)] := by
  rcases s with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem operator_equation : ObjecthoodRules.E raw=formula := by
  funext s t
  rcases s with ⟨p,v,j⟩
  rcases t with ⟨q,w,k⟩
  cases p <;> cases v <;> cases j <;> cases q <;> cases w <;> cases k <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem verifier_passes : check raw.profile.states (ObjecthoodRules.E raw) raw.anchor raw.operations=true := by
  rw [operator_equation]
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem candidate_equation : ObjecthoodRules.pi raw=expected := by
  unfold ObjecthoodRules.pi
  rw [operator_equation]
  funext s
  rcases s with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem gate : ObjecthoodRules.Gate raw := by
  refine ⟨?_,?_,?_,?_,verifier_passes⟩
  · unfold ObjecthoodRules.KernelCheck
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals decide +kernel
  · unfold ObjecthoodRules.QuotientCheck
    refine ⟨?_,?_,?_,?_,?_⟩
    all_goals decide +kernel
  · unfold ObjecthoodRules.Reconstruction
    decide +kernel
  · unfold ObjecthoodRules.SupportCheck
    decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem actual_c1_accept : ObjecthoodRules.Accept raw := by
  refine ⟨gate,?_,?_,?_,?_,?_⟩
  · rw [candidate_equation]
    intro he
    have hx := congrFun he (false,true,false)
    change (1:Rat)/16=1/8 at hx
    have hn : (1:Rat)/16≠1/8 := by decide +kernel
    exact hn hx
  · simp only [ObjecthoodRules.coreMass,candidate_equation]
    decide +kernel
  · simp only [ObjecthoodRules.TV,candidate_equation]
    decide +kernel
  · decide +kernel
  · rw [operator_equation]
    decide +kernel

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ObjecthoodProbe
