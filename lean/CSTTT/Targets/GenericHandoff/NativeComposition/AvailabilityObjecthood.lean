import CSTTT.Targets.GenericHandoff.NativeComposition.AvailabilityFactor
import CSTTT.Targets.GenericHandoff.NativeComposition.ObjecthoodCells

/-! The C4 availability repair uses the existing primitive C1 recipe.
Computed quotient reconstruction, P and both operators are preserved;
acceptance is re-established for the changed actual raw action support. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.AvailabilityObjecthood
open NativeObjecthoodCells FixedPointVerifier

def raw : ObjecthoodRules.Raw Factor Bool Factor := data (AvailabilityFactor.input false) supplement

private theorem forall_factor_iff (p : Factor → Prop) :
    (∀ s, p s) ↔ ∀ a b c : Bool, p (a,b,c) := by
  constructor
  · intro h a b c; exact h (a,b,c)
  · intro h s; rcases s with ⟨a,b,c⟩; exact h a b c
local instance (p : Factor → Prop) [∀ s, Decidable (p s)] : Decidable (∀ s, p s) :=
  decidable_of_iff (∀ a b c : Bool, p (a,b,c)) (forall_factor_iff p).symm

theorem actual_probe_rows (s : Factor) :
    AvailabilityFactor.rows s (ObjecthoodProbe.policy (AvailabilityFactor.temporal false) s)=
      (factorData false).rows s (ObjecthoodProbe.policy (factorData false) s) := by
  rcases s with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> rfl
theorem P_preserved : ObjecthoodRules.P raw=ObjecthoodRules.P ObjecthoodProbe.raw := by
  funext s t
  rcases s with ⟨p,v,j⟩
  rcases t with ⟨q,w,k⟩
  cases p <;> cases v <;> cases j <;> cases q <;> cases w <;> cases k <;> decide +kernel

theorem class_equality_preserved (s t : Factor) :
    ObjecthoodRules.classOf raw s=ObjecthoodRules.classOf raw t ↔
      ObjecthoodRules.classOf ObjecthoodProbe.raw s=ObjecthoodRules.classOf ObjecthoodProbe.raw t := by
  rcases s with ⟨p,v,j⟩
  rcases t with ⟨q,w,k⟩
  cases p <;> cases v <;> cases j <;> cases q <;> cases w <;> cases k <;> decide +kernel
theorem C_preserved : ObjecthoodRules.C raw=ObjecthoodRules.C ObjecthoodProbe.raw := by
  funext s k
  unfold ObjecthoodRules.C
  have hp : raw.prototypes=ObjecthoodProbe.raw.prototypes := rfl
  rw [hp]
  cases ObjecthoodProbe.raw.prototypes[k]? with
  | none => rfl
  | some p => simp only [class_equality_preserved]
theorem fiber_preserved (s : Factor) : ObjecthoodRules.fiber raw s=ObjecthoodRules.fiber ObjecthoodProbe.raw s := by
  unfold ObjecthoodRules.fiber
  apply List.filter_congr
  intro t ht
  simp only [class_equality_preserved]
theorem U_preserved : ObjecthoodRules.U raw=ObjecthoodRules.U ObjecthoodProbe.raw := by
  funext k s
  unfold ObjecthoodRules.U
  have hp : raw.prototypes=ObjecthoodProbe.raw.prototypes := rfl
  rw [hp]
  cases ObjecthoodProbe.raw.prototypes[k]? with
  | none => rfl
  | some p => simp only [class_equality_preserved,fiber_preserved]
theorem CU_preserved : ObjecthoodRules.CU raw=ObjecthoodRules.CU ObjecthoodProbe.raw := by
  unfold ObjecthoodRules.CU
  rw [C_preserved,U_preserved]
  rfl
theorem operator_preserved : ObjecthoodRules.E raw=ObjecthoodRules.E ObjecthoodProbe.raw :=
  ObjecthoodRules.operator_congruence raw ObjecthoodProbe.raw rfl P_preserved CU_preserved rfl rfl
theorem zero_operator_preserved : ObjecthoodRules.Ezero raw=ObjecthoodRules.Ezero ObjecthoodProbe.raw := by
  unfold ObjecthoodRules.Ezero
  rw [P_preserved,CU_preserved]
  rfl
theorem candidate_preserved : ObjecthoodRules.pi raw=ObjecthoodRules.pi ObjecthoodProbe.raw := by
  unfold ObjecthoodRules.pi
  rw [operator_preserved]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem gate : ObjecthoodRules.Gate raw := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold ObjecthoodRules.KernelCheck
    rw [P_preserved]
    exact ObjecthoodProbe.gate.1
  · unfold ObjecthoodRules.QuotientCheck
    refine ⟨?_,?_,?_,?_,?_⟩
    all_goals decide +kernel
  · unfold ObjecthoodRules.Reconstruction
    rw [P_preserved,C_preserved,U_preserved]
    exact ObjecthoodProbe.gate.2.2.1
  · unfold ObjecthoodRules.SupportCheck
    refine ⟨by decide +kernel,?_,?_,?_⟩
    · intro a; cases a <;> decide +kernel
    · intro s a e he
      change e ∈ AvailabilityFactor.rows s a at he
      by_cases ha : (a && !s.2.1)=true
      · simp [AvailabilityFactor.rows,ha] at he
      · simp [AvailabilityFactor.rows,ha] at he
        rw [he]
        change 0 < (1 : Nat)
        decide +kernel
    · intro s a
      change ((AvailabilityFactor.rows s a).map Prod.snd).sum=0 ∨
        ((AvailabilityFactor.rows s a).map Prod.snd).sum=1
      by_cases ha : (a && !s.2.1)=true
      all_goals simp [AvailabilityFactor.rows,ha]
  · rw [operator_preserved]
    exact ObjecthoodProbe.verifier_passes

theorem actual_c1_accept : ObjecthoodRules.Accept raw := by
  have ha := ObjecthoodProbe.actual_c1_accept
  have hmass : ObjecthoodRules.coreMass raw=ObjecthoodRules.coreMass ObjecthoodProbe.raw := by
    unfold ObjecthoodRules.coreMass
    rw [candidate_preserved]
    rfl
  have htv : ObjecthoodRules.TV raw=ObjecthoodRules.TV ObjecthoodProbe.raw := by
    unfold ObjecthoodRules.TV
    rw [candidate_preserved]
    rfl
  refine ⟨gate,?_,?_,?_,?_,?_⟩
  · rw [candidate_preserved]
    exact ha.2.1
  · rw [hmass]; exact ha.2.2.1
  · rw [htv]; exact ha.2.2.2.1
  · rw [zero_operator_preserved]; exact ha.2.2.2.2.1
  · rw [operator_preserved]; exact ha.2.2.2.2.2

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.AvailabilityObjecthood
