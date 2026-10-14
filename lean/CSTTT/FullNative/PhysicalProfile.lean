import CSTTT.FullNative.Primitives

namespace CSTTT.FullNative
open TargetTheory.GenericHandoff
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem state_mem (s : State) : s ∈ states := by
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel

theorem state_domain : states.Nodup ∧ states.length = 32 := by decide +kernel

theorem rows_positive_normalized (s : State) (a : Bool) :
    (∀ e ∈ rows s a, e.2 > 0 ∧ e.1 ∈ states) ∧
    ((rows s a).map Prod.snd).sum = 16 := by
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases a <;> decide +kernel

theorem supported_phase (s : State) (a : Bool) (t : State) (n : Nat)
    (h : (t,n) ∈ rows s a) : t.phase = !s.phase := by
  cases a
  · simp only [rows,Bool.false_eq_true,if_false] at h
    obtain ⟨uv,_,hr⟩ := List.mem_flatMap.mp h
    obtain ⟨r,_,he⟩ := List.mem_map.mp hr
    exact congrArg (fun e : State × Nat => e.1.phase) he.symm
  · simp only [rows,if_true,List.mem_cons,List.not_mem_nil,or_false] at h
    exact congrArg (fun e : State × Nat => e.1.phase) h

/-- A formula to prove about the computed classes, never a raw class table. -/
def classFormula (s : State) : Nat :=
  8*bit s.outside + 2*kernelCode s + bit s.phase

theorem first_profile_equation : classes model = classFormula := by
  funext s
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel

theorem step_profile_equation : ProfileRules.step (profile model) classFormula = classFormula := by
  funext s
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel

theorem stable_profile_forever (n : Nat) :
    ProfileRules.iterate (profile model) (1+n) = classFormula := by
  induction n with
  | zero => exact first_profile_equation
  | succ n ih =>
    change ProfileRules.step (profile model) (ProfileRules.iterate (profile model) (1+n)) = _
    rw [ih,step_profile_equation]

theorem profile_trajectory :
    ProfileRules.count (profile model) (ProfileRules.seed (profile model)) = 9 ∧
    ProfileRules.count (profile model) (classes model) = 16 ∧
    ProfileRules.count (profile model) (ProfileRules.second (profile model)) = 16 := by
  rw [first_profile_equation]
  change _ ∧ _ ∧ ProfileRules.count (profile model) (ProfileRules.step (profile model) (classes model)) = 16
  rw [first_profile_equation,step_profile_equation]
  decide +kernel

end CSTTT.FullNative
