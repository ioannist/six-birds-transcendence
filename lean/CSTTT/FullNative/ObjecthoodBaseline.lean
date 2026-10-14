import CSTTT.FullNative.Objecthood
namespace CSTTT.FullNative.Objecthood
open CSTTT.TargetTheory.GenericHandoff FixedPointVerifier
set_option autoImplicit false
set_option maxHeartbeats 4000000
def canonicalColumn (s : State) : State :=
  ⟨s.outside,false,if s.u=s.v then false else true,false,s.phase⟩
theorem same_column (r s : State) : P r s=P r (canonicalColumn s) := by
  cases s with
  | mk p u v replica phase =>
    cases u <;> cases v <;> simp [P_formula,canonicalColumn,weight]
def grouped (a b c d : Rat) (s : State) : Rat :=
  if s.outside then 0 else if s.u=s.v then (if s.phase then c else a)
  else (if s.phase then d else b)
theorem fixed_grouped (x : Vector State) (fixed : Fixed states P x) :
    x=grouped (x ⟨false,false,false,false,false⟩) (x ⟨false,false,true,false,false⟩)
      (x ⟨false,false,false,false,true⟩) (x ⟨false,false,true,false,true⟩) := by
  have hc (s : State) : x s=x (canonicalColumn s) := by
    rw [←fixed s,←fixed (canonicalColumn s)]
    have he : (fun r => P r s*x r)=(fun r => P r (canonicalColumn s)*x r) := by
      funext r
      rw [same_column r s]
    simp only [dot,he]
  have outside (s : State) (h : s.outside=true) : x s=0 := by
    rw [←fixed s]
    have hz (r : State) : P r s=0 := by simp [P_formula,h]
    have hg : (fun r => P r s*x r)=(fun _ => (0:Rat)) := by
      funext r
      rw [hz]
      grind
    change mass states (fun r => P r s*x r)=0
    rw [hg]
    exact PositiveMatrix.mass_zero states
  funext s
  cases s with
  | mk p u v replica phase =>
    cases p <;> cases u <;> cases v <;> cases replica <;> cases phase <;>
      simp [grouped,canonicalColumn] at hc ⊢
    all_goals first | exact outside _ rfl | exact hc _

theorem grouped_unique (a b c d : Rat) (prob : mass states (grouped a b c d)=1)
    (fixed : Fixed states P (grouped a b c d)) :
    a=3/44 ∧ b=5/88 ∧ c=3/44 ∧ d=5/88 := by
  have ha := fixed ⟨false,false,false,false,false⟩
  have hb := fixed ⟨false,false,true,false,false⟩
  have hc := fixed ⟨false,false,false,false,true⟩
  have hd := fixed ⟨false,false,true,false,true⟩
  simp [mass,dot,states,bits,grouped,P_formula,weight,diagonal] at prob ha hb hc hd
  grind

theorem baseline_stationary_unique (x : Vector State)
    (prob : Probability states x) (fixed : Fixed states P x) : x=stationary false := by
  have collapsed := fixed_grouped x fixed
  have constraints := grouped_unique _ _ _ _ (by rw [←collapsed];exact prob.2) (by rw [←collapsed];exact fixed)
  rw [collapsed]
  rcases constraints with ⟨ha,hb,hc,hd⟩
  rw [ha,hb,hc,hd]
  funext s
  have hz : (0:Rat)/32=0 := by decide +kernel
  simp [grouped,stationary,epsilon,hz]
theorem baseline_closure_unique (x : Vector State) (prob : Probability states x)
    (fixed : Fixed states (closure false false) x) : x=stationary false := by
  have hc : closure false false=P := by
    rw [closure_power]
    simp only [Bool.false_eq_true,if_false,ObjecthoodRules.power]
    rw [PositiveMatrix.product_identity_left states state_domain.1 state_mem _,unperturbed_eq]
  rw [hc] at fixed
  exact baseline_stationary_unique x prob fixed
end CSTTT.FullNative.Objecthood
