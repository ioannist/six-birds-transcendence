import CSTTT.Targets.GenericHandoff.FixedPointVerifier
import CSTTT.Objecthood.T1Audit

/-! G6d-2a: a checked algebraic instance on the published T1 kernel, not a
new model. Operation derivation rule: normalize row 0, then Gauss–Jordan in
published index order, selecting the first nonzero pivot, scaling it to one
and clearing the other rows. These exact rational constants follow that rule
from T1Audit.E2eps, itself kernel-computed from the published T1 tables.
The trace is untrusted data until the kernel checks it. No candidate supplied. -/
namespace CSTTT.TargetTheory.GenericHandoff.FixedPointT1
open CSTTT.Objecthood.T1Audit
open FixedPointVerifier

def matrix : FixedPointVerifier.Matrix I := fun i j => (E2eps.num i j : Rat) / E2eps.den

def operations : List (RowOperation I) :=
  [.add 1 0 (-1 / 160 : Rat),
   .add 2 0 (-19 / 640 : Rat),
   .add 3 0 (-19 / 640 : Rat),
   .add 4 0 (-289 / 640 : Rat),
   .add 5 0 (-1 / 160 : Rat),
   .add 6 0 (-1 / 160 : Rat),
   .add 7 0 (-1 / 160 : Rat),
   .add 8 0 (-1 / 160 : Rat),
   .add 9 0 (-289 / 640 : Rat),
   .scale 1 (-1 / 1 : Rat),
   .add 0 1 (-1 / 1 : Rat),
   .scale 2 (-1024 / 349 : Rat),
   .add 0 2 (-1 / 1 : Rat),
   .add 3 2 (-225 / 1024 : Rat),
   .add 4 2 (225 / 512 : Rat),
   .add 9 2 (225 / 512 : Rat),
   .scale 3 (-44672 / 8897 : Rat),
   .add 0 3 (-574 / 349 : Rat),
   .add 2 3 (225 / 349 : Rat),
   .add 4 3 (64575 / 89344 : Rat),
   .add 9 3 (64575 / 89344 : Rat),
   .scale 4 (-1024 / 799 : Rat),
   .add 0 4 (-1 / 1 : Rat),
   .add 9 4 (225 / 1024 : Rat),
   .scale 5 (-1 / 1 : Rat),
   .add 0 5 (-1 / 1 : Rat),
   .scale 6 (-1 / 1 : Rat),
   .add 0 6 (-1 / 1 : Rat),
   .scale 7 (-1 / 1 : Rat),
   .add 0 7 (-1 / 1 : Rat),
   .scale 8 (-1 / 1 : Rat),
   .add 0 8 (-1 / 1 : Rat),
   .scale 9 (-799 / 574 : Rat),
   .add 0 9 (-574 / 799 : Rat),
   .add 4 9 (-225 / 799 : Rat)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem checked : check (List.finRange 10) matrix 0 operations = true := by decide +kernel

theorem universal_unique :
    Probability (List.finRange 10) (candidate matrix 0 operations) ∧
    Fixed (List.finRange 10) matrix (candidate matrix 0 operations) ∧
    (∀ x, Probability (List.finRange 10) x → Fixed (List.finRange 10) matrix x →
      x = candidate matrix 0 operations) :=
  check_sound _ (fun i => by simp) _ _ _ checked
theorem mass_eq_sumRat (x : I → Rat) : mass (List.finRange 10) x = sumRat x := by
  have he : List.finRange 10 = ([0,1,2,3,4,5,6,7,8,9] : List I) := by decide
  simp only [mass,he,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,sumRat]
  grind

theorem probability_iff (x : I → Rat) : Probability (List.finRange 10) x ↔ IsProbability x := by
  simp only [Probability,IsProbability,mass_eq_sumRat]

theorem dot_eq_sumRat (a x : I → Rat) :
    dot (List.finRange 10) a x = sumRat (fun i => a i * x i) := by
  exact mass_eq_sumRat (fun i => a i * x i)

theorem fixed_iff (x : I → Rat) : Fixed (List.finRange 10) matrix x ↔ IsFixed E2eps x := by
  have hd : (E2eps.den : Rat) ≠ 0 := by rw [e2eps_denominator]; decide
  simp only [Fixed,IsFixed,dot_eq_sumRat,matrix,sumRat]
  constructor <;> intro h j
  · have hj := h j
    grind
  · have hj := h j
    grind

/-- Candidate equality follows from the generic checked system, using only
T1's probability and residual proofs, not T1's existing uniqueness theorem. -/
theorem candidate_eq_pi : candidate matrix 0 operations = pi := by
  have hu := universal_unique.2.2 pi ((probability_iff pi).mpr pi_probability)
    ((fixed_iff pi).mpr pi_fixed)
  exact hu.symm

theorem checked_uniqueness_in_T1_terms (x : I → Rat)
    (hp : IsProbability x) (hf : IsFixed E2eps x) : x = pi := by
  rw [← candidate_eq_pi]
  exact universal_unique.2.2 x ((probability_iff x).mpr hp) ((fixed_iff x).mpr hf)

theorem candidate_nonuniform : candidate matrix 0 operations ≠ uniform := by
  rw [candidate_eq_pi]
  exact pi_nonuniform

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem empty_trace_rejected : check (List.finRange 10) matrix 0 [] = false := by decide +kernel

/- Break only the operation trace: erase the final normalization row. -/
set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem zero_scale_rejected :
    check (List.finRange 10) matrix 0 (operations ++ [.scale 0 0]) = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem zero_matrix_rejected :
    check (List.finRange 10) (fun _ _ => 0) 0 operations = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem changed_anchor_rejected :
    check (List.finRange 10) matrix 1 operations = false := by decide +kernel

end CSTTT.TargetTheory.GenericHandoff.FixedPointT1
