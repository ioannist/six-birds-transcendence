import CSTTT.Targets.GenericHandoff.FixedPointT1
import CSTTT.POS04.Assigned.Adapters

/-! Bridge for the algebraic seam, not the completed generic C1 rule layer.
Assignment data reconstructs the actual T1 matrix before the checked generic
trace is used. Missing primitives reject through the existing C1Gate; no
fallback-filled inputs can bypass that gate. -/
namespace CSTTT.TargetTheory.GenericHandoff.FixedPointAssignedT1
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open FixedPointVerifier

def matrixFromInputs (d : Inputs) : Matrix I :=
  fun i j => ((computedE d).num i j : Rat) / (computedE d).den

theorem reconstructed_operator (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    computedE d = E2eps := by
  obtain ⟨hp,hpe,hcu⟩ := reconstructed_matrices d ha hr
  simp [computedE,hpe,hcu,E2eps,Peps2]

theorem matrix_link (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    matrixFromInputs d = FixedPointT1.matrix := by
  exact congrArg (fun E : ScaledMatrix => fun i j => (E.num i j : Rat) / E.den)
    (reconstructed_operator d ha hr)

theorem assigned_check (a : Assignment) (tag : Tag) (h : C1Gate a tag) :
    check (List.finRange 10) (matrixFromInputs (clauseInputs a tag .c1)) 0
      FixedPointT1.operations = true := by
  rw [matrix_link _ h.2.1 h.2.2]
  exact FixedPointT1.checked

/-- The normalized candidate is defined from the assignment's computed matrix.
Universal uniqueness comes from the generic verifier, not a stored property. -/
theorem assigned_universal_unique (a : Assignment) (tag : Tag) (h : C1Gate a tag) :
    let E := matrixFromInputs (clauseInputs a tag .c1)
    Probability (List.finRange 10) (candidate E 0 FixedPointT1.operations) ∧
    Fixed (List.finRange 10) E (candidate E 0 FixedPointT1.operations) ∧
    (∀ x, Probability (List.finRange 10) x → Fixed (List.finRange 10) E x →
      x = candidate E 0 FixedPointT1.operations) :=
  check_sound _ (fun i => by simp) _ _ _ (assigned_check a tag h)

theorem assigned_candidate_eq_pi (a : Assignment) (tag : Tag) (h : C1Gate a tag) :
    candidate (matrixFromInputs (clauseInputs a tag .c1)) 0 FixedPointT1.operations = pi := by
  rw [matrix_link _ h.2.1 h.2.2]
  exact FixedPointT1.candidate_eq_pi

/-- Exact legacy uniqueness conclusion, with the checked generic argument. -/
theorem assigned_uniqueness_legacy (a : Assignment) (tag : Tag) (h : C1Gate a tag)
    (x : I → Rat) (hp : IsProbability x) (hf : IsFixed (computedE (clauseInputs a tag .c1)) x) : x = pi := by
  rw [reconstructed_operator _ h.2.1 h.2.2] at hf
  exact FixedPointT1.checked_uniqueness_in_T1_terms x hp hf

/-- All other audit components retain their T1 proofs. Only uniqueness is
supplied by the newly checked generic row-reduction argument. -/
theorem assigned_audit_via_verifier (a : Assignment) (tag : Tag) (h : C1Gate a tag) :
    C1Audit (clauseInputs a tag .c1) := by
  let d := clauseInputs a tag .c1
  obtain ⟨hp,hpe,hcu⟩ := reconstructed_matrices d h.2.1 h.2.2
  have he : computedE d = E2eps := reconstructed_operator d h.2.1 h.2.2
  have hz : computedEzero d = E2zero := by simp [computedEzero,hp,hcu,E2zero,P2]
  have ht : d.audit.retention = 3/4 := by rw [h.2.1.1]; rfl
  change C1Audit d
  rw [C1Audit,he,hz,ht]
  exact ⟨pi_probability,pi_fixed,FixedPointT1.checked_uniqueness_in_T1_terms,
    pi_nonuniform,pi_core_mass,pi_core_retention,pi_tv_from_core_uniform,e2eps_defect,e2zero_defect⟩
/-- Fixed-family specialization only. The completed polymorphic C1 rule will
also reconstruct closure/quotient/perturbation data from generic typed cells. -/
def VerifiedT1Accept (a : Assignment) (tag : Tag) : Prop :=
  C1Gate a tag ∧ check (List.finRange 10) (matrixFromInputs (clauseInputs a tag .c1))
    0 FixedPointT1.operations = true

theorem verified_iff_legacy (a : Assignment) (tag : Tag) : VerifiedT1Accept a tag ↔ C1Accept a tag := by
  constructor
  · intro h
    exact ⟨h.1,assigned_audit_via_verifier a tag h.1⟩
  · intro h
    exact ⟨h.1,assigned_check a tag h.1⟩

theorem verified_locality {a b : Assignment} (tag : Tag)
    (h : Agrees (clauseScope tag .c1) a b) : VerifiedT1Accept a tag ↔ VerifiedT1Accept b tag := by
  rw [verified_iff_legacy,verified_iff_legacy]
  exact c1_acceptance_locality h

theorem canonical_verified (tag : Tag) : VerifiedT1Accept canonical tag :=
  (verified_iff_legacy _ _).mpr (canonical_c123 tag).1

theorem missing_dependency_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c1) : ¬ VerifiedT1Accept (put a k none) tag := by
  intro h
  exact missing_cell_rejected _ a k hk h.1.1.1

theorem neg_c1_table_transferred (tag : Tag) :
    if tag = .target then ¬ VerifiedT1Accept (negC1Table canonical) tag
    else VerifiedT1Accept (negC1Table canonical) tag := by
  cases tag
  · exact (verified_iff_legacy _ _).mpr (neg_c1_table_outcomes .source).1
  · exact fun h => (neg_c1_table_outcomes .target).1 ((verified_iff_legacy _ _).mp h)

theorem neg_c2_split_preserves_c1 (tag : Tag) : VerifiedT1Accept (negC2Split canonical) tag :=
  (verified_iff_legacy _ _).mpr (neg_c2_split_outcomes tag).1

theorem neg_c3_profile_c1_transferred (tag : Tag) :
    if tag = .target then ¬ VerifiedT1Accept (negC3Profile canonical) tag
    else VerifiedT1Accept (negC3Profile canonical) tag := by
  cases tag
  · exact (verified_iff_legacy _ _).mpr (neg_c3_profile_outcomes .source).1
  · exact fun h => (neg_c3_profile_outcomes .target).1 ((verified_iff_legacy _ _).mp h)

end CSTTT.TargetTheory.GenericHandoff.FixedPointAssignedT1
