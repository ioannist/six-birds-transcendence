import CSTTT.Targets.GenericHandoff.ProfileNormalization
import CSTTT.Targets.GenericHandoff.POS04ProfileRules

/-! Exact completion of the POS-04 C3 rule, for arbitrary partial assignments.
The extra dispatcher fixed-point/block gate is derived from the old acceptance
check, not added as a restriction on the assignment family. Positive depth is
essential; no claim is made for the previously rejected depth-zero argument. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ProfileRules
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

theorem support_blocks (d : Inputs) :
    ProfileRules.BlockCoverage (raw d) (ProfileRules.first (raw d)) ∧
    ProfileRules.BlockCoverage (raw d) (ProfileRules.second (raw d)) := by
  have hs (s : KState) : s ∈ (raw d).states := by change s ∈ kernel; cases s <;> decide
  have hf (s : KState) : ProfileRules.first (raw d) s < 10 :=
    ProfileRules.step_lt (raw d) (ProfileRules.seed (raw d)) s (hs s)
  have ht (s : KState) : ProfileRules.second (raw d) s < 10 :=
    ProfileRules.step_lt (raw d) (ProfileRules.first (raw d)) s (hs s)
  constructor
  all_goals
    intro s _ a _ e _
    cases e.1 with
    | inK k =>
      change _ ∈ List.range 12
      apply List.mem_range.mpr
      first | exact Nat.lt_trans (hf k) (by decide) | exact Nat.lt_trans (ht k) (by decide)
    | p2w0 => change 10 ∈ List.range 12; decide
    | p5w1 => change 11 ∈ List.range 12; decide

theorem genuine_stabilization (d : Inputs) (h : C3Rule d) :
    ProfileRules.StableProfile (raw d) := by
  have hp := (profile_iff d).mpr h
  refine ⟨hp,?_,(support_blocks d).1,(support_blocks d).2⟩
  exact ProfileRules.normalized_adjacent_fixed (raw d) (ProfileRules.seed (raw d))
    (by intro s; change s ∈ kernel; cases s <;> decide) hp.2.2.2.1

/-- The dispatcher completion adds no hypothesis to the existing family gate. -/
theorem accepted_completion (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : C3Accept a tag) :
    ∃ d labels, ProfileRules.decodedClause clauseSchema (clauseBindings tag) a = some (d,labels) ∧
      ProfileRules.StableProfile d := by
  refine ⟨raw (clauseInputs a tag .c3),(clauseInputs a tag .c3).publishedM,?_,genuine_stabilization _ h.2⟩
  rw [clause_decode_eq a tag .c3 (Or.inr rfl),if_pos h.1.1.1,
    raw_scoped a tag .c3 (Or.inr rfl),labels_scoped a tag .c3 (Or.inr rfl)]

end CSTTT.TargetTheory.GenericHandoff.POS04ProfileRules
