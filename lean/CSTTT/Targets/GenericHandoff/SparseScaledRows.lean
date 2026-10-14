import CSTTT.Targets.GenericHandoff.StrictSparseGame
import CSTTT.Targets.GenericHandoff.ScaledRows

/-! Exact format/normalization inverse for arbitrary natural rows. These laws
recover closure from a normalized selected response AND all-support safety,
not from resource legality. Zero entries fail even inside the safe set. -/
namespace CSTTT.TargetTheory.GenericHandoff.SparseScaledRows
open StrategyGame StrictSparseGame
variable {O : Type}

theorem positive_iff (scale n : Nat) (hs : scale > 0) :
    (0 : Rat) < (n : Rat)/(scale : Rat) ↔ n > 0 := by
  constructor
  · intro hp
    by_cases hn : n = 0
    · subst n
      have hz : ((0 : Nat) : Rat) = 0 := by decide +kernel
      simp only [hz,Rat.div_def,Rat.zero_mul] at hp
      exact False.elim (Rat.lt_irrefl hp)
    · omega
  · exact ScaledRows.positive scale n hs

theorem sparse_iff (scale : Nat) (row : List (O × Nat)) (hs : scale > 0) :
    StrictSparse (ScaledRows.probabilities scale row) ↔ ∀ e ∈ row, e.2 > 0 := by
  constructor
  · intro h e he
    exact (positive_iff scale e.2 hs).mp (h _ (List.mem_map.mpr ⟨e,he,rfl⟩))
  · intro h e he
    obtain ⟨raw,hr,rfl⟩ := List.mem_map.mp he
    exact ScaledRows.positive scale raw.2 hs (h raw hr)

theorem mass_iff (scale : Nat) (row : List (O × Nat)) (hs : scale > 0) :
    ((ScaledRows.probabilities scale row).map Prod.snd).sum = 1 ↔
      (row.map Prod.snd).sum = scale := by
  rw [ScaledRows.sum_scaled]
  have hscale : (scale : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hs)
  constructor
  · intro ht
    have he : ((row.map Prod.snd).sum : Rat) = (scale : Rat) := by grind
    exact Rat.natCast_inj.mp he
  · intro ht
    rw [ht]
    exact Rat.mul_inv_cancel _ hscale

/-- Finite-row closure in exactly the frozen sparse format. Duplicates and
order remain unconstrained; safety quantifies every positive support outcome. -/
theorem closed_iff (scale : Nat) (row : List (O × Nat)) (hs : scale > 0)
    (inside : O → Prop) :
    (row ≠ [] ∧ (row.map Prod.snd).sum = scale ∧ ∀ e ∈ row, e.2 > 0 ∧ inside e.1) ↔
    (StrictSparse (ScaledRows.probabilities scale row) ∧
      Normalized (fun (_ : Unit) (_ : Unit) (_ : Unit) => ScaledRows.probabilities scale row) () () () ∧
      ∀ o, PositiveSupport (fun (_ : Unit) (_ : Unit) (_ : Unit) => ScaledRows.probabilities scale row)
        () () () o → inside o) := by
  constructor
  · rintro ⟨hn,ht,hi⟩
    have hp := fun e he => (hi e he).1
    have normalized := ScaledRows.normalized scale row hs hn ht hp
    refine ⟨(sparse_iff scale row hs).mpr hp,⟨normalized.1,normalized.2.1,?_⟩,?_⟩
    · obtain ⟨o,w,he,hw⟩ := normalized.2.2
      exact ⟨o,w,he,hw⟩
    · rintro o ⟨w,hw,_⟩
      obtain ⟨e,he,heq⟩ := List.mem_map.mp hw
      have ho : e.1 = o := congrArg Prod.fst heq
      rw [← ho]
      exact (hi e he).2
  · rintro ⟨hsparse,hn,hi⟩
    have hp := (sparse_iff scale row hs).mp hsparse
    refine ⟨?_,(mass_iff scale row hs).mp hn.2.1,?_⟩
    · intro he
      obtain ⟨o,w,hw,_⟩ := hn.2.2
      simp [ScaledRows.probabilities,he] at hw
    · intro e he
      exact ⟨hp e he,hi e.1 ⟨(e.2 : Rat)/(scale : Rat),
        List.mem_map.mpr ⟨e,he,rfl⟩,ScaledRows.positive scale e.2 hs (hp e he)⟩⟩

end CSTTT.TargetTheory.GenericHandoff.SparseScaledRows
