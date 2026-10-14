import CSTTT.Targets.GenericHandoff.StrategyGame
/-! Exact scaled natural rows. Positivity, mass and support are proved for
arbitrary rows and a positive scale; no POS-04 table or bounded horizon occurs. -/
namespace CSTTT.TargetTheory.GenericHandoff.ScaledRows
variable {O : Type}
def probabilities (scale : Nat) (row : List (O × Nat)) : List (O × Rat) :=
  row.map fun e => (e.1,(e.2 : Rat)/(scale : Rat))

theorem sum_scaled (scale : Nat) (row : List (O × Nat)) :
    ((probabilities scale row).map Prod.snd).sum = ((row.map Prod.snd).sum : Rat) / (scale : Rat) := by
  induction row with
  | nil => simp [probabilities,Rat.div_def,Rat.zero_mul]
  | cons e es ih =>
    simp only [probabilities,List.map_cons,List.sum_cons,Rat.natCast_add] at ih ⊢
    grind

theorem positive (scale n : Nat) (hs : scale > 0) (hn : n > 0) :
    (0 : Rat) < (n : Rat)/(scale : Rat) := by
  have hs' : (0 : Rat) < scale := Rat.natCast_pos.mpr hs
  have hn' : (0 : Rat) < n := Rat.natCast_pos.mpr hn
  exact Rat.mul_pos hn' (Rat.inv_pos.mpr hs')

theorem normalized (scale : Nat) (row : List (O × Nat))
    (hs : scale > 0) (hn : row ≠ []) (ht : (row.map Prod.snd).sum = scale)
    (hp : ∀ e ∈ row, e.2 > 0) :
    (∀ e ∈ probabilities scale row, 0 ≤ e.2) ∧
    ((probabilities scale row).map Prod.snd).sum = 1 ∧
    ∃ o w, (o,w) ∈ probabilities scale row ∧ 0 < w := by
  refine ⟨?_,?_,?_⟩
  · intro e he
    obtain ⟨raw,hr,rfl⟩ := List.mem_map.mp he
    exact Rat.le_of_lt (positive scale raw.2 hs (hp raw hr))
  · rw [sum_scaled,ht]
    have hz : (scale : Rat) ≠ 0 := Rat.ne_of_gt (Rat.natCast_pos.mpr hs)
    exact Rat.mul_inv_cancel _ hz
  · obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil row hn
    exact ⟨e.1,(e.2 : Rat)/(scale : Rat),List.mem_map.mpr ⟨e,he,rfl⟩,positive scale e.2 hs (hp e he)⟩
end CSTTT.TargetTheory.GenericHandoff.ScaledRows
