import CSTTT.Targets.GenericHandoff.ProfileRules
namespace CSTTT.TargetTheory.GenericHandoff.ProfileRules
variable {S X Y : Type} [BEq X] [LawfulBEq X] [BEq Y] [LawfulBEq Y]
/-- First-occurrence class numbering depends only on equality of raw readouts. -/
theorem normalized_eq (xs : List S) (f : S → X) (g : S → Y)
    (h : ∀ s t, f s = f t ↔ g s = g t) (s : S) :
    (xs.map f).eraseDups.idxOf (f s) = (xs.map g).eraseDups.idxOf (g s) := by
  classical
  induction n : xs.length using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.map_cons,List.eraseDups_cons,List.filter_map,Function.comp_def]
      have hf : (xs.filter fun y => !(f y == f x)) = (xs.filter fun y => !(g y == g x)) := by
        apply List.filter_congr
        intro y _
        apply congrArg Bool.not
        apply Bool.eq_iff_iff.mpr
        simpa only [beq_iff_eq] using h y x
      rw [hf]
      simp only [List.idxOf_cons,cond_eq_ite,beq_iff_eq]
      by_cases he : f x = f s
      · simp [he,(h x s).mp he]
      · simp only [if_neg he,if_neg (fun hg => he ((h x s).mpr hg))]
        congr 1
        exact ih _ (by have := List.length_filter_le (fun y => !(g y == g x)) xs; simp only [List.length_cons] at n; omega) _ rfl
theorem idx_injective (xs : List X) (x y : X) (hx : x ∈ xs) (hy : y ∈ xs)
    (he : xs.idxOf x = xs.idxOf y) : x = y := by
  classical
  induction xs with
  | nil => simp at hx
  | cons z xs ih =>
    simp only [List.idxOf_cons,cond_eq_ite,beq_iff_eq] at he
    by_cases hzx : z = x <;> by_cases hzy : z = y
    · exact hzx.symm.trans hzy
    · simp only [if_pos hzx,if_neg hzy] at he; omega
    · simp only [if_neg hzx,if_pos hzy] at he; omega
    · apply ih
      · rcases List.mem_cons.mp hx with he | he; exact (hzx he.symm).elim; exact he
      · rcases List.mem_cons.mp hy with he | he; exact (hzy he.symm).elim; exact he
      · simp only [if_neg hzx,if_neg hzy] at he; omega

theorem dedup_mem (xs : List X) (x : X) : x ∈ xs.eraseDups ↔ x ∈ xs := by
  classical
  induction n : xs.length using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    cases xs with
    | nil => simp
    | cons y xs =>
      rw [List.eraseDups_cons]
      rw [List.mem_cons,ih _ (by have := List.length_filter_le (fun z => !(z == y)) xs; simp only [List.length_cons] at n; omega) _ rfl]
      simp only [List.mem_filter, Bool.not_eq_true',beq_eq_false_iff_ne,List.mem_cons]
      grind

theorem normalized_partition (xs : List S) (f : S → X) (s t : S)
    (hs : s ∈ xs) (ht : t ∈ xs) :
    ((xs.map f).eraseDups.idxOf (f s) = (xs.map f).eraseDups.idxOf (f t)) ↔ f s = f t := by
  constructor
  · exact idx_injective _ _ _ ((dedup_mem _ _).mpr (List.mem_map.mpr ⟨s,hs,rfl⟩))
      ((dedup_mem _ _).mpr (List.mem_map.mpr ⟨t,ht,rfl⟩))
  · intro h; rw [h]
omit [LawfulBEq X] in
theorem dedup_length_le (xs : List X) : xs.eraseDups.length ≤ xs.length := by
  classical
  induction n : xs.length using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [List.eraseDups_cons,List.length_cons]
      have hf := List.length_filter_le (fun z => !(z == x)) xs
      have hh := ih (xs.filter fun z => !(z == x)).length (by simp only [List.length_cons] at n; omega) (xs.filter fun z => !(z == x)) rfl
      simp only [List.length_cons] at n ⊢; omega

variable {A O : Type} [DecidableEq S]
omit [DecidableEq S] in
theorem step_lt (d : Raw S A O) (c : S → Nat) (s : S) (hs : s ∈ d.states) :
    step d c s < d.states.length := by
  have hm := (dedup_mem (d.states.map (signature d c)) (signature d c s)).mpr (List.mem_map.mpr ⟨s,hs,rfl⟩)
  have ht := List.idxOf_lt_length_of_mem hm
  have hl := dedup_length_le (d.states.map (signature d c))
  simp only [List.length_map] at hl
  exact Nat.lt_of_lt_of_le ht hl

omit [DecidableEq S] in
/-- Computed first-occurrence labels are canonical: equality of their
partitions implies equality of the numbered functions, not merely relabeling. -/
theorem step_partition_eq (d : Raw S A O) (c e : S → Nat)
    (coverage : ∀ s, s ∈ d.states) (h : SamePartition (step d c) (step d e)) :
    step d c = step d e := by
  have hs (s t : S) : signature d c s = signature d c t ↔ signature d e s = signature d e t := by
    rw [← normalized_partition d.states (signature d c) s t (coverage s) (coverage t),
      ← normalized_partition d.states (signature d e) s t (coverage s) (coverage t)]
    exact h s t
  funext s
  exact normalized_eq d.states _ _ hs s

omit [DecidableEq S] in
/-- At positive refinement depth, adjacent partition agreement certifies an
actual fixed point because both profiles use the same canonical numbering. -/
theorem normalized_adjacent_fixed (d : Raw S A O) (c : S → Nat)
    (coverage : ∀ s, s ∈ d.states)
    (h : SamePartition (step d c) (step d (step d c))) :
    step d (step d (step d c)) = step d (step d c) := by
  have he := step_partition_eq d c (step d c) coverage h
  conv => lhs; rw [← he]
end CSTTT.TargetTheory.GenericHandoff.ProfileRules
