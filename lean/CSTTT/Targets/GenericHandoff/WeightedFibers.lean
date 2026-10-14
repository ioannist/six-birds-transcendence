import Lean

/-! Exact finite weighted-fiber calculus for generic C6. A class-mass check
must not be strengthened to equality of individual outcome probabilities.
No distribution, class partition or verdict is stored by these lemmas. -/
namespace CSTTT.TargetTheory.GenericHandoff.WeightedFibers
variable {X K : Type} [DecidableEq K]

def sum (xs : List X) (f : X → Rat) : Rat := (xs.map f).sum
def mass (xs : List X) (key : X → K) (weight : X → Rat) (k : K) : Rat :=
  sum xs (fun x => if key x = k then weight x else 0)

theorem sum_congr (xs : List X) {f g : X → Rat} (h : ∀ x ∈ xs, f x = g x) : sum xs f = sum xs g :=
  congrArg List.sum (List.map_congr_left h)

theorem sum_zero (xs : List X) : sum xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [sum,Rat.zero_add] using ih

theorem split (xs : List X) (key : X → K) (weight g : X → Rat) (k : K) (value : Rat)
    (hg : ∀ x ∈ xs, key x = k → g x = value) :
    sum xs (fun x => weight x * g x) =
      mass xs key weight k * value +
      sum xs (fun x => (if key x = k then 0 else weight x) * g x) := by
  induction xs with
  | nil => simp [sum,mass,Rat.zero_mul,Rat.add_zero]
  | cons x xs ih =>
    have htail := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy))
    by_cases hk : key x = k
    · have hx := hg x (by simp) hk
      simp only [sum,mass,List.map_cons,List.sum_cons,if_pos hk,hx]
      change weight x * value + sum xs (fun y => weight y * g y) = _
      rw [htail]
      simp only [mass,sum,Rat.add_mul,Rat.zero_mul,Rat.zero_add,Rat.add_assoc]
    · simp only [sum,mass,List.map_cons,List.sum_cons,if_neg hk,Rat.zero_add]
      change weight x * g x + sum xs (fun y => weight y * g y) = _
      rw [htail]
      simp only [mass,sum,Rat.add_left_comm]

theorem outside_mass (xs : List X) (key : X → K) (weight : X → Rat) (k l : K) (hl : l ≠ k) :
    mass xs key (fun x => if key x = k then 0 else weight x) l = mass xs key weight l := by
  apply sum_congr
  intro x hx
  by_cases he : key x = l
  · have hn : key x ≠ k := fun h => hl (he.symm.trans h)
    simp [he,hl]
  · simp [he]

theorem outside_own_mass (xs : List X) (key : X → K) (weight : X → Rat) (k : K) :
    mass xs key (fun x => if key x = k then 0 else weight x) k = 0 := by
  unfold mass
  rw [show sum xs (fun x => if key x = k then (if key x = k then 0 else weight x) else 0) =
    sum xs (fun _ => 0) from sum_congr xs (by intro x hx; by_cases h : key x = k <;> simp [h])]
  exact sum_zero xs

/-- Equal raw mass on every realized fiber suffices for equal weighted
readouts that are constant on fibers. Individual branch weights may differ. -/
theorem weighted_congr (xs : List X) (key : X → K) (w v g : X → Rat)
    (hm : ∀ x ∈ xs, mass xs key w (key x) = mass xs key v (key x))
    (hg : ∀ x ∈ xs, ∀ y ∈ xs, key x = key y → g x = g y) :
    sum xs (fun x => w x * g x) = sum xs (fun x => v x * g x) := by
  induction xs generalizing w v with
  | nil => rfl
  | cons x xs ih =>
    let wo := fun y => if key y = key x then 0 else w y
    let vo := fun y => if key y = key x then 0 else v y
    have hmass : ∀ y ∈ xs, mass xs key wo (key y) = mass xs key vo (key y) := by
      intro y hy
      by_cases he : key y = key x
      · simp only [he,wo,vo,outside_own_mass]
      · rw [outside_mass xs key w _ _ he,outside_mass xs key v _ _ he]
        have hh := hm y (List.mem_cons_of_mem _ hy)
        have hn : key x ≠ key y := Ne.symm he
        simpa only [mass,sum,List.map_cons,List.sum_cons,if_neg hn,Rat.zero_add] using hh
    have hrest := ih wo vo hmass
      (fun y hy z hz => hg y (List.mem_cons_of_mem _ hy) z (List.mem_cons_of_mem _ hz))
    have hsplit (f : X → Rat) := split (x::xs) key f g (key x) (g x)
      (fun y hy he => hg y hy x (by simp) he)
    rw [hsplit w,hsplit v,hm x (by simp)]
    simpa only [sum,wo,vo,List.map_cons,List.sum_cons,if_pos rfl,if_true,Rat.zero_mul,Rat.zero_add]
      using congrArg (fun q => mass (x::xs) key v (key x) * g x + q) hrest

end CSTTT.TargetTheory.GenericHandoff.WeightedFibers
