import CSTTT.POS04.Assigned.C6ActualSupport
import CSTTT.Transport.LumpedFuture

/-! Exact probability lumping closes the future/actual-support link on arbitrary
partial assignments. The existing FiniteBisim6 is enough; equality of individual
hidden rows (ActualBisim6) is NOT added. Every actual branch contributes its
probability and actual updater. The result covers all runs and all finite words,
not just the acquisition closure or the canonical table. -/
namespace CSTTT.POS04.Assigned
open CSTTT.POS04 CSTTT.Objecthood.T1Audit CSTTT.TransportTheory
open LumpedFuture

private theorem fiber_filter {O C : Type} [DecidableEq C]
    (q : O → C) (xs : List O) (w : O → Rat) (c : C) :
    fiber q xs w c = ((xs.filter fun o => decide (q o = c)).map w).sum := by
  induction xs with
  | nil => rfl
  | cons o os ih =>
    simp only [fiber] at ih
    by_cases h : q o = c <;> simp [fiber,h,ih,Rat.zero_add]

private theorem nodup_map_on {X Y : Type} (f : X → Y) (xs : List X)
    (hn : xs.Nodup) (hi : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    have hn := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨y,hy,hf⟩ := List.mem_map.mp h
      have heq := hi x (by simp) y (by simp [hy]) hf.symm
      exact hn.1 (heq ▸ hy)
    · exact ih hn.2 (fun x hx y hy he => hi x (by simp [hx]) y (by simp [hy]) he)

theorem outcomes6_nodup (d : RunInputs6) : (outcomes6 d).Nodup := by
  apply nodup_map_on (predictive6 d) (representatives6 d)
  · exact List.Pairwise.filter _ (by decide : ambientStates.Nodup)
  · intro x hx y hy he
    have hx := of_decide_eq_true (List.mem_filter.mp hx).2
    have hy := of_decide_eq_true (List.mem_filter.mp hy).2
    rw [he] at hx
    exact Option.some.inj (hx.symm.trans hy)

/-- Pushforward of aggregated actual-outcome weights, including duplicate raw
row destinations. Unique Ambient enumeration prevents double counting. -/
theorem actual_weight_class_sum6 (d : RunInputs6) (x : Run6) (a : Action) (c : PredictiveNow) :
    fiber (predictive6 d) ambientStates (actualWeight6 d x a) c = weight6 d x a c := by
  let rs := actualRows6 d x a
  let f := fun o => if predictive6 d o = c then (1 : Rat) else 0
  have hr := regroup rs ambientStates Prod.fst Prod.snd f (by decide)
    (fun e _ => by cases e.1 with
      | inK k => cases k <;> decide
      | p2w0 => decide
      | p5w1 => decide)
  have hleft : (rs.map fun e => e.2 * f e.1).sum =
      ((rs.filter fun e => decide (predictive6 d e.1 = c)).map Prod.snd).sum := by
    rw [← fiber_filter (fun (e : Ambient × Rat) => predictive6 d e.1) rs Prod.snd c]
    unfold fiber
    congr 1
    apply List.map_congr_left
    intro e _
    by_cases h : predictive6 d e.1 = c <;> simp [f,h,Rat.mul_one,Rat.mul_zero]
  have hright : (ambientStates.map fun o => fiber Prod.fst rs Prod.snd o * f o).sum =
      fiber (predictive6 d) ambientStates (actualWeight6 d x a) c := by
    unfold fiber
    congr 1
    apply List.map_congr_left
    intro o _
    have hm : (rs.map fun e => if e.1 = o then e.2 else 0).sum = actualWeight6 d x a o :=
      fiber_filter Prod.fst rs Prod.snd o
    by_cases h : predictive6 d o = c <;> simp only [f,h,if_true,if_false,Rat.mul_one,Rat.mul_zero,hm]
  rw [hleft,hright] at hr
  exact hr.symm.trans (actual_probability_pushforward6 d x a c)

/-- The actual full eight-field trace law equals the existing quotient law;
no actual successor is replaced inside autonomy, and no branch is dropped. -/
theorem actual_word_law6 (a : Assignment) (tag : Tag)
    (h : FiniteBisim6 (runInputs6 a tag)) (x : Run6) (word : List Action) (trace : List C6Observation) :
    fullFuture (actualFuture6 a tag) x word trace = fullFuture (future6 a tag) x word trace := by
  apply future_eq_quotient (actualFuture6 a tag) (future6 a tag)
    (predictive6 (runInputs6 a tag)) (outcomes6_nodup _)
    (fun o _ => outcomes6_cover _ o) (fun _ => rfl)
    (fun x a c => actual_weight_class_sum6 _ x a c)
    (fun x a o _ => (actual_quotient_step6 _ tag x a o).1)
    (assigned6_all_words a tag h)

theorem actual_all_words6 (a : Assignment) (tag : Tag)
    (h : FiniteBisim6 (runInputs6 a tag)) : FullFutureSufficient (actualFuture6 a tag) := by
  intro x y hcode word trace
  rw [actual_word_law6 a tag h,actual_word_law6 a tag h]
  exact assigned6_all_words a tag h x y hcode word trace

theorem accepted_actual_all_words6 {a : Assignment} {tag : Tag} (h : C6Accept a tag) :
    FullFutureSufficient (actualFuture6 a tag) := actual_all_words6 a tag h.2.1

end CSTTT.POS04.Assigned
