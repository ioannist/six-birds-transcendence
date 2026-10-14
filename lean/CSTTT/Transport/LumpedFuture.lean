import CSTTT.Transport.FullFuture
namespace CSTTT.TransportTheory.LumpedFuture
set_option maxRecDepth 4096
variable {O C : Type} [DecidableEq C]
def fiber (q : O → C) (xs : List O) (w : O → Rat) (c : C) :=
  (xs.map fun o => if q o = c then w o else 0).sum

omit [DecidableEq C] in
theorem sum_add (xs : List C) (f g : C → Rat) :
    (xs.map fun c => f c + g c).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp [Rat.zero_add]
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; grind

omit [DecidableEq C] in
theorem sum_zero (xs : List C) : (xs.map fun _ => (0 : Rat)).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,Rat.zero_add]

theorem sum_single (xs : List C) (hn : xs.Nodup) (c : C) (hc : c ∈ xs) (v : Rat) :
    (xs.map fun k => if c = k then v else 0).sum = v := by
  induction xs with
  | nil => simp at hc
  | cons k ks ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hc with he | he
    · subst k
      have hz : (ks.map fun k => if c = k then v else 0).sum = 0 := by
        have hf : ks.map (fun k => if c = k then v else 0) = ks.map (fun _ => (0:Rat)) := by
          apply List.map_congr_left
          intro k hk
          have hne : c ≠ k := fun h => hnd.1 (h ▸ hk)
          simp [hne]
        rw [hf]
        exact sum_zero ks
      simp [hz,Rat.add_zero]
    · have hne : c ≠ k := by intro hh; subst c; exact hnd.1 he
      simp [hne,ih hnd.2 he,Rat.zero_add]

theorem regroup (xs : List O) (cs : List C) (q : O → C) (w : O → Rat) (f : C → Rat)
    (hn : cs.Nodup) (hc : ∀ o ∈ xs, q o ∈ cs) :
    (xs.map fun o => w o * f (q o)).sum =
      (cs.map fun c => fiber q xs w c * f c).sum := by
  induction xs with
  | nil =>
    simp only [List.map_nil,List.sum_nil,fiber,Rat.zero_mul]
    exact (sum_zero cs).symm
  | cons o xs ih =>
    have hterm : (cs.map fun c => (if q o = c then w o else 0) * f c).sum = w o * f (q o) := by
      have he : cs.map (fun c => (if q o = c then w o else 0) * f c) =
          cs.map (fun c => if q o = c then w o * f (q o) else 0) := by
        apply List.map_congr_left
        intro c _
        by_cases h : q o = c <;> simp [h]
      rw [he]
      exact sum_single cs hn _ (hc o (by simp)) _
    simp only [List.map_cons,List.sum_cons,fiber]
    have he : (cs.map fun c => ((if q o = c then w o else 0) + fiber q xs w c) * f c).sum =
        (cs.map fun c => (if q o = c then w o else 0) * f c + fiber q xs w c * f c).sum := by
      congr 1
      apply List.map_congr_left
      intro c _
      exact Rat.add_mul _ _ _
    change w o * f (q o) + (xs.map fun o => w o * f (q o)).sum =
      (cs.map fun c => ((if q o = c then w o else 0) + fiber q xs w c) * f c).sum
    rw [he,sum_add,hterm,← ih (fun o ho => hc o (by simp [ho]))]

/-- Equality of full word laws under checked probability lumping. Both futures
are mathematical interpretations at this engine boundary; a raw-model adapter
must DEFINE them from shared inputs and prove the links on all relevant runs.
No fixed carrier, probability scale, representative or horizon is assumed. -/
theorem future_eq_quotient {S A O Q K V : Type} [DecidableEq Q] [DecidableEq V]
    (actual : FullFutureModel S A O K V) (quotient : FullFutureModel S A Q K V)
    (q : O → Q) (hn : quotient.outcomes.Nodup)
    (hc : ∀ o ∈ actual.outcomes, q o ∈ quotient.outcomes)
    (ho : ∀ x, actual.observe x = quotient.observe x)
    (hw : ∀ x a c, fiber q actual.outcomes (actual.weight x a) c = quotient.weight x a c)
    (hs : ∀ x a o, o ∈ actual.outcomes →
      quotient.code (actual.next x a o) = quotient.code (quotient.next x a (q o)))
    (hb : FullFutureSufficient quotient) (x : S) (word : List A) (trace : List V) :
    fullFuture actual x word trace = fullFuture quotient x word trace := by
  induction word generalizing x trace with
  | nil => simp only [fullFuture,ho]
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      simp only [fullFuture,ho]
      by_cases hfirst : first = quotient.observe x
      · simp only [hfirst,if_true]
        have he : (actual.outcomes.map fun o => actual.weight x a o *
            fullFuture actual (actual.next x a o) rest tail) =
          (actual.outcomes.map fun o => actual.weight x a o *
            fullFuture quotient (quotient.next x a (q o)) rest tail) := by
          apply List.map_congr_left
          intro o hom
          rw [ih,hb _ _ (hs x a o hom) rest tail]
        rw [he,regroup actual.outcomes quotient.outcomes q (actual.weight x a)
          (fun c => fullFuture quotient (quotient.next x a c) rest tail) hn hc]
        simp only [hw]
      · simp only [hfirst,if_false]

/-- The same full code sufficiency, with actual support semantics. -/
theorem sufficient_of_quotient {S A O Q K V : Type} [DecidableEq Q] [DecidableEq V]
    (actual : FullFutureModel S A O K V) (quotient : FullFutureModel S A Q K V)
    (q : O → Q) (hn : quotient.outcomes.Nodup)
    (hc : ∀ o ∈ actual.outcomes, q o ∈ quotient.outcomes)
    (ho : ∀ x, actual.observe x = quotient.observe x)
    (hcode : ∀ x, actual.code x = quotient.code x)
    (hw : ∀ x a c, fiber q actual.outcomes (actual.weight x a) c = quotient.weight x a c)
    (hs : ∀ x a o, o ∈ actual.outcomes →
      quotient.code (actual.next x a o) = quotient.code (quotient.next x a (q o)))
    (hb : FullFutureSufficient quotient) : FullFutureSufficient actual := by
  intro x y hxy word trace
  rw [future_eq_quotient actual quotient q hn hc ho hw hs hb,
    future_eq_quotient actual quotient q hn hc ho hw hs hb]
  exact hb x y (by simpa only [hcode] using hxy) word trace

end CSTTT.TransportTheory.LumpedFuture
