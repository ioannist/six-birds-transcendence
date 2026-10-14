import CSTTT.Transport.FullFuture
import CSTTT.Transport.LumpedFuture

/-! Interpretation-parametric trace transport. Raw adapters must prove the
readout, weight and updater equations on ALL states. An observation embedding
changes representation only; traces outside its image have zero probability.
These are internal engine arguments, not candidate fields of a raw model. -/
namespace CSTTT.TransportTheory.FutureReindex

variable {S T A B O C K V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
private theorem list_injective (f : V → W) (hi : ∀ x y, f x = f y → x = y)
    (xs ys : List V) (h : xs.map f = ys.map f) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have he := List.cons.inj h
      rw [hi x y he.1,ih ys he.2]

theorem mapped_word_law
    (old : FullFutureModel S A O C V) (new : FullFutureModel T B O K W)
    (state : T → S) (action : B → A) (obs : V → W)
    (hi : ∀ x y, obs x = obs y → x = y)
    (hout : new.outcomes = old.outcomes)
    (hobs : ∀ x, new.observe x = obs (old.observe (state x)))
    (hweight : ∀ x b o, new.weight x b o = old.weight (state x) (action b) o)
    (hnext : ∀ x b o, state (new.next x b o) = old.next (state x) (action b) o)
    (x : T) (word : List B) (trace : List V) :
    fullFuture new x word (trace.map obs) = fullFuture old (state x) (word.map action) trace := by
  induction word generalizing x trace with
  | nil =>
    have he : trace.map obs = [obs (old.observe (state x))] ↔ trace = [old.observe (state x)] :=
      ⟨fun h => list_injective obs hi _ _ h,fun h => h ▸ rfl⟩
    simp only [List.map_nil,fullFuture,hobs,he]
  | cons b word ih =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      have he : obs first = obs (old.observe (state x)) ↔ first = old.observe (state x) :=
        ⟨hi _ _,fun h => congrArg obs h⟩
      simp only [List.map_cons,fullFuture,hobs,he]
      by_cases hf : first = old.observe (state x)
      · simp only [hf,if_true,hout]
        congr 1
        apply List.map_congr_left
        intro o _
        rw [hweight,ih,hnext]
      · simp only [hf,if_false]

omit [DecidableEq V] in
theorem outside_image_zero (m : FullFutureModel T B O K W) (obs : V → W)
    (hobs : ∀ x, ∃ v, obs v = m.observe x)
    (x : T) (word : List B) (trace : List W)
    (hn : ¬ ∃ t : List V, t.map obs = trace) : fullFuture m x word trace = 0 := by
  induction word generalizing x trace with
  | nil =>
    have he : trace ≠ [m.observe x] := by
      intro he
      obtain ⟨v,hv⟩ := hobs x
      exact hn ⟨[v],by simpa [hv] using he.symm⟩
    simp [fullFuture,he]
  | cons b word ih =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      by_cases hf : ∃ v, obs v = first
      · obtain ⟨v,hv⟩ := hf
        have ht : ¬ ∃ t : List V, t.map obs = tail := by
          rintro ⟨t,ht⟩
          exact hn ⟨v::t,by simp only [List.map_cons,hv,ht]⟩
        simp only [fullFuture]
        by_cases he : first = m.observe x
        · simp only [he,if_true,ih _ _ ht,Rat.mul_zero]
          exact LumpedFuture.sum_zero _
        · simp only [he,if_false]
      · have he : first ≠ m.observe x := by
          intro he
          obtain ⟨v,hv⟩ := hobs x
          exact hf ⟨v,hv.trans he.symm⟩
        simp only [fullFuture,he,if_false]

theorem sufficient_transport
    (old : FullFutureModel S A O C V) (new : FullFutureModel T B O K W)
    (state : T → S) (action : B → A) (obs : V → W)
    (hi : ∀ x y, obs x = obs y → x = y)
    (hout : new.outcomes = old.outcomes)
    (hobs : ∀ x, new.observe x = obs (old.observe (state x)))
    (hweight : ∀ x b o, new.weight x b o = old.weight (state x) (action b) o)
    (hnext : ∀ x b o, state (new.next x b o) = old.next (state x) (action b) o)
    (hcode : ∀ x y, new.code x = new.code y → old.code (state x) = old.code (state y))
    (hs : FullFutureSufficient old) : FullFutureSufficient new := by
  classical
  intro x y hc word trace
  by_cases ht : ∃ t : List V, t.map obs = trace
  · obtain ⟨t,rfl⟩ := ht
    rw [mapped_word_law old new state action obs hi hout hobs hweight hnext,
        mapped_word_law old new state action obs hi hout hobs hweight hnext]
    exact hs _ _ (hcode x y hc) _ _
  · have hp : ∀ r, ∃ v, obs v = new.observe r :=
      fun r => ⟨old.observe (state r),(hobs r).symm⟩
    rw [outside_image_zero new obs hp x word trace ht,
        outside_image_zero new obs hp y word trace ht]

end CSTTT.TransportTheory.FutureReindex
