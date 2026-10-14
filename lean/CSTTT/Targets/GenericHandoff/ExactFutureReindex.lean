import CSTTT.Targets.GenericHandoff.FutureReindex

/-! Exact semantic adapter engine. Surjectivity of both state and action
representations retains ALL states and ALL finite words in both directions.
These are internal interpretation equations, not free future candidates at
the RawHandoff boundary; the instance must use its defined raw interpreters. -/
namespace CSTTT.TransportTheory.FutureReindex
variable {S T A B O C K V W : Type} [DecidableEq V] [DecidableEq W]

theorem sufficient_iff
    (old : FullFutureModel S A O C V) (new : FullFutureModel T B O K W)
    (state : T → S) (action : B → A) (obs : V → W)
    (stateOnto : ∀ s, ∃ t, state t = s) (actionOnto : ∀ a, ∃ b, action b = a)
    (hi : ∀ x y, obs x = obs y → x = y)
    (hout : new.outcomes = old.outcomes)
    (hobs : ∀ x, new.observe x = obs (old.observe (state x)))
    (hweight : ∀ x b o, new.weight x b o = old.weight (state x) (action b) o)
    (hnext : ∀ x b o, state (new.next x b o) = old.next (state x) (action b) o)
    (hcode : ∀ x y, new.code x = new.code y ↔ old.code (state x) = old.code (state y)) :
    FullFutureSufficient new ↔ FullFutureSufficient old := by
  classical
  constructor
  · intro hn x y hc word trace
    obtain ⟨sx,hsx⟩ := stateOnto x
    obtain ⟨sy,hsy⟩ := stateOnto y
    let lift : A → B := fun a => Classical.choose (actionOnto a)
    have hl : ∀ a, action (lift a) = a := fun a => Classical.choose_spec (actionOnto a)
    have hw : (word.map lift).map action = word := by
      induction word with
      | nil => rfl
      | cons a rest ih => simp only [List.map_cons,hl,ih]
    have hcodes : new.code sx = new.code sy := (hcode sx sy).mpr (by simpa [hsx,hsy] using hc)
    have he := hn sx sy hcodes (word.map lift) (trace.map obs)
    rw [mapped_word_law old new state action obs hi hout hobs hweight hnext,
      mapped_word_law old new state action obs hi hout hobs hweight hnext,hsx,hsy,hw] at he
    exact he
  · exact sufficient_transport old new state action obs hi hout hobs hweight hnext
      (fun x y h => (hcode x y).mp h)

end CSTTT.TransportTheory.FutureReindex
