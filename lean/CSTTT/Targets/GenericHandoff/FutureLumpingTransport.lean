import CSTTT.Targets.GenericHandoff.FutureLumping

/-! Internal reindexing engine for the raw runtime adapters. Applicability is
proved by equations on ALL states, actual branch weights and successors.
Equal class mass is preserved; individual branch equality is not assumed. -/
namespace CSTTT.TargetTheory.GenericHandoff.FutureLumping
open CSTTT.TransportTheory
variable {S T A B O C K V W : Type} [DecidableEq C] [DecidableEq K]

theorem transport_one_step
    (old : FullFutureModel S A O C V) (new : FullFutureModel T B O K W)
    (state : T → S) (action : B → A) (codeMap : C → K) (obsMap : V → W)
    (injective : Function.Injective codeMap)
    (outcomes : new.outcomes = old.outcomes)
    (code : ∀ x, new.code x = codeMap (old.code (state x)))
    (observe : ∀ x, new.observe x = obsMap (old.observe (state x)))
    (weight : ∀ x a o, new.weight x a o = old.weight (state x) (action a) o)
    (next : ∀ x a o, state (new.next x a o) = old.next (state x) (action a) o)
    (hb : OneStep old) : OneStep new := by
  have hnext (x : T) (a : B) (o : O) :
      NextCode new x a o = codeMap (NextCode old (state x) (action a) o) := by
    simp only [NextCode,code,next]
  have fiber (x y : T) (a : B) (o : O) :
      WeightedFibers.mass new.outcomes (NextCode new x a) (new.weight y a) (NextCode new x a o) =
      WeightedFibers.mass old.outcomes (NextCode old (state x) (action a))
        (old.weight (state y) (action a)) (NextCode old (state x) (action a) o) := by
    rw [outcomes]
    apply WeightedFibers.sum_congr
    intro q _
    simp only [hnext,weight]
    have hi : codeMap (NextCode old (state x) (action a) q) =
        codeMap (NextCode old (state x) (action a) o) ↔
        NextCode old (state x) (action a) q = NextCode old (state x) (action a) o :=
      ⟨fun h => injective h,congrArg codeMap⟩
    simp only [hi]
  intro x y hc
  have ho : old.code (state x) = old.code (state y) := injective (by simpa only [code] using hc)
  have hh := hb (state x) (state y) ho
  refine ⟨by rw [observe,observe,hh.1],?_⟩
  intro a
  refine ⟨?_,?_⟩
  · intro o hm
    rw [hnext,hnext,(hh.2 (action a)).1 o (outcomes ▸ hm)]
  · intro o hm
    rw [fiber,fiber]
    exact (hh.2 (action a)).2 o (outcomes ▸ hm)
end CSTTT.TargetTheory.GenericHandoff.FutureLumping
