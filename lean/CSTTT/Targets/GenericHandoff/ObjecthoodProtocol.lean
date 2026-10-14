import CSTTT.Targets.GenericHandoff.ObjecthoodCells

/-! Generic C1 audit-protocol binding for package aggregation. Comparison
parameters and reference tables are independently declared raw audit data;
reconstruction and uniqueness still use ObjecthoodRules/FixedPointVerifier.
Neither protocol agreement nor acceptance is a supplied predicate or flag. -/
namespace CSTTT.TargetTheory.GenericHandoff.ObjecthoodProtocol

structure Reference (S : Type) where
  tau : Nat
  epsilon : Rat
  retention : Rat
  publishedP : S → S → Rat
  publishedC : S → Nat → Rat
  publishedU : Nat → S → Rat
  prototypes : List S

variable {Cell S A O : Type} {Value : Cell → Type}

def Matches (ref : Reference S) (d : ObjecthoodRules.Raw S A O) : Prop :=
  d.tau = ref.tau ∧ d.epsilon = ref.epsilon ∧ d.retention = ref.retention ∧
  d.publishedP = ref.publishedP ∧ d.publishedC = ref.publishedC ∧
  d.publishedU = ref.publishedU ∧ d.prototypes = ref.prototypes

variable [DecidableEq S]

def Accept (cfg : ProfileRules.Schema S A O) (ref : Reference S)
    (v : ObjecthoodCells.Bindings Cell Value S A O) (a : Assignment Cell Value) : Prop :=
  ∃ d, ObjecthoodCells.decoded cfg v a = some d ∧ ObjecthoodRules.Accept d ∧ Matches ref d

theorem acceptance_locality (cfg : ProfileRules.Schema S A O) (ref : Reference S)
    (v : ObjecthoodCells.Bindings Cell Value S A O) {a b : Assignment Cell Value}
    (h : Agrees v.scope a b) : Accept cfg ref v a ↔ Accept cfg ref v b := by
  simp only [Accept,ObjecthoodCells.decoder_locality cfg v h]

theorem missing_rejected (cfg : ProfileRules.Schema S A O) (ref : Reference S)
    (v : ObjecthoodCells.Bindings Cell Value S A O) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ v.scope) (hm : a k = none) : ¬ Accept cfg ref v a := by
  simp [Accept,ObjecthoodCells.missing_input cfg v a k hk hm]

theorem verified_unique (cfg : ProfileRules.Schema S A O) (ref : Reference S)
    (v : ObjecthoodCells.Bindings Cell Value S A O) (a : Assignment Cell Value)
    (h : Accept cfg ref v a) :
    ∃ d, ObjecthoodCells.decoded cfg v a = some d ∧
      FixedPointVerifier.Probability d.profile.states (ObjecthoodRules.pi d) ∧
      FixedPointVerifier.Fixed d.profile.states (ObjecthoodRules.E d) (ObjecthoodRules.pi d) ∧
      ∀ x, FixedPointVerifier.Probability d.profile.states x →
        FixedPointVerifier.Fixed d.profile.states (ObjecthoodRules.E d) x → x = ObjecthoodRules.pi d := by
  obtain ⟨d,hd,ha,_⟩ := h
  have hs := ObjecthoodRules.checked_probability_fixed_unique d ha.1
  exact ⟨d,hd,hs⟩

theorem mismatched_protocol_rejected (cfg : ProfileRules.Schema S A O) (ref : Reference S)
    (v : ObjecthoodCells.Bindings Cell Value S A O) (a : Assignment Cell Value)
    (d : ObjecthoodRules.Raw S A O) (hd : ObjecthoodCells.decoded cfg v a = some d)
    (bad : ¬ Matches ref d) : ¬ Accept cfg ref v a := by
  rintro ⟨e,he,_,hm⟩
  have heq := Option.some.inj (he.symm.trans hd)
  subst e
  exact bad hm

end CSTTT.TargetTheory.GenericHandoff.ObjecthoodProtocol
