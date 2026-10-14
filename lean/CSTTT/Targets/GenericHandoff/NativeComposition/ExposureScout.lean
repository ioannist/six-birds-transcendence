import CSTTT.Targets.GenericHandoff.NativeComposition.Factor
import CSTTT.Targets.GenericHandoff.ExposureRules

/-! The always-available native candidate cannot populate C4, for any split,
channel list, policy or connector history. Supported edges preserve visible;
the only nonconstant channels cannot collide within such a component. This
refutes actual surrogate acceptance, not merely a chosen sufficient check. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ExposureScout

def schema (pair : Factor × Factor) : ExposureRules.Schema Factor Bool Factor Unit :=
  ⟨{clauseSchema with split := pair},()⟩
def raw (channels : List ExposureRules.Channel) (policy : Factor → Bool) (history : List Factor) :
    ExposureRules.Raw Factor Bool Factor Unit :=
  ⟨(factorData false).rows,(factorData false).positions,(factorData false).hazards,
    channels,policy,fun _ => history,labels⟩

theorem predictive_equation (pair) (channels) (policy) (history) (s : Factor) :
    ExposureRules.predictive (schema pair) (raw channels policy history) s =
      (bit s.1,[[s.2.1],[s.2.1]]) := rfl

theorem supported_visible (pair) (channels) (policy) (history) (s t : Factor)
    (h : ExposureRules.weight (schema pair) (raw channels policy history) s t > 0) :
    s.2.1=t.2.1 := by
  have hd : destination s (policy s)=t := by
    by_cases he : destination s (policy s)=t
    · exact he
    · simp [ExposureRules.weight,schema,raw,factorData,clauseSchema,he] at h
  rw [← hd]
  cases policy s <;> simp [destination,probe]

theorem path_visible (pair) (channels) (policy) (history : List Factor)
    (h : (history.zip (history.drop 1)).all (fun e => decide
      (ExposureRules.weight (schema pair) (raw channels policy history) e.1 e.2 > 0))=true) :
    ∀ s ∈ history, ∀ t ∈ history, s.2.1=t.2.1 := by
  -- The weight does not consume the history field, so induction keeps it fixed.
  let d := raw channels policy history
  have chain : ∀ xs : List Factor,
      (xs.zip (xs.drop 1)).all (fun e => decide
        (ExposureRules.weight (schema pair) d e.1 e.2 > 0))=true →
      ∀ s ∈ xs, ∀ t ∈ xs, s.2.1=t.2.1 := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      cases xs with
      | nil => simp
      | cons y ys =>
        intro hh
        have he : ExposureRules.weight (schema pair) d x y > 0 := by
          simpa using (Bool.and_eq_true_iff.mp hh).1
        have ht : ((y::ys).zip ((y::ys).drop 1)).all (fun e => decide
            (ExposureRules.weight (schema pair) d e.1 e.2 > 0))=true :=
          (Bool.and_eq_true_iff.mp hh).2
        have hv := supported_visible pair channels policy history x y he
        have tail := ih ht
        intro s hs t hm
        rw [List.mem_cons] at hs hm
        rcases hs with rfl | hs <;> rcases hm with rfl | hm
        · rfl
        · exact hv.trans (tail y (by simp) t hm)
        · exact (tail s hs y (by simp)).trans hv.symm
        · exact tail s hs t hm
  exact chain history h

theorem current_component {X Y : Type} (xs : List X) (f g : X → Y)
    (h : xs.map f=xs.map g) : ∀ x ∈ xs, f x=g x := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have he := List.cons.inj h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact he.1
    · exact ih he.2 y hy

theorem actual_c4_rejected (pair : Factor × Factor) (channels : List ExposureRules.Channel)
    (policy : Factor → Bool) (history : List Factor) :
    ¬ ExposureRules.SurrogateAccept (schema pair) (raw channels policy history) := by
  intro ha
  have hp := path_visible pair channels policy history ha.2.2.1.1
  have hfirst : pair.1 ∈ history := List.mem_of_head? ha.1.2.2.2.1
  have hlast : pair.2 ∈ history := List.mem_of_getLast? ha.1.2.2.2.2.1
  have hv := hp pair.1 hfirst pair.2 hlast
  obtain ⟨c,hc,⟨s,t,hn⟩,hf⟩ := ha.2.2.2
  have he := current_component channels
    (ExposureRules.channel (schema pair) (raw channels policy history) · pair.1)
    (ExposureRules.channel (schema pair) (raw channels policy history) · pair.2) ha.2.1.1 c hc
  cases c with
  | availability =>
    exact hn (by simp [ExposureRules.channel,schema,raw,factorData,clauseSchema])
  | predictive =>
    exact ha.2.1.2 (by simpa [ExposureRules.channel] using he)
  | position =>
    have hb : bit pair.1.1=bit pair.2.1 := by
      simpa [ExposureRules.channel,raw,factorData] using congrArg (fun z => z.1.1) he
    apply ha.2.1.2
    change ExposureRules.predictive (schema pair) (raw channels policy history) pair.1 =
      ExposureRules.predictive (schema pair) (raw channels policy history) pair.2
    simp only [predictive_equation,hb,hv]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ExposureScout
