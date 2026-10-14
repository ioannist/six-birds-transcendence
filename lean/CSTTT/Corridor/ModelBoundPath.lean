import CSTTT.Corridor.RawDirectSuccessor
import CSTTT.Corridor.GeneralizedProgress
namespace CSTTT.CorridorTheory.ModelBoundPath
open CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor

/-- A leg uses this exact model's episode or successful raw projection and
this exact partial input assignment. The predicate does not encode acceptance. -/
def ModelLeg (m : ControlModel) (leg : GeneralizedLeg) : Prop :=
  leg= .overlap m.episode ∨
    ∃ raw b, directProjection m=some (raw,b) ∧ leg= .direct raw b m.input

theorem checked_model_leg_iff (m : ControlModel) :
    (∃ leg, ModelLeg m leg ∧ legCheck leg=true) ↔ OverlapMode m ∨ DirectMode m := by
  constructor
  · rintro ⟨leg,binding,checked⟩
    rcases binding with overlap | ⟨raw,b,projection,direct⟩
    · subst leg
      exact Or.inl checked
    · subst leg
      exact Or.inr ⟨raw,b,projection,checked⟩
  · rintro (overlap | ⟨raw,b,projection,direct⟩)
    · exact ⟨.overlap m.episode,Or.inl rfl,overlap⟩
    · exact ⟨.direct raw b m.input,Or.inr ⟨raw,b,projection,rfl⟩,direct⟩

/-- Both the exact model sequence and the whole boundary signatures are
indices. No unrelated leg can replace a model while preserving this evidence. -/
inductive ModelPath : List ControlModel → Signature → Signature → Type where
  | one (model : ControlModel) (leg : GeneralizedLeg)
      (binding : ModelLeg model leg) (checked : legCheck leg=true) :
      ModelPath [model] (legEntry leg) (legExit leg)
  | append {left right : List ControlModel} {a b c : Signature}
      (first : ModelPath left a b) (second : ModelPath right b c) :
      ModelPath (left++right) a c

def forgetModels {models : List ControlModel} {a b : Signature} :
    ModelPath models a b → GeneralizedPath a b
  | .one _ leg _ checked => .one leg checked
  | .append first second => .append (forgetModels first) (forgetModels second)

theorem model_path_nonempty {models : List ControlModel} {a b : Signature}
    (path : ModelPath models a b) : models≠[] := by
  induction path with
  | one model leg binding checked => simp
  | append first second hf hs => simp [hf]

theorem every_model_actual {models : List ControlModel} {a b : Signature}
    (path : ModelPath models a b) : ∀ model∈models, OverlapMode model ∨ DirectMode model := by
  induction path with
  | one model leg binding checked =>
    intro m member
    simp only [List.mem_singleton] at member
    subst m
    exact (checked_model_leg_iff model).mp ⟨leg,binding,checked⟩
  | append first second hf hs =>
    intro m member
    simp only [List.mem_append] at member
    rcases member with left | right
    · exact hf m left
    · exact hs m right

theorem overlap_model_embedding (m : ControlModel) (overlap : OverlapMode m) :
    Nonempty (ModelPath [m] (m.episode.source,(entry m.episode).frontier)
      (m.episode.target,(exit m.episode).frontier)) :=
  ⟨.one m (.overlap m.episode) (Or.inl rfl) overlap⟩

theorem direct_model_embedding (m : ControlModel) (direct : DirectMode m) :
    ∃ raw b, directProjection m=some (raw,b) ∧
      Nonempty (ModelPath [m] (b.sourceCarrier,b.source.frontier)
        (b.targetCarrier,b.target.frontier)) := by
  obtain ⟨raw,b,projection,checked⟩ := direct
  exact ⟨raw,b,projection,⟨.one m (.direct raw b m.input)
    (Or.inr ⟨raw,b,projection,rfl⟩) checked⟩⟩

theorem model_path_strict {models : List ControlModel} {a b : Signature}
    (path : ModelPath models a b) : CSTTT.CorridorTheory.GeneralizedProgress.Strict a.2 b.2 :=
  CSTTT.CorridorTheory.GeneralizedProgress.path_strict (forgetModels path)

theorem no_closed_model_path (models : List ControlModel) (a : Signature) :
    ¬ Nonempty (ModelPath models a a) := by
  rintro ⟨path⟩
  exact CSTTT.CorridorTheory.GeneralizedProgress.no_closed_path a ⟨forgetModels path⟩

theorem model_path_length {models : List ControlModel} {a b : Signature}
    (path : ModelPath models a b) : (pathLegs (forgetModels path)).length=models.length := by
  induction path with
  | one model leg binding checked => rfl
  | append first second hf hs => simp [forgetModels,pathLegs,hf,hs]

end CSTTT.CorridorTheory.ModelBoundPath
