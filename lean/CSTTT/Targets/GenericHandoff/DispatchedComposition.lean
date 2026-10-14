import CSTTT.Targets.GenericHandoff.GlobalStageComposition
import CSTTT.Targets.GenericHandoff.DispatchedPackage

/-! Closed-dispatcher package composition. One actual cover-selected middle
global supplies the right stage. Composite original-source dependencies come
from the independently declared composed reference stage, rather than actual
successful arrows. Parent primitive laws derive every composite package check.
This does not yet construct composed receivers/corridors/autonomy. -/
namespace CSTTT.TargetTheory.GenericHandoff.DispatchedComposition
variable {SC MC TC : Type} {SV : SC → Type} {MV : MC → Type} {TV : TC → Type}
variable [DecidableEq MC] [DecidableEq TC]

def compose (left : DispatchedPackage.Raw SC MC SV MV)
    (right : DispatchedPackage.Raw MC TC MV TV) : DispatchedPackage.Raw SC TC SV TV where
  language := StageComposition.language left.language right.language
  stage := GlobalStageComposition.stage left.language right.language left.stage right.stage left.cover
  referenceStage := GlobalStageComposition.stage left.language right.language left.referenceStage right.referenceStage left.cover
  sourceScopes := GlobalStageComposition.footprint
    (GlobalStageComposition.stage left.language right.language left.referenceStage right.referenceStage left.cover) right.cover.scopes
  cover := right.cover
  clauses := right.clauses

variable (left : DispatchedPackage.Raw SC MC SV MV) (right : DispatchedPackage.Raw MC TC MV TV)

theorem local_equation (a : Assignment SC SV) (c : ClauseDispatcher.Kind) :
    mappedLocal (compose left right).language a (compose left right).stage (compose left right).cover.scopes c =
      mappedLocal right.language (DispatchedPackage.global left a) right.stage right.cover.scopes c :=
  GlobalStageComposition.local_equation left.language right.language left.stage right.stage left.cover a right.cover.scopes c

theorem target_equation (a : Assignment SC SV) :
    DispatchedPackage.global (compose left right) a =
      DispatchedPackage.global right (DispatchedPackage.global left a) :=
  GlobalStageComposition.global_equation left.language right.language left.stage right.stage left.cover a right.cover

omit [DecidableEq TC] in
theorem final_dispatcher : (compose left right).clauses = right.clauses := rfl

/-- Every composite primitive/package check is derived from the two checked
parents. The middle assignment is their constructed gluing, not a premise. -/
theorem valid (a : Assignment SC SV) (hl : DispatchedPackage.Valid left a)
    (hr : DispatchedPackage.Valid right (DispatchedPackage.global left a)) :
    DispatchedPackage.Valid (compose left right) a := by
  obtain ⟨lc,_,lt,lr,lv,_,_,le⟩ := hl
  obtain ⟨rc,rd,rt,rr,rv,_,ra,re⟩ := hr
  have href := GlobalStageComposition.reference left.language right.language left.stage right.stage left.cover
    left.referenceStage right.referenceStage right.cover.scopes lr rr
  refine ⟨rc,rd,
    GlobalStageComposition.total left.language right.language left.stage right.stage left.cover a right.cover.scopes lc lt rt,
    href,
    GlobalStageComposition.value_preserving left.language right.language left.stage right.stage left.cover a
      left.referenceStage right.referenceStage right.cover.scopes lv rv,
    GlobalStageComposition.reference_coverage _ _ _ href,?_,?_⟩
  · intro c
    change (right.clauses.rule c).accept (mappedLocal (compose left right).language a
      (compose left right).stage (compose left right).cover.scopes c)
    rw [local_equation]
    exact ra c
  · intro i j k ha hi hj
    change mappedLocal (compose left right).language a (compose left right).stage (compose left right).cover.scopes i k =
      mappedLocal (compose left right).language a (compose left right).stage (compose left right).cover.scopes j k
    rw [local_equation,local_equation]
    exact re i j k ha hi hj

/-- Arbitrary-partial target acceptance is exactly the right parent's actual
final acceptance. It is independent of complete-map certification. -/
theorem target_acceptance_iff (a : Assignment SC SV) :
    (compose left right).clauses.accept (DispatchedPackage.global (compose left right) a) ↔
      right.clauses.accept (DispatchedPackage.global right (DispatchedPackage.global left a)) := by
  rw [target_equation]
  rfl

theorem constructs (a : Assignment SC SV) (hl : DispatchedPackage.Valid left a)
    (hr : DispatchedPackage.Valid right (DispatchedPackage.global left a)) :
    (∀ c k, k ∈ right.cover.scopes c →
      DispatchedPackage.global (compose left right) a k =
        mappedLocal right.language (DispatchedPackage.global left a) right.stage right.cover.scopes c k) ∧
    (∀ k, (DispatchedPackage.global (compose left right) a k).isSome = true) ∧
    right.clauses.accept (DispatchedPackage.global (compose left right) a) := by
  have h := DispatchedPackage.constructs (compose left right) a (valid left right a hl hr)
  refine ⟨?_,h.2.1,h.2.2⟩
  intro c k hk
  exact (h.1 c k hk).trans (congrFun (local_equation left right a c) k)

end CSTTT.TargetTheory.GenericHandoff.DispatchedComposition
