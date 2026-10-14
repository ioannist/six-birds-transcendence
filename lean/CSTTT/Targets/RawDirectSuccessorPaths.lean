import CSTTT.Targets.RawDirectSuccessorReturn
import CSTTT.Corridor.GeneralizedProgress

/-! Actual model-bound generalized paths. Every primitive leg retains its
model, episode/projection and partial assignment; append requires the whole
shared carrier/frontier signature. All declarations are new(b). -/
namespace CSTTT.TargetTheory.RawDirectSuccessorPaths
open CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor
open CSTTT.CorridorTheory.RawDirectControl CSTTT.CorridorTheory.ModelBoundPath
open CSTTT.TargetTheory.RawDirectSuccessorControls
open CSTTT.TargetTheory.RawDirectSuccessorReturn

def dsPos02AProjection : Raw × Boundary := (directProjection dsPos02A).get (by decide)

theorem dsPos02AProjection_spec : directProjection dsPos02A=some dsPos02AProjection :=
  (Option.some_get (by decide)).symm

def dsPos02ALeg : GeneralizedLeg :=
  .direct dsPos02AProjection.1 dsPos02AProjection.2 dsPos02A.input

theorem dsPos02ALeg_checked : legCheck dsPos02ALeg=true :=
  projected_direct dsPos02A _ _ dsPos02AProjection_spec dsPos02A_direct

theorem dsPos02ALeg_binding : ModelLeg dsPos02A dsPos02ALeg :=
  Or.inr ⟨_,_,dsPos02AProjection_spec,rfl⟩

def dsPos02APath : ModelPath [dsPos02A] (legEntry dsPos02ALeg) (legExit dsPos02ALeg) :=
  .one dsPos02A dsPos02ALeg dsPos02ALeg_binding dsPos02ALeg_checked

def dsPos02BProjection : Raw × Boundary := (directProjection dsPos02B).get (by decide)

theorem dsPos02BProjection_spec : directProjection dsPos02B=some dsPos02BProjection :=
  (Option.some_get (by decide)).symm

def dsPos02BLeg : GeneralizedLeg :=
  .direct dsPos02BProjection.1 dsPos02BProjection.2 dsPos02B.input

theorem dsPos02BLeg_checked : legCheck dsPos02BLeg=true :=
  projected_direct dsPos02B _ _ dsPos02BProjection_spec dsPos02B_direct

theorem dsPos02BLeg_binding : ModelLeg dsPos02B dsPos02BLeg :=
  Or.inr ⟨_,_,dsPos02BProjection_spec,rfl⟩

def dsPos02BPath : ModelPath [dsPos02B] (legEntry dsPos02BLeg) (legExit dsPos02BLeg) :=
  .one dsPos02B dsPos02BLeg dsPos02BLeg_binding dsPos02BLeg_checked

def mixedDirectProjection : Raw × Boundary := (directProjection mixedDirect).get (by decide)

theorem mixedDirectProjection_spec : directProjection mixedDirect=some mixedDirectProjection :=
  (Option.some_get (by decide)).symm

def mixedDirectLeg : GeneralizedLeg :=
  .direct mixedDirectProjection.1 mixedDirectProjection.2 mixedDirect.input

theorem mixedDirectLeg_checked : legCheck mixedDirectLeg=true :=
  projected_direct mixedDirect _ _ mixedDirectProjection_spec mixedDirect_direct

theorem mixedDirectLeg_binding : ModelLeg mixedDirect mixedDirectLeg :=
  Or.inr ⟨_,_,mixedDirectProjection_spec,rfl⟩

def mixedDirectPath : ModelPath [mixedDirect] (legEntry mixedDirectLeg) (legExit mixedDirectLeg) :=
  .one mixedDirect mixedDirectLeg mixedDirectLeg_binding mixedDirectLeg_checked

def overlapLeg : GeneralizedLeg := .overlap overlapOnly.episode

def overlapPath : ModelPath [overlapOnly] (legEntry overlapLeg) (legExit overlapLeg) :=
  .one overlapOnly overlapLeg (Or.inl rfl) overlapOnly_overlap

theorem two_direct_whole_boundary : legExit dsPos02ALeg=legEntry dsPos02BLeg := by decide

theorem mixed_whole_boundary : legExit overlapLeg=legEntry mixedDirectLeg := by decide

def twoDirectPath : ModelPath [dsPos02A,dsPos02B]
    (legEntry dsPos02ALeg) (legExit dsPos02BLeg) := by
  have second := dsPos02BPath
  rw [← two_direct_whole_boundary] at second
  exact .append dsPos02APath second

def mixedPath : ModelPath [overlapOnly,mixedDirect]
    (legEntry overlapLeg) (legExit mixedDirectLeg) := by
  have second := mixedDirectPath
  rw [← mixed_whole_boundary] at second
  exact .append overlapPath second

theorem two_direct_exact_models :
    (pathLegs (forgetModels twoDirectPath)).length=2 := model_path_length twoDirectPath

theorem mixed_exact_models :
    (pathLegs (forgetModels mixedPath)).length=2 := model_path_length mixedPath

/-- Query actual dependency unions; a path constructor is never an atomic
selected-left-source to selected-right-target generation edge. -/
def endpointEdgePresent (left right : ControlModel) : Bool :=
  (left.episode.dependencies++right.episode.dependencies).any fun edge =>
    edge.parent==left.episode.sourceAudit && edge.child==right.episode.targetAudit

theorem two_direct_no_atomic_endpoint_edge : endpointEdgePresent dsPos02A dsPos02B=false := by decide

theorem mixed_no_atomic_endpoint_edge : endpointEdgePresent overlapOnly mixedDirect=false := by decide

theorem two_direct_strict_endpoint :
    CSTTT.CorridorTheory.GeneralizedProgress.Strict
      (legEntry dsPos02ALeg).2 (legExit dsPos02BLeg).2 := model_path_strict twoDirectPath

theorem mixed_strict_endpoint :
    CSTTT.CorridorTheory.GeneralizedProgress.Strict
      (legEntry overlapLeg).2 (legExit mixedDirectLeg).2 := model_path_strict mixedPath

theorem actual_mixed_path_with_no_endpoint_edge :
    Nonempty (ModelPath [overlapOnly,mixedDirect]
      (legEntry overlapLeg) (legExit mixedDirectLeg)) ∧
    endpointEdgePresent overlapOnly mixedDirect=false :=
  ⟨⟨mixedPath⟩,mixed_no_atomic_endpoint_edge⟩

end CSTTT.TargetTheory.RawDirectSuccessorPaths
