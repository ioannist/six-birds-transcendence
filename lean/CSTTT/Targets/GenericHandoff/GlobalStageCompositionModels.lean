import CSTTT.Targets.GenericHandoff.GlobalStageComposition
import CSTTT.Targets.GenericHandoff.StageCompositionModels

/-! Cover-selector witness predeclared in the global-package composition
model. The left/right index types differ. Changing only one raw scope selects
an absent earlier arrow; an available later arrow cannot serve as fallback. -/
namespace CSTTT.TargetTheory.GenericHandoff.GlobalStageCompositionModels
open StageCompositionModels

def first : Stage (Index := Bool) add := fun i _ =>
  if i then some ⟨(),increment⟩ else none
def cover : RawCover Bool Unit :=
  ⟨[false,true],(fun i => if i then [()] else []),fun _ _ => true⟩
def shadowCover : RawCover Bool Unit :=
  {cover with scopes := fun _ => [()]}
def output (a : Assignment Unit (fun _ => Nat)) :=
  PackageEngine.global (StageComposition.language add multiply) a
    (GlobalStageComposition.stage add multiply first second cover) StageCompositionModels.cover ()
def shadowOutput (a : Assignment Unit (fun _ => Nat)) :=
  PackageEngine.global (StageComposition.language add multiply) a
    (GlobalStageComposition.stage add multiply first second shadowCover) StageCompositionModels.cover ()

theorem selector : firstCover cover.scopes () cover.indices = some true := by decide
theorem shadow_selector : firstCover shadowCover.scopes () shadowCover.indices = some false := by decide
theorem available_later_arrow : (first true ()).isSome = true := rfl
theorem absent_selected_arrow : first false () = none := rfl

theorem shadow_other_fields : shadowCover.indices = cover.indices ∧
    shadowCover.adjacent = cover.adjacent ∧ shadowCover.scopes true = cover.scopes true := ⟨rfl,rfl,rfl⟩

theorem available_later_value :
    mappedLocal add (fun _ => some positiveValue) first shadowCover.scopes true () =
      some (positiveValue + increment) := rfl

theorem output_equation (a : Assignment Unit (fun _ => Nat)) :
    output a = (a ()).map (fun n => (n + increment) * multiplier) := by
  cases ha : a () <;> simp [output,PackageEngine.global,glued,mappedLocal,
    GlobalStageComposition.stage,GlobalStageComposition.selectedArrow,selector,first,
    StageCompositionModels.cover,scopes,firstCover,second,StageComposition.language,add,multiply,ha]

theorem shadow_output (a : Assignment Unit (fun _ => Nat)) : shadowOutput a = none := rfl

theorem missing_source (a : Assignment Unit (fun _ => Nat)) (ha : a () = none) : output a = none := by
  rw [output_equation,ha]; rfl

theorem positive : output (fun _ => some positiveValue) = some 8 := rfl

theorem shadow_direct_control : output (fun _ => some positiveValue) = some 8 ∧
    shadowOutput (fun _ => some positiveValue) = none ∧
    (first true ()).isSome = true := ⟨rfl,rfl,rfl⟩

end CSTTT.TargetTheory.GenericHandoff.GlobalStageCompositionModels
