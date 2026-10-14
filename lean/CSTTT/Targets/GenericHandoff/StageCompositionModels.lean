import CSTTT.Targets.GenericHandoff.StageComposition

/-! Primitive-map witness declared in TTH07-STAGE-COMPOSITION.model.json.
This is not a two-hop Temporal-FIACH witness. The raw numerical instruction
parameters define actual interpreted outputs; missing sources remain absent. -/
namespace CSTTT.TargetTheory.GenericHandoff.StageCompositionModels

def increment : Nat := 1
def multiplier : Nat := 2
def positiveValue : Nat := 3
def add : TranslationLanguage Unit Unit (fun _ => Nat) (fun _ => Nat) where
  Instruction _ _ := Nat
  execute n value := some (value + n)
def multiply : TranslationLanguage Unit Unit (fun _ => Nat) (fun _ => Nat) where
  Instruction _ _ := Nat
  execute n value := some (value * n)
def first : Stage (Index := Unit) add := fun _ _ => some ⟨(),increment⟩
def second : Stage (Index := Unit) multiply := fun _ _ => some ⟨(),multiplier⟩
def scopes : Unit → List Unit := fun _ => [()]
def cover : RawCover Unit Unit := ⟨[()],scopes,fun _ _ => true⟩
def composed := StageComposition.stage add multiply first second scopes
def output (a : Assignment Unit (fun _ => Nat)) :=
  mappedLocal (StageComposition.language add multiply) a composed scopes () ()
def globalOutput (a : Assignment Unit (fun _ => Nat)) :=
  PackageEngine.global (StageComposition.language add multiply) a composed cover ()
def missingScope := StageComposition.stage add multiply first second (fun _ => [])
def absentScopeOutput (a : Assignment Unit (fun _ => Nat)) :=
  mappedLocal (StageComposition.language add multiply) a missingScope scopes () ()
def changedFirst : Stage (Index := Unit) add := fun _ _ => some ⟨(),(2 : Nat)⟩
def changedOutput (a : Assignment Unit (fun _ => Nat)) :=
  mappedLocal (StageComposition.language add multiply) a
    (StageComposition.stage add multiply changedFirst second scopes) scopes () ()
def absentRight : Stage (Index := Unit) multiply := fun _ _ => none
def absentRightOutput (a : Assignment Unit (fun _ => Nat)) :=
  mappedLocal (StageComposition.language add multiply) a
    (StageComposition.stage add multiply first absentRight scopes) scopes () ()

theorem output_equation (a : Assignment Unit (fun _ => Nat)) :
    output a = (a ()).map (fun n => (n + increment) * multiplier) := by
  cases ha : a () <;> simp [output,composed,mappedLocal,StageComposition.stage,StageComposition.language,first,second,scopes,add,multiply,ha]

theorem global_equation (a : Assignment Unit (fun _ => Nat)) : globalOutput a = output a := rfl

theorem cover_check : CoverCheck cover := by
  refine ⟨fun k => ⟨(),by decide,by cases k; decide⟩,?_⟩
  intro i j k hi hj
  cases i; cases j
  exact CSTTT.PackageTheory.ScopedReach.refl () hi

theorem source_missing (a : Assignment Unit (fun _ => Nat)) (ha : a () = none) : output a = none := by
  rw [output_equation,ha]; rfl

theorem scope_missing (a : Assignment Unit (fun _ => Nat)) : absentScopeOutput a = none := rfl

theorem right_arrow_missing (a : Assignment Unit (fun _ => Nat)) : absentRightOutput a = none := rfl

theorem changed_equation (a : Assignment Unit (fun _ => Nat)) :
    changedOutput a = (a ()).map (fun n => (n + 2) * multiplier) := by
  cases ha : a () <;> simp [changedOutput,mappedLocal,StageComposition.stage,StageComposition.language,second,changedFirst,scopes,add,multiply,ha]

theorem changed_reference : ReferenceCheck add changedFirst first scopes := by
  intro _ _ _; rfl

theorem positive : output (fun _ => some positiveValue) = some 8 := rfl

theorem instruction_change_changes_readout :
    changedOutput (fun _ => some positiveValue) = some 10 ∧
      changedOutput (fun _ => some positiveValue) ≠ output (fun _ => some positiveValue) := by decide

theorem positive_total : StageTotal (StageComposition.language add multiply)
    (fun _ => some positiveValue) composed scopes := by
  apply StageComposition.total add multiply first second scopes _ scopes (fun _ => some (positiveValue + increment))
  · intro i t ht; exact ⟨⟨(),increment⟩,rfl,rfl,fun _ => by simp [add]⟩
  · intro i t ht; exact ⟨⟨(),multiplier⟩,rfl,rfl,fun _ => by simp [multiply]⟩
  · intro i t ht r hr
    have he : r = ⟨(),multiplier⟩ := Option.some.inj hr.symm
    subst r
    change () ∈ [()]
    exact List.mem_cons_self

end CSTTT.TargetTheory.GenericHandoff.StageCompositionModels
