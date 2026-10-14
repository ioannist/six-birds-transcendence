import CSTTT.Targets.GenericHandoff.NativeComposition.ObjecthoodCells
import CSTTT.Targets.GenericHandoff.NativeComposition.NativeStages

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeObjecthoodCells
open RegisterInterpreter ModeExecution

def cellOwner : Cell → Owner | .inl o | .inr o => o
def staged (a : Assignment Cell Value) : Assignment Cell Value :=
  fun c => if cellOwner c then image a c else image (image a) c
def initialCanonical : Assignment Cell Value
  | .inl o => memoryCanonical o
  | .inr _ => some (supplement,supplement)

theorem native_stage_exposure (a : Assignment Cell Value) :
    nativeInputs (staged a)=stagedAssignment (nativeInputs a) := by
  funext o
  cases o <;> rfl

theorem canonical_native_exposure : nativeInputs (staged initialCanonical)=nativeAssignment := by
  rw [native_stage_exposure]
  exact canonical_stage_exposure

theorem canonical_supplement_exposure (o : Owner) :
    staged initialCanonical (.inr o)=some (supplement,supplement) := by
  cases o <;> rfl

theorem original_supplement_source (a : Assignment Cell Value) :
    (staged a (.inr true)).map (selectSupplement true)=
      (a (.inr false)).map (selectSupplement false) :=
  copied_supplement_source a false

theorem middle_supplement_source (a : Assignment Cell Value) :
    (staged a (.inr false)).map (selectSupplement true)=
      (image a (.inr true)).map (selectSupplement false) :=
  copied_supplement_source (image a) true

theorem missing_original_native (a : Assignment Cell Value) (hm : a (.inl false)=none) :
    staged a (.inl true)=none ∧ staged a (.inl false)=none := by
  simp [staged,cellOwner,image,nativeInputs,memoryImage,swapOwner,hm]

theorem missing_original_supplement (a : Assignment Cell Value) (hm : a (.inr false)=none) :
    staged a (.inr true)=none ∧ staged a (.inr false)=none := by
  simp [staged,cellOwner,image,swapOwner,hm]

theorem source_c1 : ObjecthoodProtocol.Accept clauseSchema.toSchema reference
    (bindings true true) (staged initialCanonical) := by
  apply actual_round_accept true true (staged initialCanonical) 0 (episodePair 0)
    (congrFun canonical_native_exposure true) rfl (supplement,supplement)
    (canonical_supplement_exposure true) rfl

theorem middle_target_c1 : ObjecthoodProtocol.Accept clauseSchema.toSchema reference
    (bindings true false) (staged initialCanonical) := by
  apply actual_round_accept true false (staged initialCanonical) 1 (episodePair 0)
    (congrFun canonical_native_exposure true) rfl (supplement,supplement)
    (canonical_supplement_exposure true) rfl

theorem middle_source_c1 : ObjecthoodProtocol.Accept clauseSchema.toSchema reference
    (bindings false true) (staged initialCanonical) := by
  apply actual_round_accept false true (staged initialCanonical) 1 (episodePair 1)
    (congrFun canonical_native_exposure false) rfl (supplement,supplement)
    (canonical_supplement_exposure false) rfl

theorem final_target_c1 : ObjecthoodProtocol.Accept clauseSchema.toSchema reference
    (bindings false false) (staged initialCanonical) := by
  apply actual_round_accept false false (staged initialCanonical) 2 (episodePair 1)
    (congrFun canonical_native_exposure false) rfl (supplement,supplement)
    (canonical_supplement_exposure false) rfl

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeObjecthoodCells
