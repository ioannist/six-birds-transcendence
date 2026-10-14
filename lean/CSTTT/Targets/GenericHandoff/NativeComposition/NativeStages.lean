import CSTTT.Targets.GenericHandoff.NativeComposition.NativeBoundary

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter

/-- The simultaneous execution namespace exposes the consumed first target
cell and consumed final target cell from ACTUAL successive raw publication. -/
def stagedAssignment (initial : Assignment Owner MemoryValue) : Assignment Owner MemoryValue :=
  fun cell => if cell then memoryImage initial true else memoryImage (memoryImage initial) false

theorem first_stage_exposure (initial : Assignment Owner MemoryValue) :
    stagedAssignment initial true=memoryImage initial true := rfl

theorem final_stage_exposure (initial : Assignment Owner MemoryValue) :
    stagedAssignment initial false=memoryImage (memoryImage initial) false := rfl

theorem original_source_exposure (initial : Assignment Owner MemoryValue) :
    sourceInputs (stagedAssignment initial) true=currentInputs initial false := by
  exact published_source initial false

theorem actual_middle_source_exposure (initial : Assignment Owner MemoryValue) :
    sourceInputs (stagedAssignment initial) false=currentInputs (memoryImage initial) true := by
  exact published_source (memoryImage initial) true

theorem canonical_stage_exposure : stagedAssignment memoryCanonical=nativeAssignment := by
  funext cell
  cases cell <;> rfl

theorem consumed_first_stage_absence (initial : Assignment Owner MemoryValue) (hm : initial false=none) :
    stagedAssignment initial true=none := by
  simp [stagedAssignment,memoryImage,swapOwner,hm]

theorem consumed_final_stage_absence (initial : Assignment Owner MemoryValue) (hm : initial false=none) :
    stagedAssignment initial false=none := by
  simp [stagedAssignment,memoryImage,swapOwner,hm]

theorem actual_mixed_reception_clocks (h : Factor) :
    firstSchema.clock 1=(snapshot h 4 1 true ()).1.counter ∧
    secondSchema.clock 1=(snapshot h 8 5 false ()).1.counter := ⟨rfl,rfl⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
