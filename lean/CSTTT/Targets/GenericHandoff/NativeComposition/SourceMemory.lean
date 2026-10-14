import CSTTT.Targets.GenericHandoff.NativeComposition.Inputs

/-! The published target includes a copy of the actual primitive source table.
This stores raw instructions, not a run, future, classifier or verdict. Target
resource interventions can therefore preserve the original source literally. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition
open RegisterInterpreter
abbrev MemoryValue (_ : Owner) := Input × Input

def memoryCanonical : Assignment Owner MemoryValue := fun o =>
  some (canonicalInput o,canonicalInput o)
def memoryPublish (p : Input × Input) : Input × Input := (publish p.1,p.1)
def memoryImage (a : Assignment Owner MemoryValue) : Assignment Owner MemoryValue :=
  fun o => (a (swapOwner o)).map memoryPublish

def currentInputs (a : Assignment Owner MemoryValue) : Assignment Owner Value :=
  fun o => (a o).map Prod.fst
def sourceInputs (a : Assignment Owner MemoryValue) : Assignment Owner Value :=
  fun o => (a o).map Prod.snd

theorem published_target (a : Assignment Owner MemoryValue) (o : Owner) :
    currentInputs (memoryImage a) o = ((a (swapOwner o)).map Prod.fst).map publish := by
  simp only [currentInputs,memoryImage,Option.map_map]
  rfl

theorem published_source (a : Assignment Owner MemoryValue) (o : Owner) :
    sourceInputs (memoryImage a) (swapOwner o) = currentInputs a o := by
  cases o <;> simp only [sourceInputs,currentInputs,memoryImage,swapOwner,Option.map_map] <;> rfl

theorem source_table_exact (a : Assignment Owner MemoryValue) (o : Owner) :
    TemporalFactorCells.decoded (factorBindings (swapOwner o) false) (sourceInputs (memoryImage a)) =
      TemporalFactorCells.decoded (factorBindings o false) (currentInputs a) := by
  rw [decoded_factor,decoded_factor,published_source]

/-- A concrete target-only primitive intervention. Source rows, histories,
resource inputs and ownership survive unchanged at every partial assignment. -/
def intervene (f : Input → Input) (a : Assignment Owner MemoryValue) : Assignment Owner MemoryValue :=
  fun o => (a o).map (fun p => (f p.1,p.2))

theorem intervention_source (f : Input → Input) (a : Assignment Owner MemoryValue) :
    sourceInputs (intervene f a) = sourceInputs a := by
  funext o
  simp only [sourceInputs,intervene,Option.map_map]
  rfl

theorem intervention_source_table (f : Input → Input) (a : Assignment Owner MemoryValue) (o : Owner) :
    TemporalFactorCells.decoded (factorBindings o false) (sourceInputs (intervene f a)) =
      TemporalFactorCells.decoded (factorBindings o false) (sourceInputs a) := by
  rw [intervention_source]

theorem consumed_absence (a : Assignment Owner MemoryValue) (o : Owner) (hm : a o = none) :
    currentInputs a o = none ∧ sourceInputs a o = none := by
  simp [currentInputs,sourceInputs,hm]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition
