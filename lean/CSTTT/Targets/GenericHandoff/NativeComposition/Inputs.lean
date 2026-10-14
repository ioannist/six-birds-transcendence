import CSTTT.Targets.GenericHandoff.NativeComposition.Factor
import CSTTT.Targets.GenericHandoff.AcquisitionExecution

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition
open RegisterInterpreter
abbrev FactorData := TemporalFactorRules.Raw Factor Bool Factor History Route Stage Bool Owner
structure Input where
  temporal : FactorData
  receiver : AcquisitionExecution.Receiver
  reveal : Bool
  withdrawal : ResourceRuntime.Withdrawal Bool
abbrev Value (_ : Owner) := Input

def swapOwner (o : Owner) : Owner := match o with | false => true | true => false
theorem swap_owner_involution (o : Owner) : swapOwner (swapOwner o) = o := by cases o <;> rfl

def withdrawal : ResourceRuntime.Withdrawal Bool :=
  ⟨ResourceRuntime.roles,fun _ => [false],[false],[true]⟩
def canonicalInput (owner : Owner) : Input :=
  ⟨factorData owner,⟨true,true,true,true⟩,false,withdrawal⟩
def canonical : Assignment Owner Value := fun o => some (canonicalInput o)

/-- A primitive publication changes the local owner and appends the actual
assigned history to itself. No derived state or verdict is stored. -/
def publish (i : Input) : Input :=
  {i with temporal := {i.temporal with
    resource := {i.temporal.resource with owner := swapOwner i.temporal.resource.owner}
    histories := fun h => i.temporal.histories h ++ i.temporal.histories h}}
def restore (i : Input) : Input :=
  {i with temporal := {i.temporal with
    resource := {i.temporal.resource with owner := swapOwner i.temporal.resource.owner}
    histories := fun h => (i.temporal.histories h).take ((i.temporal.histories h).length/2)}}

def image (a : Assignment Owner Value) : Assignment Owner Value :=
  fun o => (a (swapOwner o)).map publish

theorem half_double {X : Type} (xs : List X) :
    (xs++xs).take ((xs++xs).length/2) = xs := by
  have hn : (xs.length+xs.length)/2 = xs.length := by omega
  rw [List.length_append,hn]
  simp

theorem restore_publish (i : Input) : restore (publish i) = i := by
  simp only [publish,restore,swap_owner_involution,half_double]

theorem image_cell (a : Assignment Owner Value) (o : Owner) :
    image a o = (a (swapOwner o)).map publish := rfl

theorem actual_source (a : Assignment Owner Value) (o : Owner) :
    (image a (swapOwner o)).map restore = a o := by
  simp only [image,Option.map_map]
  have hf : restore ∘ publish = id := by funext i; exact restore_publish i
  rw [hf]
  simp only [Option.map_id]
  cases o <;> rfl

def factorBindings (cell : Owner) (inverse : Bool) :
    TemporalFactorCells.Bindings Owner Value Factor Bool Factor History Route Stage Bool Owner :=
  let get : Input → FactorData := fun i => (if inverse then restore i else i).temporal
  ⟨⟨cell,fun i => (get i).rows⟩,⟨cell,fun i => (get i).positions⟩,
    ⟨cell,fun i => (get i).hazards⟩,⟨cell,fun i => (get i).policy⟩,
    ⟨cell,fun i => (get i).classes⟩,⟨cell,fun i => (get i).publishedP⟩,
    ⟨cell,fun i => (get i).ticks⟩,⟨cell,fun i => (get i).resource⟩,
    ⟨cell,fun i => (get i).ledger⟩,⟨cell,fun i => (get i).interface⟩,
    ⟨cell,fun i => (get i).histories⟩,⟨cell,fun i => (get i).events⟩,
    ⟨cell,fun i => (get i).realized⟩,⟨cell,fun i => (get i).receiverFunded⟩,
    ⟨cell,fun i => (get i).routes⟩,⟨cell,fun i => (get i).writers⟩⟩

theorem decoded_factor (cell : Owner) (inverse : Bool) (a : Assignment Owner Value) :
    TemporalFactorCells.decoded (factorBindings cell inverse) a =
      (a cell).map (fun i => (if inverse then restore i else i).temporal) := by
  cases ha : a cell <;> simp [factorBindings,TemporalFactorCells.decoded,CellView.read,ha]

theorem decoded_actual_source (a : Assignment Owner Value) (o : Owner) :
    TemporalFactorCells.decoded (factorBindings (swapOwner o) true) (image a) =
      TemporalFactorCells.decoded (factorBindings o false) a := by
  rw [decoded_factor,decoded_factor]
  have h := congrArg (fun z : Option Input => z.map Input.temporal) (actual_source a o)
  simpa [Option.map_map] using h

theorem missing_factor (cell : Owner) (inverse : Bool) (a : Assignment Owner Value)
    (hm : a cell = none) : TemporalFactorCells.decoded (factorBindings cell inverse) a = none := by
  rw [decoded_factor,hm]
  rfl

end CSTTT.TargetTheory.GenericHandoff.NativeComposition
