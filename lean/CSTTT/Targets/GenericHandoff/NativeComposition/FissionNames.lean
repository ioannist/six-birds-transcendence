import CSTTT.Targets.GenericHandoff.OwnerRelabel
import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationReturn

/-! Primitive branch name instructions and computed coordinate images.
The transpositions fix the shared source17 and send the reference target55
to201/202. Full future codes, owner expressions, event/support coordinates
and credit owner/housing readouts use these same declared instructions. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
open CSTTT.TransportTheory
open CSTTT.CorridorTheory.AtomicChain
def transpose (a b n : Nat) : Nat := if n=a then b else if n=b then a else n
theorem transpose_involution (a b n : Nat) : transpose a b (transpose a b n)=n := by
  by_cases ha : n=a
  · subst n
    by_cases he : a=b
    · simp [transpose,he]
    · simp [transpose,Ne.symm he]
  · by_cases hb : n=b
    · subst n; simp [transpose,ha]
    · simp [transpose,ha,hb]
theorem transpose_injective (a b : Nat) : Function.Injective (transpose a b) := by
  intro n m h
  simpa only [transpose_involution] using congrArg (transpose a b) h
def branchTarget (branch : Bool) : Nat := if branch then 202 else 201
def rename (branch : Bool) : Nat → Nat := transpose 55 (branchTarget branch)
def renameOwner (branch : Bool) (owner : CarrierId) : CarrierId := ⟨rename branch owner.code⟩
def renameObservation (branch : Bool) (x : PublicationFuture.Observation) : PublicationFuture.Observation :=
  {x with owner := renameOwner branch x.owner}
def renameFrontier (branch : Bool) (x : Frontier) : Frontier := {x with owner := rename branch x.owner}
def renameStage (branch : Bool) (x : RawStage) : RawStage :=
  {x with support := x.support.map (rename branch), frontier := renameFrontier branch x.frontier}
def renameLeg (branch : Bool) (x : FiniteAtomicLeg) : FiniteAtomicLeg :=
  {x with
    source := rename branch x.source
    target := rename branch x.target
    stages := x.stages.map (renameStage branch)
    events := x.events.map (fun e => {e with owner := rename branch e.owner})
    updates := x.updates.map (fun u => {u with nextOwner := rename branch u.nextOwner})}

theorem rename_owner_involution (branch : Bool) (x : CarrierId) :
    renameOwner branch (renameOwner branch x)=x := by
  cases x
  simp [renameOwner,rename,transpose_involution]
theorem rename_observation_involution (branch : Bool) (x : PublicationFuture.Observation) :
    renameObservation branch (renameObservation branch x)=x := by
  cases x
  simp [renameObservation,rename_owner_involution]
theorem rename_observation_injective (branch : Bool) : Function.Injective (renameObservation branch) := by
  intro x y h
  simpa only [rename_observation_involution] using congrArg (renameObservation branch) h


open RegisterInterpreter PublicationReplay

def branchNames (branch : Bool) (owner : Owner) : CarrierId := renameOwner branch (names true owner)
theorem branch_names_injective (branch : Bool) : Function.Injective (branchNames branch) := by
  intro x y h
  apply PublicationFuture.names_injective true
  have he := congrArg (renameOwner branch) h
  simpa only [branchNames,rename_owner_involution] using he

theorem source_fixed (branch : Bool) : rename branch 17=17 := by cases branch <;> rfl
theorem target_renamed (branch : Bool) : rename branch 55=branchTarget branch := by cases branch <;> rfl
theorem branch_targets_distinct : branchTarget false≠branchTarget true := by decide +kernel

def swapOwner (x : CarrierId) : CarrierId := ⟨transpose 201 202 x.code⟩
def swapObservation (x : PublicationFuture.Observation) : PublicationFuture.Observation := {x with owner := swapOwner x.owner}
theorem swap_owner_involution (x : CarrierId) : swapOwner (swapOwner x)=x := by
  cases x
  simp [swapOwner,transpose_involution]
theorem swap_observation_involution (x : PublicationFuture.Observation) : swapObservation (swapObservation x)=x := by
  cases x
  simp [swapObservation,swap_owner_involution]
theorem swap_observation_injective : Function.Injective swapObservation := by
  intro x y h
  simpa only [swap_observation_involution] using congrArg swapObservation h

theorem swapped_names (branch : Bool) (owner : Owner) : branchNames (!branch) owner=swapOwner (branchNames branch owner) := by
  cases branch <;> cases owner <;> rfl

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
