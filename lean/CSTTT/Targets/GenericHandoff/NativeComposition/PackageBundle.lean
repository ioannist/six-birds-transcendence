import CSTTT.Targets.GenericHandoff.NativeComposition.PackagePrimitives

/-! A common primitive bundle lets each fixed CellView algorithm consume both
the native fields and supplementary instructions at one owner cell. Bundling
the two original arms is partial: either missing arm rejects. Publication
commutes exactly with this primitive bundling on every partial assignment. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackageBundle
open RegisterInterpreter NativePackagePrimitives

structure Bundle where
  native : Input
  supplement : Supplement
abbrev Value (_ : Owner) := Bundle × Bundle
def fromArms (a : Assignment NativePackagePrimitives.Cell NativePackagePrimitives.Value) : Assignment Owner Value :=
  fun o => do
    let n ← a (.inl o)
    let s ← a (.inr o)
    pure (⟨n.1,s.1⟩,⟨n.2,s.2⟩)
def select (copy : Bool) (p : Bundle × Bundle) : Bundle := if copy then p.2 else p.1
def nativeInputs (a : Assignment Owner Value) : Assignment Owner MemoryValue :=
  fun o => (a o).map (fun p => (p.1.native,p.2.native))
def objecthoodInputs (a : Assignment Owner Value) : Assignment NativeObjecthoodCells.Cell NativeObjecthoodCells.Value
  | .inl o => nativeInputs a o
  | .inr o => (a o).map (fun p => (p.1.supplement.objecthood,p.2.supplement.objecthood))
def publishBundle (b : Bundle) : Bundle := ⟨publish b.native,b.supplement⟩
def image (a : Assignment Owner Value) : Assignment Owner Value :=
  fun o => (a (swapOwner o)).map (fun p => (publishBundle p.1,p.1))
def staged (a : Assignment Owner Value) : Assignment Owner Value :=
  fun o => if o then image a o else image (image a) o
def initial : Assignment Owner Value := fromArms NativePackagePrimitives.initial
def canonical := staged initial

theorem image_from_arms (a : Assignment NativePackagePrimitives.Cell NativePackagePrimitives.Value) :
    fromArms (NativePackagePrimitives.image a)=image (fromArms a) := by
  funext o
  cases hn : a (.inl (swapOwner o)) <;> cases hs : a (.inr (swapOwner o)) <;>
    simp [fromArms,image,NativePackagePrimitives.image,NativePackagePrimitives.nativeInputs,
      memoryImage,memoryPublish,publishBundle,hn,hs]
theorem staged_from_arms (a : Assignment NativePackagePrimitives.Cell NativePackagePrimitives.Value) :
    fromArms (NativePackagePrimitives.staged a)=staged (fromArms a) := by
  funext o
  cases o
  · have h := image_from_arms (NativePackagePrimitives.image a)
    rw [image_from_arms a] at h
    exact congrFun h false
  · exact congrFun (image_from_arms a) true
theorem canonical_from_arms : canonical=fromArms NativePackagePrimitives.canonical :=
  (staged_from_arms NativePackagePrimitives.initial).symm
theorem missing_native_arm (a : Assignment NativePackagePrimitives.Cell NativePackagePrimitives.Value)
    (o : Owner) (hm : a (.inl o)=none) : fromArms a o=none := by simp [fromArms,hm]
theorem missing_supplement_arm (a : Assignment NativePackagePrimitives.Cell NativePackagePrimitives.Value)
    (o : Owner) (hm : a (.inr o)=none) : fromArms a o=none := by
  cases a (.inl o) <;> simp [fromArms,hm]
theorem copied_source (a : Assignment Owner Value) (o : Owner) :
    (image a (swapOwner o)).map (select true)=(a o).map (select false) := by
  cases o <;> simp [image,select,swapOwner,Option.map_map,Function.comp_def] <;> rfl
theorem canonical_native : nativeInputs canonical=AvailabilityPublication.native := by
  funext o; cases o <;> rfl
theorem canonical_objecthood : objecthoodInputs canonical=AvailabilityPublication.stages := by
  funext c; cases c with
  | inl o => cases o <;> rfl
  | inr o => cases o <;> rfl
theorem selected_native (o : Owner) (copy : Bool) :
    (canonical o).map (fun p => (select copy p).native)=some (AvailabilityPublication.selected o copy) := by
  cases o <;> cases copy <;> rfl
theorem selected_supplement (o : Owner) (copy : Bool) :
    (canonical o).map (fun p => (select copy p).supplement)=some supplement := by
  cases o <;> cases copy <;> rfl

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackageBundle
