import CSTTT.FullNative.ProgramExecution

/-! Derived all-word and actual-execution obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Binding
set_option autoImplicit false
set_option maxHeartbeats 8000000

def currentPublic (s : State) : Nat × Nat × Nat :=
  (publicLens s,((rows s false).map Prod.snd).sum,((rows s true).map Prod.snd).sum)

def Admissible {V : Type} (f : State → V) : Prop := ∃ g : Nat × Nat × Nat → V, f=g ∘ currentPublic

theorem inside_public (s : State) (inside : s.outside=false) : currentPublic s=(0,16,16) := by
  cases s with
  | mk p u v r phase =>
    cases p
    · cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel
    · contradiction

theorem non_exposure {V : Type} (f : State → V) (admissible : Admissible f)
    (s t : State) (hs : s.outside=false) (ht : t.outside=false) : f s=f t := by
  rcases admissible with ⟨g,rfl⟩
  simp only [Function.comp_apply,inside_public s hs,inside_public t ht]

theorem strict_promotion :
    currentPublic FullInterface.replicaLeft=currentPublic (⟨false,false,true,false,true⟩:State) ∧
    classes model FullInterface.replicaLeft≠classes model (⟨false,false,true,false,true⟩:State) := by
  simp only [first_profile_equation]
  decide +kernel

theorem expanded_channel_exposes :
    classes model FullInterface.replicaLeft≠classes model (⟨false,false,true,false,true⟩:State) :=
  strict_promotion.2

/-- Current availability is read from the actual enabled installed rows. -/
def actualCurrent (x : PhysicalExecution.Execution) : Nat × Nat × Nat :=
  (publicLens x.resident.current,
    ((PhysicalExecution.rawRows AccountExecution.renewable x false).map Prod.snd).sum,
    ((PhysicalExecution.rawRows AccountExecution.renewable x true).map Prod.snd).sum)

def ActualAdmissible {V : Type} (f : PhysicalExecution.Execution → V) : Prop :=
  ∃ g : Nat × Nat × Nat → V, f=g ∘ actualCurrent

theorem actual_current_sector (x : PhysicalExecution.Execution) (h : PhysicalExecution.sector x) :
    actualCurrent x=currentPublic x.resident.current := by
  simp only [actualCurrent,currentPublic,PhysicalExecution.sector_rows x h,List.map_map]
  rfl

theorem actual_non_exposure {V : Type} (f : PhysicalExecution.Execution → V)
    (admissible : ActualAdmissible f) (x y : PhysicalExecution.Execution)
    (hx : PhysicalExecution.sector x) (hy : PhysicalExecution.sector y)
    (ix : x.resident.current.outside=false) (iy : y.resident.current.outside=false) : f x=f y := by
  rcases admissible with ⟨g,rfl⟩
  simp only [Function.comp_apply,actual_current_sector x hx,actual_current_sector y hy,
    inside_public _ ix,inside_public _ iy]

/-- Adding the actual predictor is an explicitly expanded channel family. -/
def expandedCurrent (s : State) : (Nat × Nat × Nat) × Nat := (currentPublic s,classes model s)

theorem expanded_distinguishes :
    expandedCurrent FullInterface.replicaLeft≠expandedCurrent (⟨false,false,true,false,true⟩:State) := by
  intro h
  exact strict_promotion.2 (congrArg Prod.snd h)

end CSTTT.FullNative.Binding
