import CSTTT.Targets.GenericHandoff.NativeComposition.AvailabilityObjecthood
import CSTTT.Targets.GenericHandoff.NativeComposition.ExposureRepair
import CSTTT.Targets.GenericHandoff.NativeComposition.ObjecthoodPublication

/-! One actual two-publication native input now populates C1/C2/C3/C4/C6
at original, middle and final positions. Generic decoders and copy laws still
apply to every partial assignment. This is not a full C1–C8 package. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.AvailabilityPublication
open RegisterInterpreter

def initial : Assignment NativeObjecthoodCells.Cell NativeObjecthoodCells.Value
  | .inl o => some (AvailabilityFactor.input o,AvailabilityFactor.input o)
  | .inr _ => some (NativeObjecthoodCells.supplement,NativeObjecthoodCells.supplement)
def stages := NativeObjecthoodCells.staged initial
def native := NativeObjecthoodCells.nativeInputs stages
def selected (cell : Owner) (copy : Bool) : Input :=
  if cell then (if copy then AvailabilityFactor.input false else publish (AvailabilityFactor.input false))
  else (if copy then publish (AvailabilityFactor.input false) else publish (publish (AvailabilityFactor.input false)))
def dataOwner (cell : Owner) (copy : Bool) := if copy then swapOwner cell else cell

theorem selected_present (cell : Owner) (copy : Bool) :
    MemoryFrames.inputs copy native cell=some (selected cell copy) := by
  cases cell <;> cases copy <;> rfl
theorem selected_objecthood (cell : Owner) (copy : Bool) :
    NativeObjecthoodCells.data (selected cell copy) NativeObjecthoodCells.supplement=AvailabilityObjecthood.raw := by
  cases cell <;> cases copy <;> rfl
theorem selected_profile (cell : Owner) (copy : Bool) :
    ProfileCells.data (selected cell copy)=AvailabilityFactor.profile := by
  cases cell <;> cases copy <;> rfl
theorem selected_classes (cell : Owner) (copy : Bool) :
    (selected cell copy).temporal.classes=labels := by
  cases cell <;> cases copy <;> rfl
theorem selected_exposure (cell : Owner) (copy : Bool) :
    ExposureRepair.data (selected cell copy)=ExposureRepair.data (AvailabilityFactor.input false) := by
  cases cell <;> cases copy <;> rfl

theorem c1_decoded (cell : Owner) (copy : Bool) :
    ObjecthoodCells.decoded clauseSchema.toSchema (NativeObjecthoodCells.bindings cell copy) stages=
      some AvailabilityObjecthood.raw := by
  cases cell <;> cases copy <;> rfl
theorem c1 (cell : Owner) (copy : Bool) :
    ObjecthoodProtocol.Accept clauseSchema.toSchema NativeObjecthoodCells.reference
      (NativeObjecthoodCells.bindings cell copy) stages :=
  ⟨AvailabilityObjecthood.raw,c1_decoded cell copy,AvailabilityObjecthood.actual_c1_accept,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem profile_decoded (cell : Owner) (copy : Bool) :
    ProfileRules.decodedClause clauseSchema (ProfileCells.bindings cell copy) native=
      some (AvailabilityFactor.profile,labels) := by
  cases cell <;> cases copy <;> rfl
theorem c2 (cell : Owner) (copy : Bool) :
    ProfileRules.C2Accept clauseSchema (ProfileCells.bindings cell copy) native := by
  refine ⟨factor_domain,AvailabilityFactor.profile,labels,profile_decoded cell copy,?_,
    AvailabilityFactor.linked false,AvailabilityFactor.promotion⟩
  simp only [ProfileRules.RowsValid]; decide +kernel
theorem c3 (cell : Owner) (copy : Bool) :
    (ClauseDispatcher.Rule.c3 inferInstance inferInstance clauseSchema (ProfileCells.bindings cell copy)).accept native := by
  refine ⟨⟨factor_domain,AvailabilityFactor.profile,labels,profile_decoded cell copy,?_,
    AvailabilityFactor.linked false,AvailabilityFactor.recursive_profile⟩,
    AvailabilityFactor.profile,labels,profile_decoded cell copy,AvailabilityFactor.stable_profile⟩
  simp only [ProfileRules.RowsValid]; decide +kernel
theorem c4_decoded (cell : Owner) (copy : Bool) :
    ExposureRules.decoded (ExposureRepair.bindings cell copy) native=
      some (ExposureRepair.data (AvailabilityFactor.input false)) := by
  cases cell <;> cases copy <;> rfl
theorem c4 (cell : Owner) (copy : Bool) :
    ExposureRules.AssignedAccept ExposureRepair.schema (ExposureRepair.bindings cell copy) native :=
  ⟨_,c4_decoded cell copy,ExposureRepair.actual_c4_accept⟩

theorem first_published_factor_accept :
    TemporalFactorRules.Accept (factorSchema true) (publish (AvailabilityFactor.input false)).temporal := by
  obtain ⟨hd,hs,ht,hr,hlink,htrace,hfund,hinterface,hbisim,hcoarse⟩ := AvailabilityFactor.factor_accept true
  refine ⟨hd,hs,ht,hr,hlink,?_,hfund,hinterface,hbisim,hcoarse⟩
  simp only [TemporalFactorRules.Trace]; decide +kernel
theorem final_published_factor_accept :
    TemporalFactorRules.Accept (factorSchema false) (publish (publish (AvailabilityFactor.input false))).temporal := by
  obtain ⟨hd,hs,ht,hr,hlink,htrace,hfund,hinterface,hbisim,hcoarse⟩ := AvailabilityFactor.factor_accept false
  refine ⟨hd,hs,ht,hr,hlink,?_,hfund,hinterface,hbisim,hcoarse⟩
  simp only [TemporalFactorRules.Trace]; decide +kernel
theorem selected_factor_accept (cell : Owner) (copy : Bool) :
    TemporalFactorRules.Accept (factorSchema (dataOwner cell copy)) (selected cell copy).temporal := by
  cases cell <;> cases copy
  · exact final_published_factor_accept
  · exact first_published_factor_accept
  · exact first_published_factor_accept
  · exact AvailabilityFactor.factor_accept false
theorem c6_decoded (cell : Owner) (copy : Bool) :
    TemporalFactorCells.decoded (MemoryFrames.bindings cell copy) native=some (selected cell copy).temporal := by
  cases cell <;> cases copy <;> rfl
theorem c6 (cell : Owner) (copy : Bool) :
    TemporalFactorCells.Accept (factorSchema (dataOwner cell copy)) (MemoryFrames.bindings cell copy) native :=
  ⟨_,c6_decoded cell copy,selected_factor_accept cell copy⟩

theorem actual_shared_structural_clauses (cell : Owner) (copy : Bool) :
    ObjecthoodProtocol.Accept clauseSchema.toSchema NativeObjecthoodCells.reference
      (NativeObjecthoodCells.bindings cell copy) stages ∧
    ProfileRules.C2Accept clauseSchema (ProfileCells.bindings cell copy) native ∧
    (ClauseDispatcher.Rule.c3 inferInstance inferInstance clauseSchema (ProfileCells.bindings cell copy)).accept native ∧
    ExposureRules.AssignedAccept ExposureRepair.schema (ExposureRepair.bindings cell copy) native ∧
    TemporalFactorCells.Accept (factorSchema (dataOwner cell copy)) (MemoryFrames.bindings cell copy) native :=
  ⟨c1 cell copy,c2 cell copy,c3 cell copy,c4 cell copy,c6 cell copy⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.AvailabilityPublication
