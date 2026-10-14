import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationCorridor
import CSTTT.Targets.GenericHandoff.StageComposition

/-! Every clause sees the same raw bundled publication instruction. The
composite stage executes those instructions in sequence through the literal
middle value. Acceptance is still computed by the separate fixed dispatcher. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationMaps
open RegisterInterpreter NativePackageBundle

def language : TranslationLanguage Owner Owner NativePackageBundle.Value NativePackageBundle.Value where
  Instruction _ _ := Unit
  execute _ p := some (publishBundle p.1,p.1)
def stage : GenericHandoff.Stage (Index := ClauseDispatcher.Kind) language :=
  fun _ t => some ⟨swapOwner t,()⟩
def scopes (_ : ClauseDispatcher.Kind) : List Owner := [false,true]
def cover : RawCover ClauseDispatcher.Kind Owner := ⟨ClauseDispatcher.kinds,scopes,fun _ _ => true⟩
def composite := StageComposition.stage language language stage stage scopes

theorem local_image (a : Assignment Owner NativePackageBundle.Value) (k : ClauseDispatcher.Kind) :
    mappedLocal language a stage scopes k=NativePackageBundle.image a := by
  funext o
  cases ha : a (swapOwner o) <;> cases o <;> simp [mappedLocal,language,stage,scopes,NativePackageBundle.image,ha]
theorem cover_check : CoverCheck cover := by
  constructor
  · intro o
    refine ⟨.c1,by decide +kernel,?_⟩
    cases o <;> decide +kernel
  · intro i j o hi hj
    exact .step hi hj rfl (.refl j hj)
theorem compatible (a : Assignment Owner NativePackageBundle.Value) :
    EdgeCompatible cover (mappedLocal language a stage cover.scopes) := by
  intro i j o _ _ _
  exact congrFun ((local_image a i).trans (local_image a j).symm) o

theorem global_image (a : Assignment Owner NativePackageBundle.Value) :
    PackageEngine.global language a stage cover=NativePackageBundle.image a := by
  funext o
  have he := glued_restricts cover (mappedLocal language a stage cover.scopes) cover_check (compatible a) .c1 o
    (by cases o <;> decide +kernel)
  exact he.trans (congrFun (local_image a .c1) o)
theorem composite_local (a : Assignment Owner NativePackageBundle.Value) (k : ClauseDispatcher.Kind) :
    mappedLocal (StageComposition.language language language) a composite scopes k=
      NativePackageBundle.image (NativePackageBundle.image a) := by
  unfold composite
  rw [StageComposition.local_equation,local_image,local_image]
theorem composite_global (a : Assignment Owner NativePackageBundle.Value) :
    PackageEngine.global (StageComposition.language language language) a composite cover=
      NativePackageBundle.image (NativePackageBundle.image a) := by
  unfold composite
  rw [StageComposition.global_equation language language stage stage scopes a cover cover rfl cover_check
    (compatible a) (by intro i t ht r hr; cases r.source <;> simp [scopes]),global_image,global_image]

theorem actual_stage_exposure (a : Assignment Owner NativePackageBundle.Value) :
    NativePackageBundle.staged a true=PackageEngine.global language a stage cover true ∧
    NativePackageBundle.staged a false=
      PackageEngine.global (StageComposition.language language language) a composite cover false := by
  rw [global_image,composite_global]
  exact ⟨rfl,rfl⟩
theorem middle_shared (a : Assignment Owner NativePackageBundle.Value) :
    (PackageEngine.global language a stage cover true).map (select false)=
      (PackageEngine.global (StageComposition.language language language) a composite cover false).map (select true) := by
  rw [global_image,composite_global]
  exact (copied_source (NativePackageBundle.image a) true).symm

theorem composite_arrow (k : ClauseDispatcher.Kind) (o : Owner) :
    composite k o=some ⟨o,⟨swapOwner o,(),()⟩⟩ := by
  cases o <;> simp [composite,StageComposition.stage,stage,scopes,swapOwner]
theorem composite_missing (a : Assignment Owner NativePackageBundle.Value) (o : Owner)
    (hm : a o=none) (k : ClauseDispatcher.Kind) :
    mappedLocal (StageComposition.language language language) a composite scopes k o=none := by
  rw [composite_local]
  cases o <;> simp [NativePackageBundle.image,swapOwner,hm]

theorem raw_credit_transport (b : Bundle) :
    ProtocolCreditRules.Transport (NativeCreditCells.data b).tables
      (NativeCreditCells.data (publishBundle b)).tables NativeCreditCells.protocols id id
      NativePackagePrimitives.translateOwner := NativePackagePrimitives.credit_raw_transport b.native b.supplement

theorem raw_joint_transport (b : Bundle) :
    JointHistoryTransport.Transport NativeJointCells.schema NativeJointCells.schema
      (NativeJointCells.data b) (NativeJointCells.data (publishBundle b)) NativeJointCells.historyImage :=
  NativeJointCells.actual_history_transport b

theorem raw_joint_transport_twice (b : Bundle) :
    JointHistoryTransport.Transport NativeJointCells.schema NativeJointCells.schema
      (NativeJointCells.data b) (NativeJointCells.data (publishBundle (publishBundle b)))
      (NativeJointCells.historyImage ∘ NativeJointCells.historyImage) := by
  refine ⟨rfl,?_⟩
  intro id hi
  have h1 := (raw_joint_transport b).2 id hi
  have h2 := (raw_joint_transport (publishBundle b)).2 id hi
  refine ⟨?_,h1.2.1.trans h2.2.1,h1.2.2.trans h2.2.2⟩
  rw [← h2.1]
  have he := congrArg (fun p : List (List Factor) × List (List Factor) =>
    (p.1.map NativeJointCells.historyImage,p.2.map NativeJointCells.historyImage)) h1.1
  simpa only [List.map_map,Function.comp_def] using he

def exposure (a : Assignment Owner NativePackageBundle.Value) : Assignment Owner NativePackageBundle.Value :=
  fun o => if o then PackageEngine.global language a stage cover o else
    PackageEngine.global (StageComposition.language language language) a composite cover o

theorem exposure_equation (a : Assignment Owner NativePackageBundle.Value) : exposure a=NativePackageBundle.staged a := by
  funext o
  cases o
  · exact (actual_stage_exposure a).2.symm
  · exact (actual_stage_exposure a).1.symm
theorem canonical_exposure : exposure NativePackageBundle.initial=NativePackageBundle.canonical := exposure_equation _
theorem actual_clauses (cell copy : Owner) :
    (NativeClosedPackage.package cell copy).accept (exposure NativePackageBundle.initial) := by
  rw [canonical_exposure]
  exact NativeClosedPackage.actual_package cell copy

theorem whole_package_copied (a : Assignment Owner NativePackageBundle.Value) :
    (NativeClosedPackage.package false true).accept (NativePackageBundle.image (NativePackageBundle.image a)) ↔
      (NativeClosedPackage.package true false).accept (NativePackageBundle.image a) := by
  unfold ClauseDispatcher.Package.accept
  apply forall_congr'
  intro k
  cases k <;> simp only [NativeClosedPackage.package,ClauseDispatcher.Rule.accept,ObjecthoodProtocol.Accept,
    ProfileRules.C2Accept,ProfileRules.C3Accept,ExposureRules.AssignedAccept,ProtocolCreditRules.AssignedAccept,
    TemporalFactorCells.Accept,JointRules.AssignedAccept,OperationalCells.Accept,
    ObjecthoodCells.decoded,ProfileRules.decodedClause,ProfileRules.decoded,ExposureRules.decoded,
    ProtocolCreditRules.decoded,TemporalFactorCells.decoded,JointRules.decoded,OperationalViability.decoded,
    NativePackageBindings.c1,NativePackageBindings.profile,NativePackageBindings.exposure,NativePackageBindings.factor,
    NativePackageBindings.operational,NativePackageBindings.nativeView,NativePackageBindings.objecthoodView,
    CellReindex.cellView,NativePackageBindings.nativeValue,NativePackageBindings.objecthoodValue,
    NativeObjecthoodCells.bindings,NativeObjecthoodCells.cellOwner,ProfileCells.bindings,ExposureRepair.bindings,
    MemoryFrames.bindings,NativeOperationalCells.bindings,NativeCreditCells.bindings,NativeJointCells.bindings,
    NativeObjecthoodCells.selectSupplement,MemoryFrames.selectInput,select,ite_true,CellView.read]
  all_goals cases ha : a false <;> simp [NativePackageBundle.image,swapOwner,ha,select,
    AvailabilityPublication.dataOwner]


end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationMaps
