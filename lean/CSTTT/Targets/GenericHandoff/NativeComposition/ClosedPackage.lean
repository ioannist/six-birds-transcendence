import CSTTT.Targets.GenericHandoff.NativeComposition.PackageBindings

/-! All eight fixed dispatcher algorithms are populated from one successively
published primitive bundle. C4–C7 surrogate grades remain explicit. This is
structural package construction; operational full handoff assembly is separate. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeClosedPackage
open RegisterInterpreter NativePackageBundle

def package (cell : Owner) (copy : Bool) : ClauseDispatcher.Package Owner NativePackageBundle.Value :=
  ⟨fun k => match k with
    | .c1 => .c1 inferInstance clauseSchema.toSchema NativeObjecthoodCells.reference (NativePackageBindings.c1 cell copy)
    | .c2 => .c2 inferInstance inferInstance clauseSchema (NativePackageBindings.profile cell copy)
    | .c3 => .c3 inferInstance inferInstance clauseSchema (NativePackageBindings.profile cell copy)
    | .c4 => .c4 inferInstance inferInstance ExposureRepair.schema (NativePackageBindings.exposure cell copy)
    | .c5 => .c5 inferInstance inferInstance inferInstance inferInstance
        (NativeCreditCells.schema (AvailabilityPublication.dataOwner cell copy)) (NativeCreditCells.bindings cell copy)
    | .c6 => .c6 inferInstance inferInstance inferInstance inferInstance inferInstance
        (factorSchema (AvailabilityPublication.dataOwner cell copy)) (NativePackageBindings.factor cell copy)
    | .c7 => .c7 inferInstance inferInstance inferInstance inferInstance inferInstance NativeJointCells.schema (NativeJointCells.bindings cell copy)
    | .c8 => .c8 inferInstance inferInstance inferInstance
        (NativeOperationalCells.schema (AvailabilityPublication.dataOwner cell copy)) factors (NativePackageBindings.operational cell copy)⟩

def rawReadout (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) : Prop :=
  ObjecthoodProtocol.Accept clauseSchema.toSchema NativeObjecthoodCells.reference (NativeObjecthoodCells.bindings cell copy)
    (NativePackageBundle.objecthoodInputs a) ∧
  ProfileRules.C2Accept clauseSchema (ProfileCells.bindings cell copy) (NativePackageBundle.nativeInputs a) ∧
  (ClauseDispatcher.Rule.c3 inferInstance inferInstance clauseSchema (ProfileCells.bindings cell copy)).accept (NativePackageBundle.nativeInputs a) ∧
  ExposureRules.AssignedAccept ExposureRepair.schema (ExposureRepair.bindings cell copy) (NativePackageBundle.nativeInputs a) ∧
  ProtocolCreditRules.AssignedAccept (NativeCreditCells.schema (AvailabilityPublication.dataOwner cell copy)) (NativeCreditCells.bindings cell copy) a ∧
  TemporalFactorCells.Accept (factorSchema (AvailabilityPublication.dataOwner cell copy)) (MemoryFrames.bindings cell copy) (NativePackageBundle.nativeInputs a) ∧
  JointRules.AssignedAccept NativeJointCells.schema (NativeJointCells.bindings cell copy) a ∧
  OperationalCells.Accept (NativeOperationalCells.schema (AvailabilityPublication.dataOwner cell copy)) factors
    (NativeOperationalCells.bindings cell copy) (NativePackageBundle.nativeInputs a)

theorem acceptance_iff (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    (package cell copy).accept a ↔ rawReadout cell copy a := by
  constructor
  · intro h
    exact ⟨(NativePackageBindings.c1_accept_iff cell copy a).mp (h .c1),
      (NativePackageBindings.c2_accept_iff cell copy a).mp (h .c2),
      (NativePackageBindings.c3_accept_iff cell copy a).mp (h .c3),
      (NativePackageBindings.c4_accept_iff cell copy a).mp (h .c4),h .c5,
      (NativePackageBindings.c6_accept_iff _ cell copy a).mp (h .c6),h .c7,
      (NativePackageBindings.c8_accept_iff _ cell copy a).mp (h .c8)⟩
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ k
    cases k
    · exact (NativePackageBindings.c1_accept_iff cell copy a).mpr h1
    · exact (NativePackageBindings.c2_accept_iff cell copy a).mpr h2
    · exact (NativePackageBindings.c3_accept_iff cell copy a).mpr h3
    · exact (NativePackageBindings.c4_accept_iff cell copy a).mpr h4
    · exact h5
    · exact (NativePackageBindings.c6_accept_iff _ cell copy a).mpr h6
    · exact h7
    · exact (NativePackageBindings.c8_accept_iff _ cell copy a).mpr h8

theorem actual_package (cell : Owner) (copy : Bool) : (package cell copy).accept NativePackageBundle.canonical := by
  rw [acceptance_iff]
  unfold rawReadout
  rw [canonical_native,canonical_objecthood]
  exact ⟨AvailabilityPublication.c1 cell copy,AvailabilityPublication.c2 cell copy,
    AvailabilityPublication.c3 cell copy,AvailabilityPublication.c4 cell copy,NativeCreditCells.c5 cell copy,
    AvailabilityPublication.c6 cell copy,NativeJointCells.c7 cell copy,NativeOperationalCells.c8 cell copy⟩
theorem source_package : (package true true).accept NativePackageBundle.canonical := actual_package true true
theorem middle_target_package : (package true false).accept NativePackageBundle.canonical := actual_package true false
theorem middle_source_package : (package false true).accept NativePackageBundle.canonical := actual_package false true
theorem final_target_package : (package false false).accept NativePackageBundle.canonical := actual_package false false

theorem clause_scope (cell : Owner) (copy : Bool) (k : ClauseDispatcher.Kind) :
    cell ∈ ((package cell copy).rule k).scope := by
  cases k <;> simp [package,ClauseDispatcher.Rule.scope,ObjecthoodCells.Bindings.scope,ProfileRules.ClauseBindings.scope,
    ProfileRules.Bindings.scope,ExposureRules.Bindings.scope,ProtocolCreditRules.Bindings.scope,TemporalFactorCells.Bindings.scope,
    JointRules.Bindings.scope,OperationalViability.Bindings.scope,NativePackageBindings.c1,NativePackageBindings.profile,
    NativePackageBindings.exposure,NativePackageBindings.factor,NativePackageBindings.operational,
    NativePackageBindings.nativeView,NativePackageBindings.objecthoodView,CellReindex.cellView,
    NativeObjecthoodCells.bindings,NativeObjecthoodCells.cellOwner,ProfileCells.bindings,ExposureRepair.bindings,
    MemoryFrames.bindings,NativeOperationalCells.bindings,NativeCreditCells.bindings,NativeJointCells.bindings]
theorem missing_package_rejected (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value)
    (hm : a cell=none) : ¬ (package cell copy).accept a :=
  ClauseDispatcher.Package.missing_rejected (package cell copy) a .c1 cell (clause_scope cell copy .c1) hm

def mapCurrent (f : Bundle → Bundle) (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    Assignment Owner NativePackageBundle.Value :=
  fun o => if o=cell then (a o).map (fun p => (f p.1,p.2)) else a o
theorem source_bundle_preserved (f : Bundle → Bundle) (cell o : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    (mapCurrent f cell a o).map (select true)=(a o).map (select true) := by
  by_cases h : o=cell
  · simp [mapCurrent,h,select,Option.map_map,Function.comp_def]
    rfl
  · simp [mapCurrent,h]
theorem source_map_preserved {X : Type} (g : Bundle → X) (f : Bundle → Bundle)
    (cell o : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    (mapCurrent f cell a o).map (fun p => g p.2)=(a o).map (fun p => g p.2) := by
  have h := congrArg (fun z : Option Bundle => z.map g) (source_bundle_preserved f cell o a)
  simpa [Option.map_map,select] using h
theorem source_package_preserved (f : Bundle → Bundle) (cell o : Owner)
    (a : Assignment Owner NativePackageBundle.Value) :
    (package o true).accept (mapCurrent f cell a) ↔ (package o true).accept a := by
  unfold ClauseDispatcher.Package.accept
  apply forall_congr'
  intro k
  cases k <;> simp only [package,ClauseDispatcher.Rule.accept,ObjecthoodProtocol.Accept,
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
  all_goals by_cases h : o=cell
  all_goals cases ha : a o <;> simp [mapCurrent,h,ha]
theorem source_c5_preserved (f : Bundle → Bundle) (cell o : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    ProtocolCreditRules.decoded (NativeCreditCells.bindings o true) (mapCurrent f cell a)=
      ProtocolCreditRules.decoded (NativeCreditCells.bindings o true) a := by
  rw [NativeCreditCells.decoded,NativeCreditCells.decoded]
  have h := congrArg (fun z : Option Bundle => z.map NativeCreditCells.data) (source_bundle_preserved f cell o a)
  simpa [Option.map_map] using h
theorem source_c7_preserved (f : Bundle → Bundle) (cell o : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    JointRules.decoded (NativeJointCells.bindings o true) (mapCurrent f cell a)=
      JointRules.decoded (NativeJointCells.bindings o true) a := by
  rw [NativeJointCells.decoded,NativeJointCells.decoded]
  have h := congrArg (fun z : Option Bundle => z.map NativeJointCells.data) (source_bundle_preserved f cell o a)
  simpa [Option.map_map] using h
theorem cut_c5_decoded (cell : Owner) :
    ProtocolCreditRules.decoded (NativeCreditCells.bindings cell false)
      (mapCurrent NativeCreditCells.cutSelfEdges cell NativePackageBundle.canonical)=
      some (NativeCreditCells.data (NativeCreditCells.cutSelfEdges
        ⟨AvailabilityPublication.selected cell false,NativePackagePrimitives.supplement⟩)) := by
  cases cell <;> rfl
theorem cut_actual_package_rejected (cell : Owner) :
    ¬ (package cell false).accept (mapCurrent NativeCreditCells.cutSelfEdges cell NativePackageBundle.canonical) := by
  intro h
  obtain ⟨d,hd,ha⟩ := h .c5
  rw [cut_c5_decoded] at hd
  have he := Option.some.inj hd
  subst d
  exact NativeCreditCells.cut_actual_c5_rejected _ _ ha
theorem erased_c7_decoded (cell : Owner) :
    JointRules.decoded (NativeJointCells.bindings cell false)
      (mapCurrent NativeJointCells.eraseObservable cell NativePackageBundle.canonical)=
      some (NativeJointCells.data (NativeJointCells.eraseObservable
        ⟨AvailabilityPublication.selected cell false,NativePackagePrimitives.supplement⟩)) := by
  cases cell <;> rfl
theorem erased_actual_package_rejected (cell : Owner) :
    ¬ (package cell false).accept (mapCurrent NativeJointCells.eraseObservable cell NativePackageBundle.canonical) := by
  intro h
  obtain ⟨d,hd,ha⟩ := h .c7
  rw [erased_c7_decoded] at hd
  have he := Option.some.inj hd
  subst d
  exact NativeJointCells.erased_actual_c7_rejected _ ha

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeClosedPackage
