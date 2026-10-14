import CSTTT.Fallback.HistoricalPackage

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PostWithdrawalQualifiedPrototype
open RegisterInterpreter NativePackageBundle PostWithdrawalPrototype
set_option autoImplicit false
-- All new statements are class (b): nominal protocol historical content and live runtime metadata have distinct roles.
def historicalNominalData (p : Input × Input) : NominalProtocol.Data Factor Bool Factor History Route Stage Bool Owner :=
  {PublicationNominal.data p with
    events := p.2.temporal.events.map (fun e => ⟨e.id,e.fromStage,e.toStage,e.atomic,e.strictStep,
      !e.id && p.2.receiver.sourcePresent,p.1.receiver.targetFunded⟩)
    receiver := {p.1.receiver with sourcePresent := p.2.receiver.sourcePresent}}
def historicalNominalViews (cell : Owner) : NominalProtocol.Views Owner MemoryValue Factor Bool Factor History Route Stage Bool Owner :=
  {PublicationNominal.views cell with
    events := ⟨cell,fun p => (historicalNominalData p).events⟩
    receiver := ⟨cell,fun p => (historicalNominalData p).receiver⟩}
theorem nominal_decoded (cell : Owner) (a : Assignment Owner MemoryValue) :
    (NominalProtocol.reader (historicalNominalViews cell)).read a=(a cell).map historicalNominalData := by
  cases ha : a cell <;> simp [NominalProtocol.reader,historicalNominalViews,PublicationNominal.views,
    StaticView.read,StaticView.ofCell,Expr.eval,ha,historicalNominalData,PublicationNominal.data]
def historicalNominalPassAt (cell : Owner) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers) : Prop :=
  ∃ wd, (PublicationNominal.metadata cell).eval a x ()=some wd ∧
    NominalProtocol.Pass (PublicationNominal.specification cell) wd (historicalNominalViews cell) a
theorem nominal_pass_iff (cell : Owner) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers) :
    historicalNominalPassAt cell a x ↔ ∃ p, a cell=some p ∧
      NominalProtocol.check (PublicationNominal.specification cell)
        (PublicationNominal.metadataValue p cell (x ()).2) (historicalNominalData p) := by
  simp only [historicalNominalPassAt,NominalProtocol.Pass,PublicationNominal.metadata_decoded,nominal_decoded]
  cases a cell <;> simp
theorem nominal_data_consistent (p : Input × Input)
    (consistent : p.2.receiver.sourcePresent=p.1.receiver.sourcePresent) :
    historicalNominalData p=PublicationNominal.data p := by
  simp [historicalNominalData,PublicationNominal.data,PublicationNominal.events,consistent]
theorem nominal_data_cut (pair : Bundle × Bundle) :
    historicalNominalData ((NativeJointCells.cutSource pair.1).native,pair.2.native)=
      historicalNominalData (pair.1.native,pair.2.native) := rfl
theorem nominal_reader_cut (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    (NominalProtocol.reader (historicalNominalViews cell)).read (nativeInputs (PublicationComposition.cutReceiver affected a))=
      (NominalProtocol.reader (historicalNominalViews cell)).read (nativeInputs a) := by
  rw [nominal_decoded,nominal_decoded]
  by_cases h : cell=affected
  all_goals cases ha : a cell <;> simp [nativeInputs,PublicationComposition.cutReceiver,h,ha]
  all_goals rfl
theorem nominal_metadata_cut (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (x : ModeExecution.Registers) :
    (PublicationNominal.metadata cell).eval (nativeInputs (PublicationComposition.cutReceiver affected a)) x ()=
      (PublicationNominal.metadata cell).eval (nativeInputs a) x () := by
  rw [PublicationNominal.metadata_decoded,PublicationNominal.metadata_decoded]
  by_cases h : cell=affected
  all_goals cases ha : a cell <;>
    simp [nativeInputs,PublicationComposition.cutReceiver,PublicationNominal.metadataValue,h,ha]
theorem nominal_cut_iff (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (x : ModeExecution.Registers) :
    historicalNominalPassAt cell (nativeInputs (PublicationComposition.cutReceiver affected a)) x ↔
      historicalNominalPassAt cell (nativeInputs a) x := by
  simp only [historicalNominalPassAt,NominalProtocol.Pass,nominal_reader_cut,nominal_metadata_cut]
theorem nominal_consistent_iff (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (x : ModeExecution.Registers)
    (consistent : ∀ pair,a cell=some pair → pair.2.native.receiver.sourcePresent=pair.1.native.receiver.sourcePresent) :
    historicalNominalPassAt cell (nativeInputs a) x ↔ PublicationNominal.PassAt cell (nativeInputs a) x := by
  rw [nominal_pass_iff,PublicationNominal.pass_iff]
  cases ha : a cell with
  | none => simp [nativeInputs,ha]
  | some pair =>
    simp only [nativeInputs,ha,Option.map_some,Option.some.injEq]
    constructor
    · rintro ⟨p,hp,check⟩
      cases hp
      exact ⟨_,rfl,by simpa only [nominal_data_consistent (pair.1.native,pair.2.native) (consistent pair ha)] using check⟩
    · rintro ⟨p,hp,check⟩
      cases hp
      exact ⟨_,rfl,by simpa only [nominal_data_consistent (pair.1.native,pair.2.native) (consistent pair ha)] using check⟩
def qualifiedPackageAt (b : Assignment Owner NativePackageBundle.Value) (cell : Owner) (x : ModeExecution.Registers) : Prop :=
  withdrawnPackageAt b cell x ∧ historicalNominalPassAt cell (nativeInputs b) x
-- The acquired-entry predicate remains the actual pre-cut interpreter; every post-cut package and resource field consumes the same cut assignment.
def QualifiedReadout (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b)
    (affected cell : Owner) : Prop :=
  StrategyGame.GameReadout (ResourceRuntime.rows (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b)))
    (ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b))
      (cutReady affected cell b (hb.resources cell))) (PublicationComposition.entries b hb cell)
    (ResourceRuntime.DomainCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell) ∧
      ResourceRuntime.WithdrawalCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell)
        (nativeInputs (PublicationComposition.cutReceiver affected b)))
    (qualifiedPackageAt (PublicationComposition.cutReceiver affected b) cell)
    (ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b)))
    (ResourceRuntime.Legal (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b)))
    (ResourceRuntime.StepLaw (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b))
      (cutReady affected cell b (hb.resources cell)))
theorem qualified_controller (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b)
    (cell affected : Owner) (controller : StrategyGame.Strategy ModeExecution.Registers Unit Bool)
    (hw : PublicationComposition.ControllerWins b hb cell controller)
    (consistent : ∀ pair, b cell=some pair → pair.2.native.receiver.sourcePresent=pair.1.native.receiver.sourcePresent) :
    QualifiedReadout b hb affected cell := by
  have roweq : ResourceRuntime.rows (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b))=
      ResourceRuntime.rows (PublicationResources.runtime cell) (nativeInputs b) := by
    funext x d act
    exact runtime_rows_cut affected cell (swapOwner cell) (PublicationReplay.names cell) b x d act
  have upeq : ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b))
      (cutReady affected cell b (hb.resources cell))=
      ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs b) (hb.resources cell) := by
    funext x d act o
    exact runtime_update_cut affected cell b _ _ x d act o
  refine ⟨⟨hw.1.1,?_⟩,hw.2.1,controller,?_⟩
  · exact (withdrawal_check_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) b).mpr hw.1.2
  · intro entry he x past hp
    rw [roweq,upeq] at hp
    obtain ⟨pkg,closed,laws⟩ := hw.2.2 entry he x past hp
    refine ⟨⟨⟨?_,?_⟩,?_⟩,?_,?_⟩
    · exact (historical_package_cut_iff affected cell b).mpr ((historical_package_consistent_iff b cell consistent).mpr pkg.1)
    · exact (runtime_inside_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) b x).mpr pkg.2.1
    · exact (nominal_cut_iff affected cell b x).mpr ((nominal_consistent_iff cell b x consistent).mpr pkg.2.2)
    · exact (resource_closed_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) b x).mpr closed
    · intro d
      obtain ⟨legal,normalized,step⟩ := laws d
      refine ⟨(runtime_legal_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) b x d _).mpr legal,?_,?_⟩
      · simpa only [roweq] using normalized
      · intro o positive
        have po := positive
        rw [roweq] at po
        exact (runtime_step_cut_iff affected cell b _ _ x d _ o).mpr (step o po)
theorem canonical_qualified_readout (affected cell : Owner) :
    QualifiedReadout NativePackageBundle.canonical PublicationComposition.canonical_ready affected cell :=
  qualified_controller NativePackageBundle.canonical PublicationComposition.canonical_ready cell affected
    PublicationResources.safeController (PublicationComposition.canonical_controller cell) (canonical_history_consistent cell)
theorem nominal_missing_rejected (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (x : ModeExecution.Registers) (missing : a cell=none) :
    ¬historicalNominalPassAt cell (nativeInputs (PublicationComposition.cutReceiver affected a)) x := by
  rw [nominal_cut_iff,nominal_pass_iff]
  simp [nativeInputs,missing]

-- The original nominal acquisition phase directly requires CURRENT receiver source presence.
theorem nominal_phase2_source_absent (cell : Owner) (d : NominalProtocol.Data Factor Bool Factor History Route Stage Bool Owner)
    (rid : Route) (absent : d.receiver.sourcePresent=false) :
    NominalProtocol.phase2 (PublicationNominal.specification cell) d rid=false := by
  unfold NominalProtocol.phase2
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  simp [NominalProtocol.active,absent]
-- Current-source withdrawal directly refutes the ORIGINAL nominal readout on every partial assignment and unbounded state.
theorem original_nominal_cut_rejected (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (x : ModeExecution.Registers) :
    ¬PublicationNominal.PassAt cell (nativeInputs (PublicationComposition.cutReceiver cell a)) x := by
  rw [PublicationNominal.pass_iff]
  cases ha : a cell with
  | none => simp [nativeInputs,PublicationComposition.cutReceiver,ha]
  | some pair =>
    rintro ⟨p,hp,check⟩
    simp [nativeInputs,PublicationComposition.cutReceiver,ha] at hp
    cases hp
    obtain ⟨_,_,_,_,_,_,_,_,_,_,all⟩ := check
    have positive := all (false,false,false) (factor_mem _)
    have negative := nominal_phase2_source_absent cell (PublicationNominal.data ((NativeJointCells.cutSource pair.1).native,pair.2.native)) (false,false,false) rfl
    have impossible : (false : Bool)=true := negative.symm.trans positive
    cases impossible
-- The same actual receiver-cut assignment has both original nominal rejection and the fully qualified historical target continuation.
theorem canonical_qualified_withdrawal_return (cell : Owner) :
    ¬PublicationNominal.PassAt cell (nativeInputs (PublicationComposition.cutReceiver cell NativePackageBundle.canonical))
      (PublicationResources.run cell (false,false,false) 0) ∧
    QualifiedReadout NativePackageBundle.canonical PublicationComposition.canonical_ready cell cell :=
  ⟨original_nominal_cut_rejected cell _ _,canonical_qualified_readout cell cell⟩

-- Removing the copied historical source flag also directly refutes the repaired nominal readout, for every partial assignment.
theorem historical_nominal_source_erased_rejected (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (x : ModeExecution.Registers) :
    ¬historicalNominalPassAt cell (nativeInputs (eraseCopiedSource cell a)) x := by
  rw [nominal_pass_iff]
  cases ha : a cell with
  | none => simp [nativeInputs,eraseCopiedSource,ha]
  | some pair =>
    rintro ⟨p,hp,check⟩
    simp [nativeInputs,eraseCopiedSource,ha] at hp
    cases hp
    obtain ⟨_,_,_,_,_,_,_,_,_,_,all⟩ := check
    have positive := all (false,false,false) (factor_mem _)
    have negative := nominal_phase2_source_absent cell
      (historicalNominalData (pair.1.native,(NativeJointCells.cutSource pair.2).native)) (false,false,false) rfl
    have impossible : (false : Bool)=true := negative.symm.trans positive
    cases impossible
-- A stored historical flag cannot hide actual SOURCE-mode presence in the independent runtime metadata.
theorem historical_nominal_source_mode_rejected (cell : Owner) (a : Assignment Owner MemoryValue)
    (x : ModeExecution.Registers) (sourceMode : (x ()).2=swapOwner cell) :
    ¬historicalNominalPassAt cell a x := by
  rw [nominal_pass_iff]
  rintro ⟨p,_,check⟩
  have absent := check.2.2.1
  simp [PublicationNominal.metadataValue,sourceMode] at absent
end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PostWithdrawalQualifiedPrototype
