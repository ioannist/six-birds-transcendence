import CSTTT.Prospects.Statements
import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationComposition
import CSTTT.Fallback.GuardedFusion


namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PostWithdrawalPrototype
open RegisterInterpreter NativePackageBundle
set_option autoImplicit false
-- Class (b): all independent clauses except the C7 live-source gate ignore receiver source presence.
theorem clause_receiver_cut_iff (affected cell : Owner) (copy : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (k : ClauseDispatcher.Kind) (notC7 : k≠.c7) :
    ((NativeClosedPackage.package cell copy).rule k).accept (PublicationComposition.cutReceiver affected a) ↔
      ((NativeClosedPackage.package cell copy).rule k).accept a := by
  cases k <;> try contradiction
  all_goals simp only [NativeClosedPackage.package,ClauseDispatcher.Rule.accept,ObjecthoodProtocol.Accept,
    ProfileRules.C2Accept,ProfileRules.C3Accept,ExposureRules.AssignedAccept,ProtocolCreditRules.AssignedAccept,
    TemporalFactorCells.Accept,OperationalCells.Accept,
    ObjecthoodCells.decoded,ProfileRules.decodedClause,ProfileRules.decoded,ExposureRules.decoded,
    ProtocolCreditRules.decoded,TemporalFactorCells.decoded,OperationalViability.decoded,
    NativePackageBindings.c1,NativePackageBindings.profile,NativePackageBindings.exposure,NativePackageBindings.factor,
    NativePackageBindings.operational,NativePackageBindings.nativeView,NativePackageBindings.objecthoodView,
    CellReindex.cellView,NativePackageBindings.nativeValue,NativePackageBindings.objecthoodValue,
    NativeObjecthoodCells.bindings,NativeObjecthoodCells.cellOwner,ProfileCells.bindings,ExposureRepair.bindings,
    MemoryFrames.bindings,NativeOperationalCells.bindings,NativeCreditCells.bindings,
    NativeObjecthoodCells.selectSupplement,MemoryFrames.selectInput,select,CellView.read]
  all_goals by_cases h : cell=affected
  all_goals cases ha : a cell <;> cases copy <;>
    simp [PublicationComposition.cutReceiver,h,ha]
  all_goals rfl
-- Class (b): current live C7 directly blocks the complete target package after source withdrawal, on every partial assignment.
theorem cut_current_package_rejected (affected : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    ¬(NativeClosedPackage.package affected false).accept (PublicationComposition.cutReceiver affected a) := by
  intro accepted
  have c7 : JointRules.AssignedAccept NativeJointCells.schema (NativeJointCells.bindings affected false)
      (PublicationComposition.cutReceiver affected a) := accepted .c7
  obtain ⟨data,decoded,passes⟩ := c7
  rw [NativeJointCells.decoded] at decoded
  cases ha : a affected with
  | none => simp [PublicationComposition.cutReceiver,ha] at decoded
  | some pair =>
    have eq : NativeJointCells.data (NativeJointCells.cutSource pair.1)=data := by
      simpa [PublicationComposition.cutReceiver,ha,select,NativeJointCells.cutSource] using decoded
    subst data
    exact NativeJointCells.cut_actual_c7_rejected pair.1 passes


-- Class (b): C7 historical provenance reads the actual copied source bundle, while funding reads the current target.
def historicalData (pair : Bundle × Bundle) :
    JointRules.Raw Factor Bool Factor Bool Factor Bool Bool Bool Unit Stage Bool :=
  {NativeJointCells.data pair.1 with
    events := pair.1.native.temporal.events.map (fun event =>
      ⟨event.id,event.fromStage,event.toStage,event.atomic,
        (!event.id && pair.2.native.receiver.sourcePresent),pair.1.native.receiver.targetFunded⟩)
    receiver := ⟨pair.2.native.receiver.sourcePresent,pair.1.native.receiver.targetFunded,
      pair.1.native.receiver.funded,pair.1.native.receiver.mixedRequired⟩}
def historicalBindings (cell : Owner) :
    JointRules.Bindings Owner NativePackageBundle.Value Factor Bool Factor Bool Factor Bool Bool Bool Unit Stage Bool :=
  {NativeJointCells.bindings cell false with
    events := ⟨cell,fun pair => (historicalData pair).events⟩
    receiver := ⟨cell,fun pair => (historicalData pair).receiver⟩}
-- Class (b): complete optional historical C7 decoder on all raw assignments, without a default source snapshot.
theorem historical_decoded (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    JointRules.decoded (historicalBindings cell) a=(a cell).map historicalData := by
  cases ha : a cell <;> simp [JointRules.decoded,historicalBindings,NativeJointCells.bindings,
    historicalData,NativeJointCells.data,select,CellView.read,ha]
-- Class (b): withdrawing the current live source preserves the copied historical source literally.
theorem historical_data_current_cut (pair : Bundle × Bundle) :
    historicalData (NativeJointCells.cutSource pair.1,pair.2)=historicalData pair := rfl
-- Class (b): every partial assignment preserves the historical C7 decoder through the actual receiver cut.
theorem historical_decoded_cut (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    JointRules.decoded (historicalBindings cell) (PublicationComposition.cutReceiver affected a)=
      JointRules.decoded (historicalBindings cell) a := by
  rw [historical_decoded,historical_decoded]
  by_cases h : cell=affected
  · cases ha : a cell <;> simp [PublicationComposition.cutReceiver,h,ha,historicalData,
      NativeJointCells.data,NativeJointCells.events,NativeJointCells.receiver]
  · simp [PublicationComposition.cutReceiver,h]
-- Class (b): this explicit successor replaces only the live-source C7 binding by historical provenance, retaining all other clauses.
def historicalPackage (cell : Owner) : ClauseDispatcher.Package Owner NativePackageBundle.Value :=
  ⟨fun kind => match kind with
    | .c7 => .c7 inferInstance inferInstance inferInstance inferInstance inferInstance NativeJointCells.schema (historicalBindings cell)
    | other => (NativeClosedPackage.package cell false).rule other⟩
-- Class (b): independent historical package acceptance is unchanged by current-source withdrawal, for all partial assignments.
theorem historical_package_cut_iff (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    (historicalPackage cell).accept (PublicationComposition.cutReceiver affected a) ↔
      (historicalPackage cell).accept a := by
  unfold ClauseDispatcher.Package.accept
  apply forall_congr'
  intro kind
  cases kind
  case c7 => simp only [historicalPackage,ClauseDispatcher.Rule.accept,JointRules.AssignedAccept,historical_decoded_cut]
  all_goals exact clause_receiver_cut_iff affected cell false a _ (by decide)
-- Class (b): when the copied source-presence flag equals the current flag, the historical data agrees with the old live C7 data.
theorem historical_data_consistent (pair : Bundle × Bundle)
    (consistent : pair.2.native.receiver.sourcePresent=pair.1.native.receiver.sourcePresent) :
    historicalData pair=NativeJointCells.data pair.1 := by
  simp [historicalData,NativeJointCells.data,NativeJointCells.events,NativeJointCells.receiver,consistent]
-- Class (b): actual primitive publication copies source presence without choosing a package verdict.
theorem published_historical_data (a : Assignment Owner NativePackageBundle.Value) (cell : Owner) :
    (NativePackageBundle.image a cell).map historicalData=
      (NativePackageBundle.image a cell).map (fun pair => NativeJointCells.data pair.1) := by
  cases ha : a (swapOwner cell) with
  | none => simp [NativePackageBundle.image,ha]
  | some pair =>
    simp only [NativePackageBundle.image,ha,Option.map_some]
    exact congrArg some (historical_data_consistent (publishBundle pair.1,pair.1) rfl)
-- Class (b): exact package return on the actual published assignment, with no independent final acceptance field.
theorem historical_package_publication_iff (a : Assignment Owner NativePackageBundle.Value) (cell : Owner) :
    (historicalPackage cell).accept (NativePackageBundle.image a) ↔
      (NativeClosedPackage.package cell false).accept (NativePackageBundle.image a) := by
  unfold ClauseDispatcher.Package.accept
  apply forall_congr'
  intro kind
  cases kind
  case c7 =>
    simp only [historicalPackage,NativeClosedPackage.package,ClauseDispatcher.Rule.accept,JointRules.AssignedAccept,
      historical_decoded,NativeJointCells.decoded,published_historical_data,select,Bool.false_eq_true,ite_false]
  all_goals rfl
-- Class (b): a genuinely accepted published target retains the complete historical package after current source withdrawal.
theorem constructed_withdrawn_package (a : Assignment Owner NativePackageBundle.Value) (cell affected : Owner)
    (accepted : (NativeClosedPackage.package cell false).accept (NativePackageBundle.image a)) :
    (historicalPackage cell).accept (PublicationComposition.cutReceiver affected (NativePackageBundle.image a)) := by
  exact (historical_package_cut_iff affected cell _).mpr ((historical_package_publication_iff a cell).mpr accepted)

-- Class (b): every raw cell remains present or absent after cutting its current receiver flag.
theorem cut_presence (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    (PublicationComposition.cutReceiver affected a cell).isSome=(a cell).isSome := by
  by_cases h : cell=affected
  · simp [PublicationComposition.cutReceiver,h]
  · simp [PublicationComposition.cutReceiver,h]
-- Class (b): actual native execution consumes temporal data, which is unchanged by the live receiver cut.
theorem context_cut (affected cell sourceOwner : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (x : ModeExecution.Registers) :
    (ModeExecution.context cell sourceOwner).eval (nativeInputs (PublicationComposition.cutReceiver affected a)) x ()=
      (ModeExecution.context cell sourceOwner).eval (nativeInputs a) x () := by
  by_cases h : cell=affected
  all_goals cases ha : a cell <;>
    simp [ModeExecution.context,ModeExecution.activeData,ModeExecution.sourceData,ModeExecution.targetData,
      Expr.eval,nativeInputs,PublicationComposition.cutReceiver,h,ha]
-- Class (b): the actual retained withdrawal instructions also ignore the current receiver flag.
theorem withdrawal_cut (affected cell sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value) :
    (ModeExecution.resources cell sourceOwner names).withdrawal.read (nativeInputs (PublicationComposition.cutReceiver affected a))=
      (ModeExecution.resources cell sourceOwner names).withdrawal.read (nativeInputs a) := by
  by_cases h : cell=affected
  all_goals cases ha : a cell <;>
    simp [ModeExecution.resources,CellView.read,nativeInputs,PublicationComposition.cutReceiver,h,ha]
-- Class (b): whole finite rows from the same raw execution are preserved, including missing-input rejection.
theorem runtime_rows_cut (affected cell sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value) (x : ModeExecution.Registers) (d : Unit) (act : Bool) :
    ResourceRuntime.rows (ModeExecution.resources cell sourceOwner names) (nativeInputs (PublicationComposition.cutReceiver affected a)) x d act=
      ResourceRuntime.rows (ModeExecution.resources cell sourceOwner names) (nativeInputs a) x d act := by
  simp only [ResourceRuntime.rows,ModeExecution.resources,ModeExecution.execution,ModeExecution.rowExpr,
    Expr.eval,Expr.reenv_eval,context_cut]
-- Class (b): optional simultaneous native updates agree before totalization for every raw assignment and unbounded state.
theorem runtime_update_expr_cut (affected cell sourceOwner : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (x : ModeExecution.Registers) (d : Unit) (act : Bool) (o : Factor) :
    (ModeExecution.updateExpr cell sourceOwner).eval (nativeInputs (PublicationComposition.cutReceiver affected a)) x (d,act,o)=
      (ModeExecution.updateExpr cell sourceOwner).eval (nativeInputs a) x (d,act,o) := by
  simp only [ModeExecution.updateExpr,Expr.eval,Expr.reenv_eval,context_cut]
-- Class (b): the resource readiness guard is preserved exactly; missing cells cannot be made ready by a receiver cut.
theorem runtime_ready_cut_iff (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    ResourceRuntime.Ready (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected a)) ↔
      ResourceRuntime.Ready (PublicationResources.runtime cell) (nativeInputs a) := by
  rw [PublicationResources.ready_iff,PublicationResources.ready_iff]
  simp only [nativeInputs,Option.isSome_map,cut_presence]
-- Class (b): checked execution agrees for any lawful readiness proofs, and is not defaulted when cells are absent.
theorem runtime_update_cut (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (before : ResourceRuntime.Ready (PublicationResources.runtime cell) (nativeInputs a))
    (after : ResourceRuntime.Ready (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected a)))
    (x : ModeExecution.Registers) (d : Unit) (act : Bool) (o : Factor) :
    ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected a)) after x d act o=
      ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs a) before x d act o := by
  unfold ResourceRuntime.update
  funext reg
  apply Option.some.inj
  rw [←checked_execute_eq _ _ after.2.1 x (d,act,o) reg,
    ←checked_execute_eq _ _ before.2.1 x (d,act,o) reg]
  exact runtime_update_expr_cut affected cell (swapOwner cell) a x d act o
-- Class (b): the actual source-absence and retained-owner/funding/writer conditions survive the receiver cut exactly.
theorem resource_closed_cut_iff (affected cell sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value) (x : ModeExecution.Registers) :
    ResourceRuntime.ResourceClosed (ModeExecution.resourceSchema sourceOwner names) (ModeExecution.resources cell sourceOwner names)
      (nativeInputs (PublicationComposition.cutReceiver affected a)) x ↔
    ResourceRuntime.ResourceClosed (ModeExecution.resourceSchema sourceOwner names) (ModeExecution.resources cell sourceOwner names)
      (nativeInputs a) x := by
  simp only [ResourceRuntime.ResourceClosed,withdrawal_cut]
  simp only [ModeExecution.resources,ModeExecution.stateExpr,Expr.eval,context_cut]

-- Class (b): retained-role withdrawal checks remain exact on all partial raw assignments.
theorem withdrawal_check_cut_iff (affected cell sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value) :
    ResourceRuntime.WithdrawalCheck (ModeExecution.resourceSchema sourceOwner names) (ModeExecution.resources cell sourceOwner names)
      (nativeInputs (PublicationComposition.cutReceiver affected a)) ↔
    ResourceRuntime.WithdrawalCheck (ModeExecution.resourceSchema sourceOwner names) (ModeExecution.resources cell sourceOwner names)
      (nativeInputs a) := by
  simp only [ResourceRuntime.WithdrawalCheck,withdrawal_cut]
-- Class (b): actual resource-factor membership is unchanged without inspecting source presence.
theorem runtime_inside_cut_iff (affected cell sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value) (x : ModeExecution.Registers) :
    ResourceRuntime.Inside (ModeExecution.resourceSchema sourceOwner names) (ModeExecution.resources cell sourceOwner names)
      (nativeInputs (PublicationComposition.cutReceiver affected a)) x ↔
    ResourceRuntime.Inside (ModeExecution.resourceSchema sourceOwner names) (ModeExecution.resources cell sourceOwner names)
      (nativeInputs a) x := by
  simp only [ResourceRuntime.Inside,ModeExecution.resources,ModeExecution.stateExpr,Expr.eval]
-- Class (b): actual legal target debits, credits and retained resources agree after withdrawal, for every partial assignment.
theorem runtime_legal_cut_iff (affected cell sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value) (x : ModeExecution.Registers) (d : Unit) (act : Bool) :
    ResourceRuntime.Legal (ModeExecution.resourceSchema sourceOwner names) (ModeExecution.resources cell sourceOwner names)
      (nativeInputs (PublicationComposition.cutReceiver affected a)) x d act ↔
    ResourceRuntime.Legal (ModeExecution.resourceSchema sourceOwner names) (ModeExecution.resources cell sourceOwner names)
      (nativeInputs a) x d act := by
  simp only [ResourceRuntime.Legal,withdrawal_cut]
  simp only [ModeExecution.resources,ModeExecution.stateExpr,Expr.eval,Expr.reenv_eval,context_cut]
-- Class (b): actual post-update resource solvency and all four positive clock/record advances are preserved.
theorem runtime_step_cut_iff (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (before : ResourceRuntime.Ready (PublicationResources.runtime cell) (nativeInputs a))
    (after : ResourceRuntime.Ready (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected a)))
    (x : ModeExecution.Registers) (d : Unit) (act : Bool) (o : Factor) :
    ResourceRuntime.StepLaw (PublicationResources.cfg cell) (PublicationResources.runtime cell)
      (nativeInputs (PublicationComposition.cutReceiver affected a)) after x d act o ↔
    ResourceRuntime.StepLaw (PublicationResources.cfg cell) (PublicationResources.runtime cell)
      (nativeInputs a) before x d act o := by
  unfold ResourceRuntime.StepLaw
  rw [runtime_update_cut affected cell a before after]
  simp only [PublicationResources.cfg,PublicationResources.runtime,resource_closed_cut_iff]
  simp only [ModeExecution.resources,ModeExecution.stateExpr,Expr.eval,Expr.reenv_eval,context_cut]

-- Class (b): exact agreement of the repaired package with the original when copied/current primitive flags agree.
theorem historical_package_consistent_iff (a : Assignment Owner NativePackageBundle.Value) (cell : Owner)
    (consistent : ∀ pair, a cell=some pair → pair.2.native.receiver.sourcePresent=pair.1.native.receiver.sourcePresent) :
    (historicalPackage cell).accept a ↔ (NativeClosedPackage.package cell false).accept a := by
  unfold ClauseDispatcher.Package.accept
  apply forall_congr'
  intro kind
  cases kind
  case c7 =>
    simp only [historicalPackage,NativeClosedPackage.package,ClauseDispatcher.Rule.accept,JointRules.AssignedAccept,
      historical_decoded,NativeJointCells.decoded]
    have he : (a cell).map historicalData=(a cell).map (fun p => NativeJointCells.data (select false p)) := by
      cases ha : a cell with
      | none => rfl
      | some pair => exact congrArg some (historical_data_consistent pair (consistent pair ha))
    rw [he]
  all_goals rfl
-- Class (b): target-state package predicates consume this same assignment and actual resource factor readout.
def withdrawnPackageAt (b : Assignment Owner NativePackageBundle.Value) (cell : Owner) (x : ModeExecution.Registers) : Prop :=
  (historicalPackage cell).accept b ∧
    ResourceRuntime.Inside (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs b) x
-- Class (b): cut readiness is derived from the original raw guard, not supplied as a final outcome.
def cutReady (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (before : ResourceRuntime.Ready (PublicationResources.runtime cell) (nativeInputs a)) :
    ResourceRuntime.Ready (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected a)) :=
  (runtime_ready_cut_iff affected cell a).mpr before
-- Class (b): actual acquired entries precede withdrawal; target continuation uses the repaired historical package and the SAME raw runtime.
theorem withdrawn_controller_game (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b)
    (cell affected : Owner) (controller : StrategyGame.Strategy ModeExecution.Registers Unit Bool)
    (hw : PublicationComposition.ControllerWins b hb cell controller)
    (consistent : ∀ pair, b cell=some pair → pair.2.native.receiver.sourcePresent=pair.1.native.receiver.sourcePresent) :
    StrategyGame.GameReadout (ResourceRuntime.rows (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b)))
      (ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b))
        (cutReady affected cell b (hb.resources cell))) (PublicationComposition.entries b hb cell)
      (ResourceRuntime.DomainCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell) ∧
        ResourceRuntime.WithdrawalCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell)
          (nativeInputs (PublicationComposition.cutReceiver affected b)))
      (withdrawnPackageAt (PublicationComposition.cutReceiver affected b) cell)
      (ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b)))
      (ResourceRuntime.Legal (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b)))
      (ResourceRuntime.StepLaw (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b))
        (cutReady affected cell b (hb.resources cell))) := by
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
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · exact (historical_package_cut_iff affected cell b).mpr ((historical_package_consistent_iff b cell consistent).mpr pkg.1)
    · exact (runtime_inside_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) b x).mpr pkg.2.1
    · exact (resource_closed_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) b x).mpr closed
    · intro d
      obtain ⟨legal,normalized,step⟩ := laws d
      refine ⟨(runtime_legal_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) b x d _).mpr legal,?_,?_⟩
      · simpa only [roweq] using normalized
      · intro o positive
        have po := positive
        rw [roweq] at po
        exact (runtime_step_cut_iff affected cell b _ _ x d _ o).mpr (step o po)

-- Class (b): all original published canonical cells carry the actual matching source-presence copy.
theorem canonical_history_consistent (cell : Owner) (pair : Bundle × Bundle)
    (hp : NativePackageBundle.canonical cell=some pair) :
    pair.2.native.receiver.sourcePresent=pair.1.native.receiver.sourcePresent := by
  cases cell <;> cases hp <;> rfl
-- Class (b): the actual canonical eight-clause package, with its existing disclosed grades, survives the live receiver cut under the historical binding.
theorem canonical_cut_package (affected cell : Owner) :
    (historicalPackage cell).accept (PublicationComposition.cutReceiver affected NativePackageBundle.canonical) := by
  apply (historical_package_cut_iff affected cell _).mpr
  exact (historical_package_consistent_iff _ cell (canonical_history_consistent cell)).mpr
    (NativeClosedPackage.actual_package cell false)
-- Class (b): complete target continuation after the actual receiver cut, using entries computed before withdrawal.
def PostWithdrawalReadout (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b)
    (affected cell : Owner) : Prop :=
  StrategyGame.GameReadout (ResourceRuntime.rows (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b)))
    (ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b))
      (cutReady affected cell b (hb.resources cell))) (PublicationComposition.entries b hb cell)
    (ResourceRuntime.DomainCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell) ∧
      ResourceRuntime.WithdrawalCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell)
        (nativeInputs (PublicationComposition.cutReceiver affected b)))
    (withdrawnPackageAt (PublicationComposition.cutReceiver affected b) cell)
    (ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b)))
    (ResourceRuntime.Legal (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b)))
    (ResourceRuntime.StepLaw (PublicationResources.cfg cell) (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected b))
      (cutReady affected cell b (hb.resources cell)))
-- Class (b): the actual primitive construction supplies the target continuation game with the same explicit safe controller at both hops.
theorem canonical_cut_readout (affected cell : Owner) :
    PostWithdrawalReadout NativePackageBundle.canonical PublicationComposition.canonical_ready affected cell :=
  withdrawn_controller_game NativePackageBundle.canonical PublicationComposition.canonical_ready cell affected
    PublicationResources.safeController (PublicationComposition.canonical_controller cell) (canonical_history_consistent cell)
-- Class (b): a direct obstruction and constructive return refer to the SAME actual source-withdrawn assignment.
theorem canonical_withdrawal_return (cell : Owner) :
    ¬(NativeClosedPackage.package cell false).accept (PublicationComposition.cutReceiver cell NativePackageBundle.canonical) ∧
    (historicalPackage cell).accept (PublicationComposition.cutReceiver cell NativePackageBundle.canonical) ∧
    PostWithdrawalReadout NativePackageBundle.canonical PublicationComposition.canonical_ready cell cell :=
  ⟨cut_current_package_rejected cell _,canonical_cut_package cell cell,canonical_cut_readout cell cell⟩
-- Class (b): missing cells reject the actual historical package directly and stay missing after the cut.
theorem historical_missing_rejected (affected cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (missing : a cell=none) :
    ¬(historicalPackage cell).accept (PublicationComposition.cutReceiver affected a) := by
  intro accepted
  have before := (historical_package_cut_iff affected cell a).mp accepted
  obtain ⟨data,decoded,_⟩ := before .c7
  rw [historical_decoded,missing] at decoded
  cases decoded

-- Class (b): this actual ablation withdraws copied historical source presence, rather than the current live receiver flag.
def eraseCopiedSource (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) : Assignment Owner NativePackageBundle.Value :=
  fun o => if o=cell then (a o).map (fun pair => (pair.1,NativeJointCells.cutSource pair.2)) else a o
-- Class (b): historical source erasure feeds the actual C7 live-false data, without inserting a rejection verdict.
theorem historical_source_erased_data (pair : Bundle × Bundle) :
    historicalData (pair.1,NativeJointCells.cutSource pair.2)=NativeJointCells.data (NativeJointCells.cutSource pair.1) := rfl
-- Class (b): erasing historical source presence rejects the actual complete historical package on every partial assignment.
theorem historical_source_erased_rejected (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    ¬(historicalPackage cell).accept (eraseCopiedSource cell a) := by
  intro accepted
  obtain ⟨data,decoded,passes⟩ := accepted .c7
  rw [historical_decoded] at decoded
  cases ha : a cell with
  | none => simp [eraseCopiedSource,ha] at decoded
  | some pair =>
    have eq : NativeJointCells.data (NativeJointCells.cutSource pair.1)=data := by
      simpa [eraseCopiedSource,ha,historical_source_erased_data] using decoded
    subst data
    exact NativeJointCells.cut_actual_c7_rejected pair.1 passes
-- Class (b): erase the target's raw joint observable list; historical source presence remains untouched.
def eraseJointRecord (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) : Assignment Owner NativePackageBundle.Value :=
  fun o => if o=cell then (a o).map (fun pair => (NativeJointCells.eraseObservable pair.1,pair.2)) else a o
-- Class (b): the actual two recombination readouts coincide after observable-record erasure, regardless of historical-source flags.
theorem historical_record_erased_displays (pair : Bundle × Bundle) :
    JointRules.receiverDisplay NativeJointCells.schema (historicalData (NativeJointCells.eraseObservable pair.1,pair.2)) false=
      JointRules.receiverDisplay NativeJointCells.schema (historicalData (NativeJointCells.eraseObservable pair.1,pair.2)) true := by
  simp [JointRules.receiverDisplay,JointRules.display,historicalData,NativeJointCells.data,NativeJointCells.eraseObservable]
-- Class (b): actual record erasure directly rejects the complete historical package, rather than merely failing a sufficient certificate.
theorem historical_record_erased_rejected (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    ¬(historicalPackage cell).accept (eraseJointRecord cell a) := by
  intro accepted
  obtain ⟨data,decoded,passes⟩ := accepted .c7
  rw [historical_decoded] at decoded
  cases ha : a cell with
  | none => simp [eraseJointRecord,ha] at decoded
  | some pair =>
    have eq : historicalData (NativeJointCells.eraseObservable pair.1,pair.2)=data := by
      simpa [eraseJointRecord,ha] using decoded
    subst data
    exact JointRules.equal_displays_rejected _ _ (historical_record_erased_displays pair) passes
end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PostWithdrawalPrototype
