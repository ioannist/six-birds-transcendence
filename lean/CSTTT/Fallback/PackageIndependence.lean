import CSTTT.Fallback.TemporalIAPS

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackageIndependencePrototype
open RegisterInterpreter NativePackageBundle NativePredictiveBridgePrototype NativeAcquisitionSeedPrototype
open PostWithdrawalPrototype PostWithdrawalQualifiedPrototype
set_option autoImplicit false
-- Reuse the already committed primitive generator-edge ablation. Only the current supplementary C5 instructions change.
def ablate (cell : Owner) (current : Assignment Owner NativePackageBundle.Value) : Assignment Owner NativePackageBundle.Value :=
  NativeClosedPackage.mapCurrent NativeCreditCells.cutSelfEdges cell current
-- EVERY actual native recipe (rows/classes/history/resources/receiver/interpreter) is unchanged, including absent cells.
theorem native_inputs_unchanged (cell : Owner) (current : Assignment Owner NativePackageBundle.Value) :
    nativeInputs (ablate cell current)=nativeInputs current := by
  funext owner
  by_cases same : owner=cell
  · simp only [nativeInputs,ablate,NativeClosedPackage.mapCurrent,same,ite_true,Option.map_map]
    rfl
  · simp [nativeInputs,ablate,NativeClosedPackage.mapCurrent,same]
-- Exact whole GLOBAL optional ancestry decision invariance on all current/acquired assignments and endpoint queries.
theorem retained_decision_unchanged (cell : Owner) (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ o, AcquisitionExecution.Ready (PublicationReplay.raw o) (nativeInputs acquired))
    (history : Factor) (source target : Nat) :
    NativeTwoHopReceiptPrototype.retainedDecision leftNames rightNames (ablate cell current) acquired ready history source target=
      NativeTwoHopReceiptPrototype.retainedDecision leftNames rightNames current acquired ready history source target := by
  cases hl : current true with
  | none => cases cell <;> simp [NativeTwoHopReceiptPrototype.retainedDecision,ablate,NativeClosedPackage.mapCurrent,hl]
  | some left =>
    cases hr : current false with
    | none => cases cell <;> simp [NativeTwoHopReceiptPrototype.retainedDecision,ablate,NativeClosedPackage.mapCurrent,hl,hr]
    | some right =>
      cases cell <;> simp only [NativeTwoHopReceiptPrototype.retainedDecision,ablate,NativeClosedPackage.mapCurrent,hl,hr,
        if_true,if_false,Bool.false_eq_true,Bool.true_eq_false,Option.map_some,bind,Option.bind_some] <;> rfl
-- Actual C5 decoding rejects the ablated self-cycle on EVERY partial raw assignment; no final checker bit is deleted or supplied.
theorem ablated_c5_rejected (cell : Owner) (current : Assignment Owner NativePackageBundle.Value) :
    ¬ProtocolCreditRules.AssignedAccept (NativeCreditCells.schema (AvailabilityPublication.dataOwner cell false))
      (NativeCreditCells.bindings cell false) (ablate cell current) := by
  rw [NativeCreditCells.acceptance_iff]
  cases hc : current cell with
  | none => simp [ablate,NativeClosedPackage.mapCurrent,hc]
  | some pair =>
    simp only [ablate,NativeClosedPackage.mapCurrent,ite_true,hc,Option.map_some,Option.some.injEq]
    rintro ⟨p,eq,accepted⟩
    cases eq
    exact NativeCreditCells.cut_actual_c5_rejected _ pair.1 accepted
-- Whole HISTORICAL package acceptance fails directly through its unchanged C5 clause, so historical-source C7 repair cannot hide this independent obstruction.
theorem historical_package_rejected (cell : Owner) (current : Assignment Owner NativePackageBundle.Value) :
    ¬(historicalPackage cell).accept (ablate cell current) := by
  intro package
  have c5 := package ClauseDispatcher.Kind.c5
  exact ablated_c5_rejected cell current c5
theorem qualified_package_rejected (cell : Owner) (current : Assignment Owner NativePackageBundle.Value) (x : ModeExecution.Registers) :
    ¬qualifiedPackageAt (ablate cell current) cell x := by
  intro accepted
  exact historical_package_rejected cell current accepted.1.1
-- On the SAME receiver cut/current assignment, ancestry remains actualSomeTrue while the COMPLETE historical package is false.
theorem actual_historical_package_split (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor) :
    NativeTwoHopReceiptPrototype.retainedDecision leftNames rightNames
      (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
      NativePackageBundle.canonical PublicationReplay.ready history 0 4=some true ∧
    ¬(historicalPackage false).accept (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) ∧
    (∀ x, ¬qualifiedPackageAt (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) false x) := by
  refine ⟨?_,historical_package_rejected _ _,fun x => qualified_package_rejected _ _ x⟩
  rw [retained_decision_unchanged,NativeTwoHopReceiptPrototype.combined_decision_cut]
  exact NativeTwoHopReceiptPrototype.canonical_combined_positive leftNames rightNames history
-- Exact stronger TTF08 schema uses the repaired historical package itself, on an independent actual raw C5 ablation.
theorem historical_package_schema (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor) :
    CSTTT.Prospects.PredictiveAncestryPackageInsufficient Factor
      (fun h => NativeTwoHopReceiptPrototype.retainedDecision leftNames rightNames
        (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
        NativePackageBundle.canonical PublicationReplay.ready h 0 4=some true)
      (fun _ => (historicalPackage false).accept (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) := by
  have split := actual_historical_package_split affected leftNames rightNames history
  exact ⟨history,split.1,split.2.1⟩

-- Raw resource readiness is transported only through the proved exact native-input equality, not a supplied continuation verdict.
def resourceReady (affected : Owner) : ResourceRuntime.Ready (PublicationResources.runtime false)
    (nativeInputs (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) := by
  rw [native_inputs_unchanged]
  exact cutReady affected false NativePackageBundle.canonical (PublicationResources.ready false)
def ResourceContinuation (affected : Owner) (entry : ModeExecution.Registers) : Prop :=
  ∀ x past, StrategyGame.Play
    (ResourceRuntime.rows (PublicationResources.runtime false) (nativeInputs (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))))
    (ResourceRuntime.update (PublicationResources.runtime false) (nativeInputs (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) (resourceReady affected))
    PublicationResources.safeController entry (x::past) →
    ResourceRuntime.ResourceClosed (PublicationResources.cfg false) (PublicationResources.runtime false)
      (nativeInputs (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) x ∧
    ∀ d, ResourceRuntime.Legal (PublicationResources.cfg false) (PublicationResources.runtime false)
      (nativeInputs (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) x d (PublicationResources.safeController (x::past) d) ∧
    StrategyGame.Normalized (ResourceRuntime.rows (PublicationResources.runtime false)
      (nativeInputs (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)))) x d (PublicationResources.safeController (x::past) d) ∧
    ∀ o, StrategyGame.PositiveSupport (ResourceRuntime.rows (PublicationResources.runtime false)
      (nativeInputs (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)))) x d (PublicationResources.safeController (x::past) d) o →
      ResourceRuntime.StepLaw (PublicationResources.cfg false) (PublicationResources.runtime false)
        (nativeInputs (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) (resourceReady affected) x d
        (PublicationResources.safeController (x::past) d) o
-- The SAME actual safe controller retains all native resource laws after the independent C5 graph ablation.
theorem resources_retained (affected : Owner) (entry : ModeExecution.Registers)
    (original : NativeAcquiredWithdrawalPrototype.ContinuationLaw affected false entry) : ResourceContinuation affected entry := by
  have transport : ∀ a b (ha : ResourceRuntime.Ready (PublicationResources.runtime false) a)
      (hb : ResourceRuntime.Ready (PublicationResources.runtime false) b), a=b →
      ResourceRuntime.update (PublicationResources.runtime false) a ha=ResourceRuntime.update (PublicationResources.runtime false) b hb := by
    intro a b ha hb equal
    cases equal
    rfl
  have updater := transport _ _ (resourceReady affected) (cutReady affected false NativePackageBundle.canonical (PublicationResources.ready false))
    (native_inputs_unchanged false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
  intro x past play
  have actualPlay : StrategyGame.Play
    (ResourceRuntime.rows (PublicationResources.runtime false) (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)))
    (ResourceRuntime.update (PublicationResources.runtime false) (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
      (cutReady affected false NativePackageBundle.canonical (PublicationResources.ready false)))
    PublicationResources.safeController entry (x::past) := by
    rw [updater,native_inputs_unchanged] at play
    exact play
  have laws := original x past actualPlay
  simpa only [ResourceRuntime.StepLaw,updater,native_inputs_unchanged] using laws.2
-- Stronger honest return: ancestry AND same-entry resource autonomy remain positive while the WHOLE repaired historical package is directly false.
theorem independent_package_return (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor) :
    ∃ pair, NativeTwoHopReceiptPrototype.execute NativePackageBundle.canonical PublicationReplay.ready history=some pair ∧
      NativeTwoHopReceiptPrototype.retainedDecision leftNames rightNames
        (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) NativePackageBundle.canonical PublicationReplay.ready history 0 4=some true ∧
      CSTTT.FallbackTheory.OperationalTrace.Path pair.edges 0 4 ∧ PublicationResources.entries false pair.right.entry ∧
      ResourceContinuation affected pair.right.entry ∧
      ¬(historicalPackage false).accept (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) ∧
      ¬qualifiedPackageAt (ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) false pair.right.entry := by
  obtain ⟨pair,actual,seed,path,_,_,entry,continuation⟩ := NativeTwoHopReceiptPrototype.combined_withdrawal_return affected leftNames rightNames history
  refine ⟨pair,actual,?_,path,entry,resources_retained affected pair.right.entry continuation,historical_package_rejected _ _,qualified_package_rejected _ _ _⟩
  rw [retained_decision_unchanged]
  exact seed
end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackageIndependencePrototype
