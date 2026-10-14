import CSTTT.Fallback.NativeAcquisition

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeAcquiredWithdrawalPrototype
open RegisterInterpreter CSTTT.TransportTheory NativePredictiveBridgePrototype NativePackageBundle
open PostWithdrawalPrototype PostWithdrawalQualifiedPrototype
set_option autoImplicit false
-- The acquisition assignment is primitive pre-cut memory; the receipt is recomputed by the actual acquisition interpreter, never supplied by the caller.
-- Current target memory supplies the prediction recipes and can have its live source receiver withdrawn.
noncomputable def retainedSeedDecision (cell : Owner) (names : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (nativeInputs acquired))
    (history : Factor) (source target : Nat) : Option Bool := do
  let pair ← current cell
  let (original,received,edges) ← NativeAcquisitionSeedPrototype.scientificRead cell acquired ready history source target
  let b := raw cell names (pair.1.native,pair.2.native)
  some (CSTTT.FallbackTheory.ExecutableSeed.pathBit edges source target &&
    decide (CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature b
      (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries b) original=
      CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature b
        (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries b) received))
theorem same_assignment_seed (cell : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (nativeInputs a))
    (history : Factor) (source target : Nat) :
    retainedSeedDecision cell names a a ready history source target=
      NativeAcquisitionSeedPrototype.seedDecision cell names a ready history source target := rfl
-- Withdrawing the current receiver changes no retained acquisition receipt or predictive recipe; the whole optional outcome is preserved.
theorem retained_seed_cut (affected cell : Owner) (names : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (nativeInputs acquired))
    (history : Factor) (source target : Nat) :
    retainedSeedDecision cell names (PublicationComposition.cutReceiver affected current) acquired ready history source target=
      retainedSeedDecision cell names current acquired ready history source target := by
  by_cases same : cell=affected
  · subst cell
    cases hp : current affected with
    | none => simp [retainedSeedDecision,PublicationComposition.cutReceiver,hp]
    | some pair =>
      simp only [retainedSeedDecision,PublicationComposition.cutReceiver,hp,Option.map_some]
      rfl
  · simp [retainedSeedDecision,PublicationComposition.cutReceiver,same]
theorem canonical_retained_seed (affected cell : Owner) (names : Owner → CarrierId) (history : Factor) :
    retainedSeedDecision cell names (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)
      NativePackageBundle.canonical (PublicationReplay.ready cell) history 0 2=some true := by
  rw [retained_seed_cut,same_assignment_seed]
  exact NativeAcquisitionSeedPrototype.canonical_seed_positive cell names history
-- The concrete controller starts at the SAME actually acquired receipt entry; every law uses the actual cut assignment.
theorem canonical_qualified_receipt_play (affected cell : Owner) (history : Factor)
    (receipt : NativeAcquisitionSeedPrototype.Receipt)
    (actual : NativeAcquisitionSeedPrototype.actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=some receipt)
    (x : ModeExecution.Registers) (past : List ModeExecution.Registers)
    (play : StrategyGame.Play
      (ResourceRuntime.rows (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)))
      (ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
        (cutReady affected cell NativePackageBundle.canonical (PublicationResources.ready cell)))
      PublicationResources.safeController receipt.entry (x::past)) :
    qualifiedPackageAt (PublicationComposition.cutReceiver affected NativePackageBundle.canonical) cell x ∧
      ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (PublicationResources.runtime cell)
        (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) x ∧
      ∀ d, ResourceRuntime.Legal (PublicationResources.cfg cell) (PublicationResources.runtime cell)
        (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) x d (PublicationResources.safeController (x::past) d) ∧
        StrategyGame.Normalized (ResourceRuntime.rows (PublicationResources.runtime cell)
          (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) x d (PublicationResources.safeController (x::past) d) ∧
        ∀ o, StrategyGame.PositiveSupport (ResourceRuntime.rows (PublicationResources.runtime cell)
          (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) x d (PublicationResources.safeController (x::past) d) o →
          ResourceRuntime.StepLaw (PublicationResources.cfg cell) (PublicationResources.runtime cell)
            (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
            (cutReady affected cell NativePackageBundle.canonical (PublicationResources.ready cell)) x d (PublicationResources.safeController (x::past) d) o := by
  have roweq : ResourceRuntime.rows (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))=
      ResourceRuntime.rows (PublicationResources.runtime cell) (nativeInputs NativePackageBundle.canonical) := by
    funext y d act
    exact runtime_rows_cut affected cell (swapOwner cell) (PublicationReplay.names cell) NativePackageBundle.canonical y d act
  have upeq : ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
      (cutReady affected cell NativePackageBundle.canonical (PublicationResources.ready cell))=
      ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs NativePackageBundle.canonical) (PublicationResources.ready cell) := by
    funext y d act o
    exact runtime_update_cut affected cell NativePackageBundle.canonical _ _ y d act o
  rw [roweq,upeq] at play
  have he : PublicationComposition.entries NativePackageBundle.canonical PublicationComposition.canonical_ready cell receipt.entry :=
    NativeAcquisitionSeedPrototype.canonical_receipt_entry cell history receipt actual
  obtain ⟨pkg,closed,laws⟩ := (PublicationComposition.canonical_controller cell).2.2 receipt.entry he x past play
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_,?_⟩
  · exact (historical_package_cut_iff affected cell NativePackageBundle.canonical).mpr
      ((historical_package_consistent_iff NativePackageBundle.canonical cell (canonical_history_consistent cell)).mpr pkg.1)
  · exact (runtime_inside_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) NativePackageBundle.canonical x).mpr pkg.2.1
  · exact (nominal_cut_iff affected cell NativePackageBundle.canonical x).mpr
      ((nominal_consistent_iff cell NativePackageBundle.canonical x (canonical_history_consistent cell)).mpr pkg.2.2)
  · exact (resource_closed_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) NativePackageBundle.canonical x).mpr closed
  · intro d
    obtain ⟨legal,normalized,step⟩ := laws d
    refine ⟨(runtime_legal_cut_iff affected cell (swapOwner cell) (PublicationReplay.names cell) NativePackageBundle.canonical x d _).mpr legal,?_,?_⟩
    · simpa only [roweq] using normalized
    · intro o positive
      have po := positive
      rw [roweq] at po
      exact (runtime_step_cut_iff affected cell NativePackageBundle.canonical _ _ x d _ o).mpr (step o po)

-- Current and acquired memory are separately optional raw inputs. Missing current owner or missing actual acquisition readout rejects on every partial assignment.
theorem retained_seed_none_exact (cell : Owner) (names : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (nativeInputs acquired))
    (history : Factor) (source target : Nat) :
    retainedSeedDecision cell names current acquired ready history source target=none ↔
      current cell=none ∨ NativeAcquisitionSeedPrototype.scientificRead cell acquired ready history source target=none := by
  cases hp : current cell with
  | none => simp [retainedSeedDecision,hp]
  | some pair =>
    cases hr : NativeAcquisitionSeedPrototype.scientificRead cell acquired ready history source target with
    | none => simp [retainedSeedDecision,hp,hr]
    | some value => obtain ⟨original,received,edges⟩ := value; simp [retainedSeedDecision,hp,hr]
-- This predicate spells out the SAME selected controller and complete laws; it has no supplied success bit.
def ContinuationLaw (affected cell : Owner) (entry : ModeExecution.Registers) : Prop :=
    ∀ x past, StrategyGame.Play
      (ResourceRuntime.rows (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)))
      (ResourceRuntime.update (PublicationResources.runtime cell) (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
        (cutReady affected cell NativePackageBundle.canonical (PublicationResources.ready cell)))
      PublicationResources.safeController entry (x::past) →
    qualifiedPackageAt (PublicationComposition.cutReceiver affected NativePackageBundle.canonical) cell x ∧
      ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (PublicationResources.runtime cell)
        (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) x ∧
      ∀ d, ResourceRuntime.Legal (PublicationResources.cfg cell) (PublicationResources.runtime cell)
        (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) x d (PublicationResources.safeController (x::past) d) ∧
        StrategyGame.Normalized (ResourceRuntime.rows (PublicationResources.runtime cell)
          (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) x d (PublicationResources.safeController (x::past) d) ∧
        ∀ o, StrategyGame.PositiveSupport (ResourceRuntime.rows (PublicationResources.runtime cell)
          (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) x d (PublicationResources.safeController (x::past) d) o →
          ResourceRuntime.StepLaw (PublicationResources.cfg cell) (PublicationResources.runtime cell)
            (nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
            (cutReady affected cell NativePackageBundle.canonical (PublicationResources.ready cell)) x d (PublicationResources.safeController (x::past) d) o
-- Constructive return on the same actual receipt: retained predictive Seed, exact actual path/full prediction, and target-owned qualified resource continuation.
theorem canonical_acquired_withdrawal_return (affected cell : Owner) (names : Owner → CarrierId) (history : Factor) :
    ∃ receipt, NativeAcquisitionSeedPrototype.actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=some receipt ∧
      retainedSeedDecision cell names (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)
        NativePackageBundle.canonical (PublicationReplay.ready cell) history 0 2=some true ∧
      CSTTT.FallbackTheory.OperationalTrace.Path receipt.edges 0 2 ∧
      (∀ query, sourceFuture (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native)) (receipt.initial ()).1.factor query=
        targetFuture (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native)) (receipt.entry ()).1.factor query) ∧
      PublicationResources.entries cell receipt.entry ∧ ContinuationLaw affected cell receipt.entry := by
  obtain ⟨receipt,actual,path,future⟩ := NativeAcquisitionSeedPrototype.canonical_seed_actual_full cell names history 0 2
    (NativeAcquisitionSeedPrototype.canonical_seed_positive cell names history)
  refine ⟨receipt,actual,canonical_retained_seed affected cell names history,path,future,
    NativeAcquisitionSeedPrototype.canonical_receipt_entry cell history receipt actual,?_⟩
  intro x past play
  exact canonical_qualified_receipt_play affected cell history receipt actual x past play
-- The positive historical return does not revive the directly false original current-source package/nominal gates.
theorem original_current_gates_rejected_with_return (cell : Owner) (names : Owner → CarrierId) (history : Factor) :
    ¬(NativeClosedPackage.package cell false).accept (PublicationComposition.cutReceiver cell NativePackageBundle.canonical) ∧
    ¬PublicationNominal.PassAt cell (nativeInputs (PublicationComposition.cutReceiver cell NativePackageBundle.canonical))
      (PublicationPhysical.entryRun cell history) ∧
    ∃ receipt, NativeAcquisitionSeedPrototype.actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=some receipt ∧
      retainedSeedDecision cell names (PublicationComposition.cutReceiver cell NativePackageBundle.canonical)
        NativePackageBundle.canonical (PublicationReplay.ready cell) history 0 2=some true ∧ ContinuationLaw cell cell receipt.entry := by
  refine ⟨cut_current_package_rejected cell _,original_nominal_cut_rejected cell _ _,?_⟩
  obtain ⟨receipt,actual,seed,_,_,_,continuation⟩ := canonical_acquired_withdrawal_return cell cell names history
  exact ⟨receipt,actual,seed,continuation⟩
-- Timing and ownership belong to the same receipt whose target continues after withdrawal.
theorem acquired_withdrawal_physical_return (affected cell : Owner) (names : Owner → CarrierId) (history : Factor) :
    ∃ receipt, NativeAcquisitionSeedPrototype.actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=some receipt ∧
      retainedSeedDecision cell names (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)
        NativePackageBundle.canonical (PublicationReplay.ready cell) history 0 2=some true ∧
      (receipt.terminal ()).1.counter=PublicationReplay.start cell+(PublicationReplay.jump cell-1) ∧
      (receipt.entry ()).1.counter=PublicationReplay.start cell+PublicationReplay.jump cell ∧
      (PublicationPhysical.ownerExpr cell).eval PublicationResources.assignment receipt.terminal ()=some (PublicationReplay.names cell (swapOwner cell)) ∧
      (PublicationPhysical.ownerExpr cell).eval PublicationResources.assignment receipt.entry ()=some (PublicationReplay.names cell cell) ∧
      ContinuationLaw affected cell receipt.entry := by
  obtain ⟨receipt,actual,seed,_,_,_,continuation⟩ := canonical_acquired_withdrawal_return affected cell names history
  obtain ⟨terminalTime,entryTime,terminalOwner,entryOwner⟩ := NativeAcquisitionSeedPrototype.canonical_receipt_physical cell history receipt actual
  exact ⟨receipt,actual,seed,terminalTime,entryTime,terminalOwner,entryOwner,continuation⟩
end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeAcquiredWithdrawalPrototype
