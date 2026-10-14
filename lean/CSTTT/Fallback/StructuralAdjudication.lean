import CSTTT.Fallback.ReconstructionRoles
import CSTTT.Fallback.BranchIdentity
import CSTTT.Fallback.IdentityUnderdetermination
import CSTTT.Fallback.PackageIndependence

/-! Exact structural landings for TTF-06/07/08. The original target-as-source
and arbitrary-identity schemas are retained and refuted, not silently proved.
Physical package upgrades and independent sibling financing remain separate. -/
namespace CSTTT.FallbackTheory.StructuralAdjudication
open CSTTT.TransportTheory CSTTT.FallbackTheory.RawPredictiveQuotient
open CSTTT.FallbackTheory.OperationalTrace CSTTT.FallbackTheory.SharedOperationalSeed
open CSTTT.FallbackTheory.ReconstructionRolesPrototype
open CSTTT.FallbackTheory.IdentityUnderdeterminationPrototype
open CSTTT.TargetTheory.GenericHandoff
open CSTTT.TargetTheory.GenericHandoff.NativeComposition
open NativeReceiptExtensionPrototype NativeTwoHopReceiptPrototype NativeSafeClosurePrototype
set_option autoImplicit false

-- The historical source has its own coordinate; structural equality compares
-- targets. This repairs the direction error in the original TTF-06 schema.
def RootedReconstructionTwinSeparation (Source Target : Type)
    (sameStructure : Target → Target → Prop) (ancestral : Source → Target → Prop) : Prop :=
  ∃ source reconstruction twin,
    sameStructure reconstruction twin ∧ ancestral source reconstruction ∧ ¬ancestral source twin

theorem rooted_twin_exact {H S T E R SC TC RR M : Type} [DecidableEq S] [DecidableEq T]
    (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (program : Option (GuardedFusion.Program T)) (credits : Option GuardedFusion.Credits)
    (source reconstruction twin : Nat) :
    RootedTwinSeparation b inputs program credits source reconstruction twin ↔
      SameActualTargets b inputs program credits reconstruction twin ∧
      GuardedFusion.actualAncestry b inputs [] program credits [] source reconstruction=some true ∧
      (GuardedFusion.actualRun b inputs [] program credits []).isSome=true ∧
      GuardedFusion.actualAncestry b inputs [] program credits [] source twin≠some true := by
  constructor
  · rintro ⟨same,positive,negative⟩
    have available := (GuardedFusion.actual_ancestry_false_iff _ _ _ _ _ _ _ _).mp negative
    refine ⟨same,positive,available.1,?_⟩
    rw [negative]; decide
  · rintro ⟨same,positive,available,negative⟩
    refine ⟨same,positive,?_⟩
    cases h : GuardedFusion.actualAncestry b inputs [] program credits [] source twin with
    | none =>
      have missing := (GuardedFusion.actual_ancestry_none_iff _ _ _ _ _ _ _ _).mp h
      rw [missing] at available
      cases available
    | some value => cases value <;> simp_all

-- A real checked snapshot/erase/gap/reconstruction execution supplies both
-- the typed repair and a direct refutation of the old schema on the SAME data.
theorem destructive_reconstruction_return {H S T E R SC TC RR M : Type}
    [DecidableEq S] [DecidableEq T]
    (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (program : GuardedFusion.Program T) (credits : GuardedFusion.Credits)
    (source record target twin duration maxAge : Nat) (payload : S)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge) :
    RootedReconstructionTwinSeparation Nat Nat
      (SameActualTargets b (rawInputs b source record target twin duration maxAge payload) (some program) (some credits))
      (fun root endpoint => GuardedFusion.actualAncestry b
        (rawInputs b source record target twin duration maxAge payload) [] (some program) (some credits) [] root endpoint=some true) ∧
    (∀ sourceDerived, ¬CSTTT.Prospects.DestructiveReconstructionTwinSeparation Nat
      (SameActualTargets b (rawInputs b source record target twin duration maxAge payload) (some program) (some credits))
      sourceDerived (fun root endpoint => GuardedFusion.actualAncestry b
        (rawInputs b source record target twin duration maxAge payload) [] (some program) (some credits) [] root endpoint=some true)) ∧
    ∃ world, GuardedFusion.actualRun b (rawInputs b source record target twin duration maxAge payload)
      [] (some program) (some credits) []=some world ∧
      world.store.active source=false ∧ world.store.read source=some (.source payload) ∧
      world.store.read record=some (.record source 1 payload) ∧
      world.store.read target=world.store.read twin ∧ world.store.active target=true ∧ world.store.active twin=true ∧
      (∀ query,targetFuture b (b.mapState payload) query=sourceFuture b payload query) := by
  obtain ⟨separation,execution⟩ := repaired_constructive_return b laws program credits
    source record target twin duration maxAge payload sr st sw rt rw tw age
  refine ⟨⟨source,target,twin,separation.1,separation.2.1,?_⟩,
    fun sourceDerived => original_schema_refuted b _ _ _ sourceDerived,execution⟩
  dsimp only
  rw [separation.2.2]; decide

-- Logical underdetermination of full equivalence relations, rather than a
-- pointwise negative for an arbitrary externally supplied identity predicate.
def IdentityUnderdetermined (ancestry : Nat → Nat → Prop) (source left right : Nat) : Prop :=
  left≠right ∧ ∃ i j : Nat → Nat → Prop,
    Compatible ancestry source i ∧ Compatible ancestry source j ∧ i≠j ∧
    i source left ∧ ¬i source right ∧ j source right ∧ ¬j source left ∧
    ¬(∀ q,Compatible ancestry source q → q source left) ∧
    ¬(∀ q,Compatible ancestry source q → q source right)

theorem branching_identity_underdetermined (ancestry : Nat → Nat → Prop) (source left right : Nat)
    (hl : ancestry source left) (hr : ancestry source right)
    (ls : left≠source) (rs : right≠source) (lr : left≠right) :
    IdentityUnderdetermined ancestry source left right := by
  obtain ⟨lc,rc,ll,ln,rr,rn,different⟩ := two_identity_extensions ancestry source left right hl hr ls rs lr
  exact ⟨lr,NumericalIdentity source left,NumericalIdentity source right,
    lc,rc,different,ll,ln,rr,rn,fun forced => rn (forced _ rc),fun forced => ln (forced _ lc)⟩

theorem compatible_invariant_excludes_both (ancestry identity : Nat → Nat → Prop)
    (source left right : Nat) (ls : left≠source) (rs : right≠source) (lr : left≠right)
    (compatible : Compatible ancestry source identity)
    (invariant : identity source left ↔ identity source right) :
    ¬identity source left ∧ ¬identity source right := by
  exact ⟨fun h => lr (compatible.2.2 left right ls rs h (invariant.mp h)),
    fun h => lr (compatible.2.2 left right ls rs (invariant.mpr h) h)⟩

-- No identity interpretation enters the actual execution. Both branches copy
-- the complete same state for EVERY finite continuation length.
theorem actual_branch_identity_return (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (history : Factor) (length : Nat) :
    ∃ commands finished state,
      SafeCommands commands ∧ commands.length=length+1 ∧
      extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
        history commands=some finished ∧
      finished.read (5+length)=some state ∧ finished.read (6+length)=some state ∧
      PostWithdrawalQualifiedPrototype.qualifiedPackageAt (withdrawnCurrent affected) false state ∧
      NativeAcquiredWithdrawalPrototype.ContinuationLaw affected false state ∧
      IdentityUnderdetermined
        (fun source endpoint => ancestryDecision leftNames rightNames (withdrawnCurrent affected)
          NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected) history commands source endpoint=some true)
        0 (5+length) (6+length) := by
  obtain ⟨commands,finished,state,safe,size,execution,leftRead,rightRead,hl,hr,package,law⟩ :=
    canonical_arbitrary_length_fission affected leftNames rightNames history length
  exact ⟨commands,finished,state,safe,size,execution,leftRead,rightRead,package,law,
    branching_identity_underdetermined _ 0 _ _ hl hr (by omega) (by omega) (by omega)⟩

-- The arbitrary-identity formulation is false even on the same actual native
-- branching model. It cannot serve as a universal formulation of TTF-07.
theorem original_identity_schema_rejected (ancestry : Nat → Nat → Prop) (swap : Nat → Nat) :
    ¬CSTTT.Prospects.AncestryNoUniqueIdentity Nat Nat ancestry (fun _ _ => True) swap :=
  BranchSymmetryPrototype.total_identity_refutes_original ancestry swap

-- This landing uses the original TTF-08 schema unchanged, with the complete
-- repaired historical package, not an arbitrary supplied package predicate.
theorem actual_package_ablation_control (affected : Owner) :
    (PostWithdrawalPrototype.historicalPackage false).accept
      (PublicationComposition.cutReceiver affected NativePackageBundle.canonical) ∧
    NativePackageBundle.nativeInputs
      (NativePackageIndependencePrototype.ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))=
      NativePackageBundle.nativeInputs (PublicationComposition.cutReceiver affected NativePackageBundle.canonical) ∧
    ¬(PostWithdrawalPrototype.historicalPackage false).accept
      (NativePackageIndependencePrototype.ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)) :=
  ⟨PostWithdrawalPrototype.canonical_cut_package affected false,
    NativePackageIndependencePrototype.native_inputs_unchanged false _,
    NativePackageIndependencePrototype.historical_package_rejected false _⟩

theorem actual_package_insufficiency_return (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (history : Factor) :
    CSTTT.Prospects.PredictiveAncestryPackageInsufficient Factor
      (fun h => retainedDecision leftNames rightNames
        (NativePackageIndependencePrototype.ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
        NativePackageBundle.canonical PublicationReplay.ready h 0 4=some true)
      (fun _ => (PostWithdrawalPrototype.historicalPackage false).accept
        (NativePackageIndependencePrototype.ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) :=
  NativePackageIndependencePrototype.historical_package_schema affected leftNames rightNames history

theorem no_actual_ancestry_package_implication (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (history : Factor) :
    ¬(∀ h, retainedDecision leftNames rightNames
      (NativePackageIndependencePrototype.ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))
      NativePackageBundle.canonical PublicationReplay.ready h 0 4=some true →
      (PostWithdrawalPrototype.historicalPackage false).accept
        (NativePackageIndependencePrototype.ablate false (PublicationComposition.cutReceiver affected NativePackageBundle.canonical))) := by
  obtain ⟨h,ancestry,rejected⟩ := actual_package_insufficiency_return affected leftNames rightNames history
  exact fun implication => rejected (implication h ancestry)

end CSTTT.FallbackTheory.StructuralAdjudication
