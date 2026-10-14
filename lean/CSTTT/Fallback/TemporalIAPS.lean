import CSTTT.Fallback.NativeReceiptComposition

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeIAPSLandingPrototype
open RegisterInterpreter NativePredictiveBridgePrototype NativeAcquisitionSeedPrototype NativeAcquiredWithdrawalPrototype
open PostWithdrawalPrototype PostWithdrawalQualifiedPrototype CSTTT.TransportTheory
set_option autoImplicit false
-- A certificate contains only the chosen primitive receiver-cut owner and history identifier. All executions/readouts are computed from the same released RAW canonical package.
abbrev Cert := Owner × Factor
def Valid (c : Cert) : Prop :=
  (NativeTwoHopReceiptPrototype.execute NativePackageBundle.canonical PublicationReplay.ready c.2).isSome=true
def Ancestry (c : Cert) : Prop :=
  NativeTwoHopReceiptPrototype.retainedDecision (PublicationReplay.names true) (PublicationReplay.names false)
    (PublicationComposition.cutReceiver c.1 NativePackageBundle.canonical) NativePackageBundle.canonical PublicationReplay.ready c.2 0 4=some true ∧
  ∃ pair, NativeTwoHopReceiptPrototype.execute NativePackageBundle.canonical PublicationReplay.ready c.2=some pair ∧
    CSTTT.FallbackTheory.OperationalTrace.Path pair.edges 0 4 ∧ pair.left.entry=pair.right.initial ∧
    ∀ query, sourceFuture (raw true (PublicationReplay.names true) ((canonicalPair true).1.native,(canonicalPair true).2.native))
      (pair.left.initial ()).1.factor query=
      targetFuture (raw false (PublicationReplay.names false) ((canonicalPair false).1.native,(canonicalPair false).2.native))
        (pair.right.entry ()).1.factor query
def PackageRealized (c : Cert) : Prop :=
  ∃ pair, NativeTwoHopReceiptPrototype.execute NativePackageBundle.canonical PublicationReplay.ready c.2=some pair ∧
    PublicationResources.entries false pair.right.entry ∧
    ∀ x past, StrategyGame.Play
      (ResourceRuntime.rows (PublicationResources.runtime false) (NativePackageBundle.nativeInputs (PublicationComposition.cutReceiver c.1 NativePackageBundle.canonical)))
      (ResourceRuntime.update (PublicationResources.runtime false) (NativePackageBundle.nativeInputs (PublicationComposition.cutReceiver c.1 NativePackageBundle.canonical))
        (cutReady c.1 false NativePackageBundle.canonical (PublicationResources.ready false)))
      PublicationResources.safeController pair.right.entry (x::past) →
    qualifiedPackageAt (PublicationComposition.cutReceiver c.1 NativePackageBundle.canonical) false x
def Autonomous (c : Cert) : Prop :=
  ∃ pair, NativeTwoHopReceiptPrototype.execute NativePackageBundle.canonical PublicationReplay.ready c.2=some pair ∧
    ContinuationLaw c.1 false pair.right.entry
-- Validity is actual execution availability, not a stored ancestry/package/autonomy conjunction.
theorem valid_every_primitive_request (c : Cert) : Valid c := by
  simp only [Valid,NativeTwoHopReceiptPrototype.canonical_two_hop,Option.isSome_some]
-- The SAME computed pair simultaneously returns all three independent lane readouts.
theorem all_lanes_from_raw (c : Cert) : Ancestry c ∧ PackageRealized c ∧ Autonomous c := by
  obtain ⟨pair,actual,seed,path,middle,future,entry,continuation⟩ :=
    NativeTwoHopReceiptPrototype.combined_withdrawal_return c.1 (PublicationReplay.names true) (PublicationReplay.names false) c.2
  refine ⟨⟨seed,pair,actual,path,middle,future⟩,⟨pair,actual,entry,?_⟩,⟨pair,actual,continuation⟩⟩
  intro x past play
  exact (continuation x past play).1
-- Exact return to the original typed TTF-05 schema, with the historical package qualification explicitly represented.
theorem integrated_schema : CSTTT.Prospects.IntegratedTemporalIAPS Cert Valid Ancestry PackageRealized Autonomous := by
  intro c _valid
  exact all_lanes_from_raw c
-- Existence of an actual initial supported play exposes package/resource content; the controller result cannot be vacuous.
theorem same_entry_initial_content (c : Cert) :
    ∃ pair, NativeTwoHopReceiptPrototype.execute NativePackageBundle.canonical PublicationReplay.ready c.2=some pair ∧
      qualifiedPackageAt (PublicationComposition.cutReceiver c.1 NativePackageBundle.canonical) false pair.right.entry ∧
      ResourceRuntime.ResourceClosed (PublicationResources.cfg false) (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs (PublicationComposition.cutReceiver c.1 NativePackageBundle.canonical)) pair.right.entry := by
  obtain ⟨pair,actual,_,_,_,_,_,continuation⟩ :=
    NativeTwoHopReceiptPrototype.combined_withdrawal_return c.1 (PublicationReplay.names true) (PublicationReplay.names false) c.2
  have initial := continuation pair.right.entry [] StrategyGame.Play.initial
  exact ⟨pair,actual,initial.1,initial.2.1⟩
-- Use actual computed predictive ancestry and the actual original full current-source target package as the two predicates of TTF-08.
def CurrentPackage (c : Cert) : Prop :=
  (NativeClosedPackage.package false false).accept (PublicationComposition.cutReceiver c.1 NativePackageBundle.canonical)
theorem final_cut_original_package_rejected (history : Factor) : ¬CurrentPackage (false,history) :=
  cut_current_package_rejected false NativePackageBundle.canonical
theorem actual_ancestry_package_split (history : Factor) : Ancestry (false,history) ∧ ¬CurrentPackage (false,history) :=
  ⟨(all_lanes_from_raw (false,history)).1,final_cut_original_package_rejected history⟩
theorem predictive_package_schema (history : Factor) :
    CSTTT.Prospects.PredictiveAncestryPackageInsufficient Cert Ancestry CurrentPackage :=
  ⟨(false,history),actual_ancestry_package_split history⟩
-- The no-go is direct failure of the actual package readout, rather than deletion of a sufficient checker.
theorem ancestry_does_not_imply_current_package : ¬(∀ c : Cert, Ancestry c → CurrentPackage c) := by
  intro purported
  have split := actual_ancestry_package_split (false,false,false)
  exact split.2 (purported (false,(false,false,false)) split.1)
end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeIAPSLandingPrototype
