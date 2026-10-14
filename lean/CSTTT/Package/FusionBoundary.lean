import CSTTT.Package.FiniteGluing

namespace CSTTT.PackageTheory

/-- A many-to-one lineage premise is separately typed from target-package realization. -/
structure FusionBoundaryData where
  leftLineage : Prop
  rightLineage : Prop
  distinctSources : Prop
  commonTarget : Prop
  branchwisePreserved : Prop
  actionCreditCoherent : Prop
  recombinationPreserved : Prop
  integratedTargetPackage : Prop

/-- The finite obstruction exposes both a credit failure and a recombination failure. -/
structure FusionBoundaryCertificate (d : FusionBoundaryData) where
  leftLineage : d.leftLineage
  rightLineage : d.rightLineage
  distinctSources : d.distinctSources
  commonTarget : d.commonTarget
  branchwisePreserved : d.branchwisePreserved
  actionCreditConflict : ¬ d.actionCreditCoherent
  recombinationFailure : ¬ d.recombinationPreserved
  packageFailure : ¬ d.integratedTargetPackage

/-- Process merger can be witnessed while the independently audited target package fails. -/
theorem fusionLineageDoesNotImplyIntegratedPackage
    {d : FusionBoundaryData}
    (cert : FusionBoundaryCertificate d) :
    d.leftLineage ∧ d.rightLineage ∧ d.branchwisePreserved ∧ ¬ d.integratedTargetPackage := by
  exact ⟨cert.leftLineage, cert.rightLineage, cert.branchwisePreserved, cert.packageFailure⟩

/-- Branchwise preservation cannot repair a missing joint recombination relation. -/
theorem fusionBranchwiseDoesNotRepairRecombination
    {d : FusionBoundaryData}
    (cert : FusionBoundaryCertificate d) :
    d.branchwisePreserved ∧ ¬ d.recombinationPreserved := by
  exact ⟨cert.branchwisePreserved, cert.recombinationFailure⟩

end CSTTT.PackageTheory
