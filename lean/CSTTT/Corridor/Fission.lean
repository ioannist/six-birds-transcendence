import CSTTT.Core.Finite

namespace CSTTT.CorridorTheory

/-- A relation-valued fork records both branches and an explicit target symmetry. -/
structure TemporalFissionData (Source Target : Type) where
  source : Source
  left : Target
  right : Target
  related : Source → Target → Prop
  valid : Target → Prop
  swap : Target → Target

/-- Audited evidence for one symmetric temporal fission. -/
structure TemporalFissionCertificate
    {Source Target : Type}
    (d : TemporalFissionData Source Target) where
  targetsDistinct : d.left ≠ d.right
  leftRelated : d.related d.source d.left
  rightRelated : d.related d.source d.right
  leftValid : d.valid d.left
  rightValid : d.valid d.right
  swapLeft : d.swap d.left = d.right
  swapRight : d.swap d.right = d.left

/-- TTH-08 / PTH-07: the lineage output is the two-valued relation, not a selected singleton. -/
theorem relationValuedTemporalFission
    {Source Target : Type}
    {d : TemporalFissionData Source Target}
    (cert : TemporalFissionCertificate d) :
    d.related d.source d.left ∧ d.related d.source d.right := by
  exact ⟨cert.leftRelated, cert.rightRelated⟩

/-- The target swap preserves validity on the certified pair. -/
theorem targetSwapPreservesFissionValidity
    {Source Target : Type}
    {d : TemporalFissionData Source Target}
    (cert : TemporalFissionCertificate d) :
    d.valid (d.swap d.left) ∧ d.valid (d.swap d.right) := by
  rw [cert.swapLeft, cert.swapRight]
  exact ⟨cert.rightValid, cert.leftValid⟩

/-- Exact fixed-point-free target symmetry supplies no invariant singleton on the branch pair. -/
theorem targetSwapSymmetryNonselection
    {Source Target : Type}
    {d : TemporalFissionData Source Target}
    (cert : TemporalFissionCertificate d) :
    d.swap d.left ≠ d.left ∧ d.swap d.right ≠ d.right := by
  constructor
  · rw [cert.swapLeft]
    exact Ne.symm cert.targetsDistinct
  · rw [cert.swapRight]
    exact cert.targetsDistinct

end CSTTT.CorridorTheory
