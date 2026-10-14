import CSTTT.Corridor.FiniteTemporalCorridor

namespace CSTTT.CorridorTheory

/-- A summary of a nonempty chain of audited overlap legs. -/
structure CorridorSummaryData (Signature : Type) where
  source : CarrierId
  target : CarrierId
  entry : Signature
  exit : Signature
  atomicLegsValid : Prop
  noRealizedGap : Prop
  routeDisciplined : Prop
  frontierWitness : Prop

/-- Proof fields for a strict carrier-chain corridor summary. -/
structure CorridorSummaryCertificate
    {Signature : Type}
    (d : CorridorSummaryData Signature) where
  endpointDistinct : d.source ≠ d.target
  atomicLegsValid : d.atomicLegsValid
  noRealizedGap : d.noRealizedGap
  routeDisciplined : d.routeDisciplined
  frontierWitness : d.frontierWitness

/-- Exact compatibility of the shared carrier and temporal frontier. -/
def FrontierCompatible
    {Signature : Type}
    (left right : CorridorSummaryData Signature) : Prop :=
  left.target = right.source ∧ left.exit = right.entry

/-- Concatenation keeps every leg, gap, route, and frontier obligation explicit. -/
def composeData
    {Signature : Type}
    (left right : CorridorSummaryData Signature) : CorridorSummaryData Signature where
  source := left.source
  target := right.target
  entry := left.entry
  exit := right.exit
  atomicLegsValid := left.atomicLegsValid ∧ right.atomicLegsValid
  noRealizedGap := left.noRealizedGap ∧ right.noRealizedGap
  routeDisciplined := left.routeDisciplined ∧ right.routeDisciplined
  frontierWitness := FrontierCompatible left right

/-- Two certified corridors compose when the shared temporal frontier agrees. -/
def composeCertificate
    {Signature : Type}
    {left right : CorridorSummaryData Signature}
    (leftCert : CorridorSummaryCertificate left)
    (rightCert : CorridorSummaryCertificate right)
    (frontier : FrontierCompatible left right)
    (endpointsDistinct : left.source ≠ right.target) :
    CorridorSummaryCertificate (composeData left right) where
  endpointDistinct := endpointsDistinct
  atomicLegsValid := ⟨leftCert.atomicLegsValid, rightCert.atomicLegsValid⟩
  noRealizedGap := ⟨leftCert.noRealizedGap, rightCert.noRealizedGap⟩
  routeDisciplined := ⟨leftCert.routeDisciplined, rightCert.routeDisciplined⟩
  frontierWitness := frontier

/-- TTH-04: strict carrier-chain corridor composition. -/
theorem strictTemporalCorridorComposition
    {Signature : Type}
    {left right : CorridorSummaryData Signature}
    (leftCert : CorridorSummaryCertificate left)
    (rightCert : CorridorSummaryCertificate right)
    (frontier : FrontierCompatible left right)
    (endpointsDistinct : left.source ≠ right.target) :
    Nonempty (CorridorSummaryCertificate (composeData left right)) := by
  exact ⟨composeCertificate leftCert rightCert frontier endpointsDistinct⟩

end CSTTT.CorridorTheory
