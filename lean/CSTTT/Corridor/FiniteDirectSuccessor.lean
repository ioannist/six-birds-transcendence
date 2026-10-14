import CSTTT.Core.Episode
import CSTTT.Temporal.Signature

namespace CSTTT.DirectSuccessorTheory

/-- Event-level evidence for one immediate cross-carrier temporal edge. -/
structure AtomicDirectSuccessorData where
  source : CarrierId
  target : CarrierId
  immediateEdge : Prop
  payloadComplete : Prop
  payloadHashBound : Prop
  edgeNecessary : Prop
  storageMediated : Prop
  replayableArchive : Prop
  alternativeTemporalParent : Prop
  singleUseToken : Prop
  predictiveStep : Prop
  orderStep : Prop
  tickStep : Prop
  progressStep : Prop
  recordStep : Prop
  routeDisciplined : Prop
  ownershipTransferred : Prop

/-- Proof fields for one immediate temporal edge. -/
structure AtomicDirectSuccessorCertificate (d : AtomicDirectSuccessorData) where
  distinctCarriers : d.source ≠ d.target
  immediateEdge : d.immediateEdge
  payloadComplete : d.payloadComplete
  payloadHashBound : d.payloadHashBound
  edgeNecessary : d.edgeNecessary
  notStorageMediated : ¬ d.storageMediated
  notReplayableArchive : ¬ d.replayableArchive
  noAlternativeTemporalParent : ¬ d.alternativeTemporalParent
  singleUseToken : d.singleUseToken
  predictiveStep : d.predictiveStep
  orderStep : d.orderStep
  tickStep : d.tickStep
  progressStep : d.progressStep
  recordStep : d.recordStep
  routeDisciplined : d.routeDisciplined
  ownershipTransferred : d.ownershipTransferred

/-- The operational pattern excluded by the immediate-edge certificate. -/
def DetachedOperationalPattern (d : AtomicDirectSuccessorData) : Prop :=
  d.storageMediated ∨ d.replayableArchive ∨ ¬ d.edgeNecessary ∨ ¬ d.immediateEdge

/-- TTD-01: all event-level and temporal fields imply the declared validity bundle. -/
theorem directSuccessorValidity
    {d : AtomicDirectSuccessorData}
    (c : AtomicDirectSuccessorCertificate d) :
    d.immediateEdge ∧ d.payloadComplete ∧ d.payloadHashBound ∧
    d.edgeNecessary ∧ d.predictiveStep ∧ d.orderStep ∧ d.tickStep ∧
    d.progressStep ∧ d.recordStep ∧ d.routeDisciplined ∧
    d.ownershipTransferred := by
  exact ⟨c.immediateEdge, c.payloadComplete, c.payloadHashBound,
    c.edgeNecessary, c.predictiveStep, c.orderStep, c.tickStep,
    c.progressStep, c.recordStep, c.routeDisciplined,
    c.ownershipTransferred⟩

/-- TTD-03: a valid immediate edge excludes the declared detached pattern. -/
theorem directSuccessorDetachedCopyExclusion
    {d : AtomicDirectSuccessorData}
    (c : AtomicDirectSuccessorCertificate d) :
    ¬ DetachedOperationalPattern d := by
  intro h
  rcases h with hStorage | hReplay | hNotNecessary | hNotImmediate
  · exact c.notStorageMediated hStorage
  · exact c.notReplayableArchive hReplay
  · exact hNotNecessary c.edgeNecessary
  · exact hNotImmediate c.immediateEdge

/-- Summary data for a nonempty path of immediate temporal edges. -/
structure DirectSuccessorPathData (Signature : Type) where
  source : CarrierId
  target : CarrierId
  entry : Signature
  exit : Signature
  everyAtomicEdgeValid : Prop
  noRealizedGap : Prop
  exactFrontiers : Prop

/-- Proof fields for an event-edge path. -/
structure DirectSuccessorPathCertificate
    {Signature : Type}
    (d : DirectSuccessorPathData Signature) where
  endpointDistinct : d.source ≠ d.target
  everyAtomicEdgeValid : d.everyAtomicEdgeValid
  noRealizedGap : d.noRealizedGap
  exactFrontiers : d.exactFrontiers

/-- Exact boundary agreement for two event-edge paths. -/
def DirectPathCompatible
    {Signature : Type}
    (left right : DirectSuccessorPathData Signature) : Prop :=
  left.target = right.source ∧ left.exit = right.entry

/-- Path concatenation does not create a new atomic endpoint edge. -/
def composePathData
    {Signature : Type}
    (left right : DirectSuccessorPathData Signature) : DirectSuccessorPathData Signature where
  source := left.source
  target := right.target
  entry := left.entry
  exit := right.exit
  everyAtomicEdgeValid := left.everyAtomicEdgeValid ∧ right.everyAtomicEdgeValid
  noRealizedGap := left.noRealizedGap ∧ right.noRealizedGap
  exactFrontiers := DirectPathCompatible left right

/-- Certified event-edge paths compose under exact boundary agreement. -/
theorem directSuccessorPathComposition
    {Signature : Type}
    {left right : DirectSuccessorPathData Signature}
    (leftCert : DirectSuccessorPathCertificate left)
    (rightCert : DirectSuccessorPathCertificate right)
    (frontier : DirectPathCompatible left right)
    (endpointsDistinct : left.source ≠ right.target) :
    Nonempty (DirectSuccessorPathCertificate (composePathData left right)) := by
  exact ⟨{
    endpointDistinct := endpointsDistinct
    everyAtomicEdgeValid := ⟨leftCert.everyAtomicEdgeValid, rightCert.everyAtomicEdgeValid⟩
    noRealizedGap := ⟨leftCert.noRealizedGap, rightCert.noRealizedGap⟩
    exactFrontiers := frontier
  }⟩

end CSTTT.DirectSuccessorTheory
