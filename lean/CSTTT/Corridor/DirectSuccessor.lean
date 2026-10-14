import CSTTT.Core.Episode
import CSTTT.Transport.TemporalBridge

namespace CSTTT

/-- A separately named, provisional class for a direct source-event to target-event successor. -/
structure DirectSuccessorCertificate
    {n : Nat}
    (source target : Carrier)
    (srcA dstA : TemporalAlphabet)
    (srcSpec : TemporalClosureSpec source srcA)
    (dstSpec : TemporalClosureSpec target dstA) where
  distinctCarriers : source.id ≠ target.id
  episode : Episode n
  episodeSourceMatches : episode.source = source.id
  episodeTargetMatches : episode.target = target.id
  lastSourceEvent : Event n
  firstTargetEvent : Event n
  lastSourceDeclared : lastSourceEvent ∈ episode.events
  firstTargetDeclared : firstTargetEvent ∈ episode.events
  sourceOwned : lastSourceEvent.owner = source.id
  targetOwned : firstTargetEvent.owner = target.id
  operationalDependency : Dependency n
  dependencyDeclared : operationalDependency ∈ episode.dependencies
  dependencyMatches :
    operationalDependency.parent = lastSourceEvent ∧
    operationalDependency.child = firstTargetEvent
  transport : TemporalTransportCertificate source target srcA dstA srcSpec dstSpec
  successorCompatible : Prop
  recordDescent : Prop
  ownershipInterface : Prop
  provenanceNotEndpointEquality : Prop

end CSTTT
