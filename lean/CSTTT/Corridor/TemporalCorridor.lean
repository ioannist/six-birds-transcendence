import CSTTT.Core.Episode
import CSTTT.Temporal.Signature

namespace CSTTT

/-- Counterfactual nonredundancy is specified without referring to the final handoff verdict. -/
structure CounterfactualAudit (n : Nat) where
  atStage : Stage n
  laterStage : Stage n
  laterIsStrictlyLater : atStage.val < laterStage.val
  sourceRemovalChangesLaterSignature : Prop
  targetRemovalChangesLaterSignature : Prop

/-- Episode-local data used by the strict overlap corridor. -/
structure TemporalCorridorData (n : Nat) where
  episode : Episode n
  temporalRealizedAt : Stage n → Prop
  transportAuditedAt : Stage n → Prop
  counterfactual : CounterfactualAudit n
  takeoverFrontier : Stage n
  routeStatus : RouteStatus

/-- The strict corridor is a certificate over independently declared temporal and episode data. -/
structure TemporalCorridorCertificate {n : Nat} (d : TemporalCorridorData n) where
  startsSourceOnly : ∃ k : Stage n, k.val = 0 ∧ d.episode.sourceOnly k
  endsTargetOnly : ∃ k : Stage n, k.val = n ∧ d.episode.targetOnly k
  noTemporalGap : d.episode.noGap ∧ ∀ k : Stage n, d.temporalRealizedAt k
  genuinelyMixed : d.episode.mixedAt d.counterfactual.atStage
  sourceNonredundant : d.counterfactual.sourceRemovalChangesLaterSignature
  targetNonredundant : d.counterfactual.targetRemovalChangesLaterSignature
  transportAudited : ∀ k : Stage n, d.transportAuditedAt k
  takeoverValid : d.episode.sourceAbsentAfter d.takeoverFrontier
  routeDiscipline : d.routeStatus = .flat ∨ d.routeStatus = .routeIndexed

end CSTTT
