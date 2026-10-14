import CSTTT.Temporal.Closure
import CSTTT.Temporal.Clock

namespace CSTTT

/-- Heterogeneous transport data contain no lineage verdict. -/
structure TemporalBridge (src dst : TemporalAlphabet) where
  clock : ClockTranslation src dst
  representativeIndependent : Prop
  predictivePreserved : Prop
  orderPreserved : Prop
  tickPhasePreserved : Prop
  tickProgressPreserved : Prop
  recordDescentPreserved : Prop
  routeResidueRetained : Prop
  maintenanceTranslated : Prop
  ownershipInterfaceValid : Prop

/-- A bundled bridge connects separately typed temporal witnesses without asserting lineage. -/
structure TemporalTransportCertificate
    (source target : Carrier)
    (srcA dstA : TemporalAlphabet)
    (srcSpec : TemporalClosureSpec source srcA)
    (dstSpec : TemporalClosureSpec target dstA) where
  distinctCarriers : source.id ≠ target.id
  sourceState : source.State
  targetState : target.State
  sourceTemporal : TemporalClosureWitness source srcA srcSpec
  targetTemporal : TemporalClosureWitness target dstA dstSpec
  bridge : TemporalBridge srcA dstA
  sourceWitnessMatches : sourceTemporal.state = sourceState
  targetWitnessMatches : targetTemporal.state = targetState
  bundledAgreement : Prop

/-- A route audit keeps current, predictive, residue, and clock-translation comparisons separate. -/
structure RouteHolonomyAudit where
  routeA : List NamedToken
  routeB : List NamedToken
  sameEndpoints : Prop
  currentAgreement : Prop
  predictiveAgreement : Prop
  routeResidueAgreement : Prop
  translationAgreement : Prop

/-- Route independence is available only through separately audited completion conditions. -/
structure FlatnessCertificate where
  everyDeclaredCriticalPairJoins : Prop
  routeResidueTrivial : Prop
  clockTranslationHolonomyZero : Prop

end CSTTT
