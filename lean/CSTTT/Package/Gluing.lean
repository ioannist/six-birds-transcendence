import CSTTT.Package.Clauses

namespace CSTTT

structure JoinEdge where
  left : ClauseId
  right : ClauseId
  deriving DecidableEq, Repr

/-- The running-intersection and acyclicity obligations remain explicit theorem premises. -/
structure JoinTree where
  edges : List JoinEdge
  coversAllClauses : Prop
  acyclic : Prop
  runningIntersection : Prop

/-- Certificate layer for one coherent target package. -/
structure IntegratedPackageCertificate
    (target : Carrier)
    (pa : PackageAlphabet)
    (ta : TemporalAlphabet)
    (ts : TemporalClosureSpec target ta)
    (c1 : ClauseSpec .c1Objecthood pa)
    (c2 : ClauseSpec .c2StrictPromotion pa)
    (c3 : ClauseSpec .c3ReflexiveSelfCoordinate pa)
    (c4 : ClauseSpec .c4InterfaceNonexposure pa)
    (c5 : ClauseSpec .c5ActionCredit pa)
    (c6 : ClauseSpec .c6TemporalClosure pa)
    (c7 : ClauseSpec .c7BindingRecombination pa)
    (c8 : ClauseSpec .c8ViabilityRepair pa) where
  globalAssignment : GlobalAssignment pa
  localWitnesses : ClauseBundle pa c1 c2 c3 c4 c5 c6 c7 c8
  joinTree : JoinTree
  overlapCompatible : Prop
  globalWitnessValid : Prop
  everyHardGatePassed : Prop
  temporalSubstance : TemporalClosureWitness target ta ts
  targetOwnedAfterTakeover : Prop

/-- Staged preservation is separate from target realization and from any lineage criterion. -/
structure StagedClausePreservationEvidence where
  eachDeclaredStageAudited : Prop
  clauseMapsSeparatelyTyped : Prop
  hardGatesNeverAveragedAway : Prop

end CSTTT
