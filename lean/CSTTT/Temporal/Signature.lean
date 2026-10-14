import CSTTT.Core.Carrier

namespace CSTTT

/-- Finite alphabets for each independently audited component of layer-realized time. -/
structure TemporalAlphabet where
  predictiveType : Type
  orderType : Type
  tickType : Type
  progressType : Type
  recordType : Type
  routeType : Type
  maintenanceType : Type
  predictiveEnum : FiniteEnum predictiveType
  orderEnum : FiniteEnum orderType
  tickEnum : FiniteEnum tickType
  progressEnum : FiniteEnum progressType
  recordEnum : FiniteEnum recordType
  routeEnum : FiniteEnum routeType
  maintenanceEnum : FiniteEnum maintenanceType

/-- The future-sufficient present includes current predictive state and retained route residue. -/
structure PredictiveNow (a : TemporalAlphabet) where
  predictiveClass : a.predictiveType
  routeResidue : a.routeType
  futureSufficient : Prop

/-- The temporal object is defined before any corridor or handoff predicate. -/
structure TemporalSignature (a : TemporalAlphabet) where
  predictiveNow : PredictiveNow a
  orderState : a.orderType
  tickPhase : a.tickType
  progressState : a.progressType
  arrowRecord : a.recordType
  maintenanceState : a.maintenanceType
  owner : CarrierId

inductive RouteStatus where
  | flat
  | routeIndexed
  | unresolved
  deriving DecidableEq, Repr

inductive RecognitionStatus where
  | notAddressed
  | assumedInterface
  | externallyAudited
  deriving DecidableEq, Repr

end CSTTT
