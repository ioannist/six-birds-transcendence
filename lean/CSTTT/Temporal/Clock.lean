import CSTTT.Temporal.Signature

namespace CSTTT

/-- A separately typed translation between source-local and target-local temporal vocabularies. -/
structure ClockTranslation (src dst : TemporalAlphabet) where
  mapPredictive : src.predictiveType → dst.predictiveType
  mapOrder : src.orderType → dst.orderType
  mapTick : src.tickType → dst.tickType
  mapProgress : src.progressType → dst.progressType
  mapRecord : src.recordType → dst.recordType
  mapRoute : src.routeType → dst.routeType
  mapMaintenance : src.maintenanceType → dst.maintenanceType
  successorCompatible : Prop
  progressCompatible : Prop
  recordMonotone : Prop

/-- Two route translations can agree currently while differing predictively or on route residue. -/
structure RouteComparison where
  currentAgreement : Prop
  predictiveAgreement : Prop
  routeAgreement : Prop
  clockTranslationAgreement : Prop

end CSTTT
