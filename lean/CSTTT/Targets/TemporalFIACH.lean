import CSTTT.Temporal.Signature

namespace CSTTT

/-- Claim lanes are returned independently. -/
inductive ClaimLane where
  | structuralTransport
  | structuralRealization
  | structuralLineage
  | autonomy
  | recognition
  | ontology
  | methodology
  deriving DecidableEq, Repr

/-- Generic aggregation keeps the certificate layers separately typed and endpoint-linked. -/
structure TemporalFIACHCertificate
    (PackageCert CorridorCert AutonomyCert : Type)
    (packageValid : PackageCert → Prop)
    (corridorValid : CorridorCert → Prop)
    (autonomyValid : AutonomyCert → Prop)
    (packageTarget : PackageCert → CarrierId)
    (corridorSource : CorridorCert → CarrierId)
    (corridorTarget : CorridorCert → CarrierId)
    (autonomyTarget : AutonomyCert → CarrierId) where
  source : CarrierId
  target : CarrierId
  distinct : source ≠ target
  sourcePackagePremise : Prop
  sourcePackageEvidence : sourcePackagePremise
  stagedClausePreservation : Prop
  stagedPreservationEvidence : stagedClausePreservation
  packageCertificate : PackageCert
  packageEvidence : packageValid packageCertificate
  packageEndpoint : packageTarget packageCertificate = target
  corridorCertificate : CorridorCert
  corridorEvidence : corridorValid corridorCertificate
  corridorSourceEndpoint : corridorSource corridorCertificate = source
  corridorTargetEndpoint : corridorTarget corridorCertificate = target
  autonomyCertificate : AutonomyCert
  autonomyEvidence : autonomyValid autonomyCertificate
  autonomyEndpoint : autonomyTarget autonomyCertificate = target
  routeStatus : RouteStatus
  recognitionStatus : RecognitionStatus

/-- The structural relation is existence of a separately typed certificate, not an identity predicate. -/
def TemporalFIACH
    (PackageCert CorridorCert AutonomyCert : Type)
    (packageValid : PackageCert → Prop)
    (corridorValid : CorridorCert → Prop)
    (autonomyValid : AutonomyCert → Prop)
    (packageTarget : PackageCert → CarrierId)
    (corridorSource : CorridorCert → CarrierId)
    (corridorTarget : CorridorCert → CarrierId)
    (autonomyTarget : AutonomyCert → CarrierId)
    (source target : CarrierId) : Prop :=
  ∃ cert : TemporalFIACHCertificate PackageCert CorridorCert AutonomyCert
      packageValid corridorValid autonomyValid packageTarget corridorSource corridorTarget autonomyTarget,
    cert.source = source ∧ cert.target = target

end CSTTT
