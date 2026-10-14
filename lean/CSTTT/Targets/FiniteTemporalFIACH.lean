import CSTTT.Targets.TemporalFIACH
import CSTTT.Autonomy.FiniteAutonomy

namespace CSTTT.TargetTheory

/-- The integrated theorem is only a projection of already independent proof
    fields. No lane is inferred from either of the other two. -/
theorem temporalFIACHCertificateSoundness
    {PackageCert CorridorCert AutonomyCert : Type}
    {packageValid : PackageCert → Prop}
    {corridorValid : CorridorCert → Prop}
    {autonomyValid : AutonomyCert → Prop}
    {packageTarget : PackageCert → CarrierId}
    {corridorSource : CorridorCert → CarrierId}
    {corridorTarget : CorridorCert → CarrierId}
    {autonomyTarget : AutonomyCert → CarrierId}
    (cert : TemporalFIACHCertificate PackageCert CorridorCert AutonomyCert
      packageValid corridorValid autonomyValid packageTarget
      corridorSource corridorTarget autonomyTarget) :
    packageValid cert.packageCertificate ∧
    corridorValid cert.corridorCertificate ∧
    autonomyValid cert.autonomyCertificate := by
  exact ⟨cert.packageEvidence, cert.corridorEvidence, cert.autonomyEvidence⟩

/-- Endpoint linkage is also exposed separately from lane validity. -/
theorem temporalFIACHEndpointsLinked
    {PackageCert CorridorCert AutonomyCert : Type}
    {packageValid : PackageCert → Prop}
    {corridorValid : CorridorCert → Prop}
    {autonomyValid : AutonomyCert → Prop}
    {packageTarget : PackageCert → CarrierId}
    {corridorSource : CorridorCert → CarrierId}
    {corridorTarget : CorridorCert → CarrierId}
    {autonomyTarget : AutonomyCert → CarrierId}
    (cert : TemporalFIACHCertificate PackageCert CorridorCert AutonomyCert
      packageValid corridorValid autonomyValid packageTarget
      corridorSource corridorTarget autonomyTarget) :
    packageTarget cert.packageCertificate = cert.target ∧
    corridorSource cert.corridorCertificate = cert.source ∧
    corridorTarget cert.corridorCertificate = cert.target ∧
    autonomyTarget cert.autonomyCertificate = cert.target := by
  exact ⟨cert.packageEndpoint, cert.corridorSourceEndpoint,
    cert.corridorTargetEndpoint, cert.autonomyEndpoint⟩

/-- Executable three-lane abstraction used only to verify conjunction logic. -/
structure ThreeLaneStatus where
  realized : Bool
  lineage : Bool
  autonomous : Bool
  deriving DecidableEq, Repr

/-- The aggregate Boolean is exact conjunction, never a score or vote. -/
def ThreeLaneStatus.aggregate (status : ThreeLaneStatus) : Bool :=
  status.realized && status.lineage && status.autonomous

/-- The eight-row truth table has exactly one positive row. -/
theorem threeLaneAggregateExact (status : ThreeLaneStatus) :
    status.aggregate = true ↔
      status.realized = true ∧ status.lineage = true ∧ status.autonomous = true := by
  cases status with
  | mk realized lineage autonomous =>
      cases realized <;> cases lineage <;> cases autonomous <;> decide

end CSTTT.TargetTheory
