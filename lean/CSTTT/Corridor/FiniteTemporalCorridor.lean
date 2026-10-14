import CSTTT.Core.Episode
import CSTTT.Temporal.Signature

namespace CSTTT.CorridorTheory

/-- One finite stage of the episode-local temporal audit. -/
structure FiniteTemporalStage where
  index : Nat
  support : List CarrierId
  realized : Bool
  predictiveRank : Nat
  orderRank : Nat
  tickIndex : Nat
  progressRank : Nat
  recordValue : Nat
  routeResidue : List Nat
  maintenanceOwner : CarrierId
  deriving DecidableEq, Repr

/-- Every declared stage realizes the temporal package. -/
def NoRealizedGap (stages : List FiniteTemporalStage) : Prop :=
  ∀ stage ∈ stages, stage.realized = true

/-- A local source and local target are both active at one stage. -/
def HasMixedSupport
    (source target : CarrierId)
    (stages : List FiniteTemporalStage) : Prop :=
  ∃ stage ∈ stages, source ∈ stage.support ∧ target ∈ stage.support

/-- A finite intervention projection used to test both carrier contributions. -/
structure InterventionProjection where
  full : Nat × Nat × Nat
  sourceRemoved : Nat × Nat × Nat
  targetRemoved : Nat × Nat × Nat
  deriving DecidableEq, Repr

/-- Removing the local source changes the declared later projection. -/
def SourceNonredundant (p : InterventionProjection) : Prop :=
  p.full ≠ p.sourceRemoved

/-- Removing the local target changes the declared later projection. -/
def TargetNonredundant (p : InterventionProjection) : Prop :=
  p.full ≠ p.targetRemoved

/-- Data for one overlap leg. The temporal signature is fixed before this data. -/
structure AtomicTemporalCorridorData where
  source : CarrierId
  target : CarrierId
  stages : List FiniteTemporalStage
  intervention : InterventionProjection
  startsSourceOnly : Prop
  endsTargetOnly : Prop
  localStepsStrict : Prop
  eventGraphForward : Prop
  transportAudited : Prop
  takeoverExact : Prop
  routeDisciplined : Prop

/-- Proof fields for one overlap leg. -/
structure AtomicTemporalCorridorCertificate (d : AtomicTemporalCorridorData) where
  distinctCarriers : d.source ≠ d.target
  startsSourceOnly : d.startsSourceOnly
  endsTargetOnly : d.endsTargetOnly
  noRealizedGap : NoRealizedGap d.stages
  mixedSupport : HasMixedSupport d.source d.target d.stages
  sourceNonredundant : SourceNonredundant d.intervention
  targetNonredundant : TargetNonredundant d.intervention
  localStepsStrict : d.localStepsStrict
  eventGraphForward : d.eventGraphForward
  transportAudited : d.transportAudited
  takeoverExact : d.takeoverExact
  routeDisciplined : d.routeDisciplined

/-- The certificate exposes every atomic obligation as a separate conjunct. -/
theorem atomicTemporalCorridorCertificateSound
    {d : AtomicTemporalCorridorData}
    (c : AtomicTemporalCorridorCertificate d) :
    d.source ≠ d.target ∧
    NoRealizedGap d.stages ∧
    HasMixedSupport d.source d.target d.stages ∧
    SourceNonredundant d.intervention ∧
    TargetNonredundant d.intervention ∧
    d.localStepsStrict ∧
    d.eventGraphForward ∧
    d.transportAudited ∧
    d.takeoverExact ∧
    d.routeDisciplined := by
  exact ⟨c.distinctCarriers, c.noRealizedGap, c.mixedSupport,
    c.sourceNonredundant, c.targetNonredundant, c.localStepsStrict,
    c.eventGraphForward, c.transportAudited, c.takeoverExact,
    c.routeDisciplined⟩

/-- With no mixed-support stage, no atomic overlap certificate exists. -/
theorem noMixedStageExcludesAtomicCorridor
    (d : AtomicTemporalCorridorData)
    (hNoMixed : ¬ HasMixedSupport d.source d.target d.stages) :
    ¬ Nonempty (AtomicTemporalCorridorCertificate d) := by
  intro hCert
  rcases hCert with ⟨cert⟩
  exact hNoMixed cert.mixedSupport

/-- A declared unrealized stage contradicts the no-gap field. -/
theorem realizedGapExcludesAtomicCorridor
    (d : AtomicTemporalCorridorData)
    (stage : FiniteTemporalStage)
    (hStage : stage ∈ d.stages)
    (hGap : stage.realized = false) :
    ¬ Nonempty (AtomicTemporalCorridorCertificate d) := by
  intro hCert
  rcases hCert with ⟨cert⟩
  have hRealized : stage.realized = true := cert.noRealizedGap stage hStage
  rw [hGap] at hRealized
  contradiction

end CSTTT.CorridorTheory
