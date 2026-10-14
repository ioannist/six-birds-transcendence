import CSTTT.Core.Finite

namespace CSTTT.RobustnessTheory

/-- A signed temporal margin with an exact symmetric perturbation radius. -/
structure TemporalMargin where
  baseIncrement : Int
  minimumIncrement : Int
  radius : Int
  radiusNonnegative : 0 ≤ radius
  certifiedWorstCase : minimumIncrement + radius ≤ baseIncrement

/-- The declared perturbation lies inside the exact componentwise box. -/
def WithinRadius (m : TemporalMargin) (delta : Int) : Prop :=
  -m.radius ≤ delta ∧ delta ≤ m.radius

/-- TTS-03a. The certified box preserves the minimum increment. -/
theorem boundedPerturbationPreservesMargin
    (m : TemporalMargin)
    (delta : Int)
    (hDelta : WithinRadius m delta) :
    m.minimumIncrement ≤ m.baseIncrement + delta := by
  rcases hDelta with ⟨hLower, _⟩
  have hWorst := m.certifiedWorstCase
  omega

/-- Hard gates are kept separate from numerical margins. -/
structure HardGateBundle where
  distinctCarriers : Prop
  routeDisciplined : Prop
  targetOwned : Prop
  integratedPackage : Prop
  strictLineageMode : Prop
  postWithdrawalAutonomy : Prop

structure HardGateCertificate (g : HardGateBundle) where
  distinctCarriers : g.distinctCarriers
  routeDisciplined : g.routeDisciplined
  targetOwned : g.targetOwned
  integratedPackage : g.integratedPackage
  strictLineageMode : g.strictLineageMode
  postWithdrawalAutonomy : g.postWithdrawalAutonomy

/-- TTS-03b. Numerical approximation cannot repair a failed hard gate. -/
theorem failedHardGateCannotBeAveragedAway
    (g : HardGateBundle)
    (hFail : ¬ g.integratedPackage) :
    ¬ Nonempty (HardGateCertificate g) := by
  intro h
  rcases h with ⟨cert⟩
  exact hFail cert.integratedPackage

/-- A finite list of independently certified margins is robust pointwise. -/
def MarginVectorAccepts
    (margins : List TemporalMargin)
    (deltas : List Int) : Prop :=
  ListForall₂
    (fun margin delta =>
      WithinRadius margin delta ∧
      margin.minimumIncrement ≤ margin.baseIncrement + delta)
    margins deltas

end CSTTT.RobustnessTheory
