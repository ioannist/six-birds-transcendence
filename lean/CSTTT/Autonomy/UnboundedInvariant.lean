import CSTTT.Autonomy.FiniteAutonomy

namespace CSTTT.AutonomyTheory

/-- A total target-owned policy chooses one admissible successor at every
    certified state and disturbance. -/
structure ExactAutonomyPolicy (d : ExactAutonomyData) where
  action : d.sys.carrier.State → d.sys.Disturbance → d.sys.Action
  next : d.sys.carrier.State → d.sys.Disturbance → d.sys.carrier.State
  endpointInside : d.inside d.endpoint
  owner :
    ∀ x disturbance, d.inside x →
      d.sys.actionOwner (action x disturbance) = d.sys.carrier.id
  step :
    ∀ x disturbance, d.inside x →
      d.sys.step x disturbance (action x disturbance) (next x disturbance)
  insideNext :
    ∀ x disturbance, d.inside x → d.inside (next x disturbance)
  antiStall :
    ∀ x disturbance, d.inside x →
      d.antiStall x disturbance (action x disturbance) (next x disturbance)
  budgetSolvent :
    ∀ x disturbance, d.inside x →
      d.budgetSolvent x disturbance (action x disturbance) (next x disturbance)

/-- The state selected after n disturbances. -/
def policyState
    {d : ExactAutonomyData}
    (policy : ExactAutonomyPolicy d)
    (disturbance : Nat → d.sys.Disturbance) : Nat → d.sys.carrier.State
  | 0 => d.endpoint
  | n + 1 => policy.next (policyState policy disturbance n) (disturbance n)

/-- Every point of the infinite model-relative trajectory remains in the
    controlled invariant. -/
theorem policyStateInside
    {d : ExactAutonomyData}
    (policy : ExactAutonomyPolicy d)
    (disturbance : Nat → d.sys.Disturbance) :
    ∀ n, d.inside (policyState policy disturbance n) := by
  intro n
  induction n with
  | zero => exact policy.endpointInside
  | succ n ih =>
      exact policy.insideNext (policyState policy disturbance n) (disturbance n) ih

/-- TTS-04. A total exact policy supplies an unbounded sequence of
    target-owned, anti-stalling, budget-solvent transitions inside the finite
    controlled model. This is not a theorem of indefinite physical persistence. -/
theorem modelRelativeUnboundedControlledInvariant
    {d : ExactAutonomyData}
    (cert : ExactAutonomyCertificate d)
    (policy : ExactAutonomyPolicy d)
    (disturbance : Nat → d.sys.Disturbance) :
    ∀ n,
      d.sys.packageValid (policyState policy disturbance n) ∧
      d.sys.actionOwner
        (policy.action (policyState policy disturbance n) (disturbance n)) =
        d.sys.carrier.id ∧
      d.sys.step
        (policyState policy disturbance n)
        (disturbance n)
        (policy.action (policyState policy disturbance n) (disturbance n))
        (policyState policy disturbance (n + 1)) ∧
      d.antiStall
        (policyState policy disturbance n)
        (disturbance n)
        (policy.action (policyState policy disturbance n) (disturbance n))
        (policyState policy disturbance (n + 1)) ∧
      d.budgetSolvent
        (policyState policy disturbance n)
        (disturbance n)
        (policy.action (policyState policy disturbance n) (disturbance n))
        (policyState policy disturbance (n + 1)) := by
  intro n
  have hInside := policyStateInside policy disturbance n
  exact ⟨
    cert.packageInside _ hInside,
    policy.owner _ _ hInside,
    policy.step _ _ hInside,
    policy.antiStall _ _ hInside,
    policy.budgetSolvent _ _ hInside
  ⟩

/-- For every finite horizon there is a countdown that is live throughout the
    horizon and fails immediately afterwards. -/
def CountdownLive (horizon time : Nat) : Prop := time ≤ horizon

/-- TTN-12 strengthened boundary. No fixed finite prefix length alone
    establishes unbounded liveness. -/
theorem arbitrarilyLongFinitePrefixStillInsufficient
    (horizon : Nat) :
    (∀ time, time ≤ horizon → CountdownLive horizon time) ∧
    ¬ CountdownLive horizon (horizon + 1) := by
  constructor
  · intro time h
    exact h
  · simp [CountdownLive]

end CSTTT.AutonomyTheory
