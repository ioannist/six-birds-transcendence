import CSTTT.Autonomy.System

namespace CSTTT.AutonomyTheory

/-- Exact autonomy data are fixed independently of any handoff verdict. -/
structure ExactAutonomyData where
  sys : ControlledSystem
  endpoint : sys.carrier.State
  withdrawal : WithdrawalSpec
  inside : sys.carrier.State → Prop
  resourceOwner : ResourceId → CarrierId
  antiStall : sys.carrier.State → sys.Disturbance → sys.Action → sys.carrier.State → Prop
  budgetSolvent : sys.carrier.State → sys.Disturbance → sys.Action → sys.carrier.State → Prop
  boundaryFixedBeforeEvaluation : Prop
  disturbanceClassFixedBeforeEvaluation : Prop

/-- A certificate keeps withdrawal, package closure, resource ownership,
    response, anti-stall, and budget obligations as separate proof fields. -/
structure ExactAutonomyCertificate (d : ExactAutonomyData) where
  sourceRemoved : d.withdrawal.sourceRemoved
  bridgeRemoved : d.withdrawal.bridgeRemoved
  migrationControllerRemoved : d.withdrawal.migrationControllerRemoved
  externalDecoderRemoved : d.withdrawal.externalDecoderRemoved
  externalSchedulerRemoved : d.withdrawal.externalSchedulerRemoved
  undeclaredRepairRemoved : d.withdrawal.undeclaredRepairRemoved
  boundaryFixed : d.boundaryFixedBeforeEvaluation
  disturbanceClassFixed : d.disturbanceClassFixedBeforeEvaluation
  endpointInside : d.inside d.endpoint
  packageInside : ∀ x : d.sys.carrier.State, d.inside x → d.sys.packageValid x
  resourceClosed :
    ∀ x : d.sys.carrier.State, d.inside x →
      ∀ r : ResourceId, r ∈ d.sys.maintenanceResources x →
        r ∈ d.withdrawal.retainedResources
  retainedResourcesTargetOwned :
    ∀ r : ResourceId, r ∈ d.withdrawal.retainedResources →
      d.resourceOwner r = d.sys.carrier.id
  response :
    ∀ x : d.sys.carrier.State, ∀ disturbance : d.sys.Disturbance,
      d.inside x →
        ∃ action : d.sys.Action, ∃ x' : d.sys.carrier.State,
          d.sys.actionOwner action = d.sys.carrier.id ∧
          d.sys.step x disturbance action x' ∧
          d.inside x' ∧
          d.antiStall x disturbance action x' ∧
          d.budgetSolvent x disturbance action x'

/-- A finite disturbance word is answered only by target-owned, anti-stalling,
    budget-solvent steps that remain inside the declared region. -/
inductive ControlledRun (d : ExactAutonomyData) :
    d.sys.carrier.State → List d.sys.Disturbance → d.sys.carrier.State → Prop where
  | nil (x : d.sys.carrier.State) (inside : d.inside x) :
      ControlledRun d x [] x
  | cons
      {x x' y : d.sys.carrier.State}
      {disturbance : d.sys.Disturbance}
      {rest : List d.sys.Disturbance}
      (action : d.sys.Action)
      (owner : d.sys.actionOwner action = d.sys.carrier.id)
      (step : d.sys.step x disturbance action x')
      (inside : d.inside x')
      (antiStall : d.antiStall x disturbance action x')
      (budgetSolvent : d.budgetSolvent x disturbance action x')
      (tail : ControlledRun d x' rest y) :
      ControlledRun d x (disturbance :: rest) y

/-- Every finite disturbance word has a certified target-owned response run. -/
theorem finiteHorizonRunExists
    {d : ExactAutonomyData}
    (cert : ExactAutonomyCertificate d)
    (x : d.sys.carrier.State)
    (inside : d.inside x)
    (word : List d.sys.Disturbance) :
    ∃ y : d.sys.carrier.State, ControlledRun d x word y ∧ d.inside y := by
  induction word generalizing x with
  | nil =>
      exact ⟨x, ControlledRun.nil x inside, inside⟩
  | cons disturbance rest ih =>
      rcases cert.response x disturbance inside with
        ⟨action, x', owner, step, inside', antiStall, budgetSolvent⟩
      rcases ih x' inside' with ⟨y, tail, insideY⟩
      exact ⟨y,
        ControlledRun.cons action owner step inside' antiStall budgetSolvent tail,
        insideY⟩

/-- TTH-05 / PTH-04. The package persists at the end of every declared finite
    disturbance word. This theorem does not assert unbounded physical liveness. -/
theorem postWithdrawalFiniteHorizonInvariance
    {d : ExactAutonomyData}
    (cert : ExactAutonomyCertificate d)
    (word : List d.sys.Disturbance) :
    ∃ y : d.sys.carrier.State,
      ControlledRun d d.endpoint word y ∧ d.sys.packageValid y := by
  rcases finiteHorizonRunExists cert d.endpoint cert.endpointInside word with
    ⟨y, run, insideY⟩
  exact ⟨y, run, cert.packageInside y insideY⟩

/-- A resource required at the endpoint cannot simultaneously be removed and
    certified as retained. This is the generic TTN-06 boundary. -/
theorem removedEssentialResourceExcludesAutonomy
    (d : ExactAutonomyData)
    (resource : ResourceId)
    (required : resource ∈ d.sys.maintenanceResources d.endpoint)
    (removed : resource ∈ d.withdrawal.removedResources) :
    ¬ Nonempty (ExactAutonomyCertificate d) := by
  intro hasCertificate
  rcases hasCertificate with ⟨cert⟩
  have retained : resource ∈ d.withdrawal.retainedResources :=
    cert.resourceClosed d.endpoint cert.endpointInside resource required
  exact d.withdrawal.disjoint resource removed retained

/-- If every candidate response to one allowed disturbance stalls, no exact
    autonomy certificate exists. -/
theorem stalledOnlyResponsesExcludeAutonomy
    (d : ExactAutonomyData)
    (disturbance : d.sys.Disturbance)
    (noProgress :
      ∀ action : d.sys.Action, ∀ x' : d.sys.carrier.State,
        d.sys.actionOwner action = d.sys.carrier.id →
        d.sys.step d.endpoint disturbance action x' →
        d.inside x' →
        ¬ d.antiStall d.endpoint disturbance action x') :
    ¬ Nonempty (ExactAutonomyCertificate d) := by
  intro hasCertificate
  rcases hasCertificate with ⟨cert⟩
  rcases cert.response d.endpoint disturbance cert.endpointInside with
    ⟨action, x', owner, step, inside', antiStall, _⟩
  exact (noProgress action x' owner step inside') antiStall

/-- Likewise, if every candidate response is insolvent, autonomy fails. -/
theorem insolventOnlyResponsesExcludeAutonomy
    (d : ExactAutonomyData)
    (disturbance : d.sys.Disturbance)
    (noSolventResponse :
      ∀ action : d.sys.Action, ∀ x' : d.sys.carrier.State,
        d.sys.actionOwner action = d.sys.carrier.id →
        d.sys.step d.endpoint disturbance action x' →
        d.inside x' →
        ¬ d.budgetSolvent d.endpoint disturbance action x') :
    ¬ Nonempty (ExactAutonomyCertificate d) := by
  intro hasCertificate
  rcases hasCertificate with ⟨cert⟩
  rcases cert.response d.endpoint disturbance cert.endpointInside with
    ⟨action, x', owner, step, inside', _, budgetSolvent⟩
  exact (noSolventResponse action x' owner step inside') budgetSolvent

end CSTTT.AutonomyTheory
