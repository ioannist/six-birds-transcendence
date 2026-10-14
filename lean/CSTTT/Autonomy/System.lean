import CSTTT.Core.Carrier

namespace CSTTT

structure ControlledSystem where
  carrier : Carrier
  Disturbance : Type
  Action : Type
  disturbanceEnum : FiniteEnum Disturbance
  actionEnum : FiniteEnum Action
  step : carrier.State → Disturbance → Action → carrier.State → Prop
  packageValid : carrier.State → Prop
  actionOwner : Action → CarrierId
  maintenanceResources : carrier.State → List ResourceId

/-- Withdrawal names every removed and retained dependency before autonomy is evaluated. -/
structure WithdrawalSpec where
  removedResources : List ResourceId
  retainedResources : List ResourceId
  disjoint : ∀ r : ResourceId, r ∈ removedResources → r ∉ retainedResources
  sourceRemoved : Prop
  bridgeRemoved : Prop
  migrationControllerRemoved : Prop
  externalDecoderRemoved : Prop
  externalSchedulerRemoved : Prop
  undeclaredRepairRemoved : Prop

structure ControlledInvariantCertificate
    (sys : ControlledSystem) (endpoint : sys.carrier.State) where
  inside : sys.carrier.State → Prop
  endpointInside : inside endpoint
  packageInside : ∀ x : sys.carrier.State, inside x → sys.packageValid x
  targetOwnedResponse :
    ∀ x : sys.carrier.State, ∀ d : sys.Disturbance, inside x →
      ∃ a : sys.Action, ∃ x' : sys.carrier.State,
        sys.actionOwner a = sys.carrier.id ∧ sys.step x d a x' ∧ inside x'

structure AutonomyCertificate
    (sys : ControlledSystem) (endpoint : sys.carrier.State) where
  withdrawal : WithdrawalSpec
  invariant : ControlledInvariantCertificate sys endpoint
  antiStall : Prop
  budgetSolventOnInvariant : Prop
  targetOwnsMaintenance : Prop

end CSTTT
