import CSTTT.Package.FiniteGluing
import CSTTT.Core.Carrier

namespace CSTTT.PackageTheory

/-- Substantive finite C6 data.  Each Boolean audit carries its own proof and
    the tick/record obligations are numerical rather than status labels. -/
structure TemporalSubstance (target : CarrierId) where
  predictiveFutureSufficient : Bool
  predictivePass : predictiveFutureSufficient = true
  orderStable : Bool
  orderPass : orderStable = true
  viableSuccessorAvailable : Bool
  successorPass : viableSuccessorAvailable = true
  tickViable : Bool
  tickViablePass : tickViable = true
  tickProgress : Nat
  tickProgressPositive : 0 < tickProgress
  recordBefore : Nat
  recordAfter : Nat
  recordStrictlyAdvances : recordBefore < recordAfter
  arrowEndogenous : Bool
  arrowPass : arrowEndogenous = true
  externalScheduler : Bool
  noExternalScheduler : externalScheduler = false
  routeResidue : List Nat
  routeResiduePresent : routeResidue ≠ []
  temporalOwner : CarrierId
  temporalOwnerMatches : temporalOwner = target
  maintenanceOwner : CarrierId
  maintenanceOwnerMatches : maintenanceOwner = target

/-- Exactly eight clause indices are inherited from `ClauseId`; C6 is a
    separately supplied temporal field and is not made sufficient for C1-C5 or C7-C8. -/
structure EightClauseIntegratedPackage
    {Coord Value : Type}
    (target : CarrierId)
    (tree : RootedJoinTree ClauseId Coord)
    (localAssignment : ClauseId → Coord → Value)
    (accepted hardGate : ClauseId → Prop) where
  structural : IntegratedPackageWitness tree localAssignment accepted hardGate
  temporal : TemporalSubstance target
  packageOwner : CarrierId
  packageOwnerMatches : packageOwner = target

/-- Reading the structural field does not discharge temporal substance. -/
theorem structuralPackageDoesNotEraseTemporalField
    {Coord Value : Type}
    {target : CarrierId}
    {tree : RootedJoinTree ClauseId Coord}
    {localAssignment : ClauseId → Coord → Value}
    {accepted hardGate : ClauseId → Prop}
    (package : EightClauseIntegratedPackage target tree localAssignment accepted hardGate) :
    (∃ witness : IntegratedPackageWitness tree localAssignment accepted hardGate,
      witness = package.structural) ∧
    (∃ temporal : TemporalSubstance target, temporal = package.temporal) := by
  exact ⟨⟨package.structural, rfl⟩, ⟨package.temporal, rfl⟩⟩

end CSTTT.PackageTheory
