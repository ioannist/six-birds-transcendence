import CSTTT.Core.Finite

namespace CSTTT

structure CarrierId where
  code : Nat
  deriving DecidableEq, Repr

structure ResourceId where
  code : Nat
  deriving DecidableEq, Repr

/-- A carrier has an independently named identity and an explicit finite state presentation. -/
structure Carrier where
  id : CarrierId
  State : Type
  stateEnum : FiniteEnum State

/-- Source and target are separately typed carriers and are distinct before any verdict. -/
structure CarrierPair where
  source : Carrier
  target : Carrier
  distinct : source.id ≠ target.id

structure OwnedResource where
  resource : ResourceId
  owner : CarrierId
  deriving DecidableEq, Repr

end CSTTT
