import CSTTT.Core.Carrier

namespace CSTTT

abbrev Stage (n : Nat) := Fin (n + 1)

structure Event (n : Nat) where
  id : Nat
  owner : CarrierId
  stage : Stage n
  deriving DecidableEq, Repr

/-- Operational dependencies point strictly forward in the declared stage order. -/
structure Dependency (n : Nat) where
  parent : Event n
  child : Event n
  before : parent.stage.val < child.stage.val

/-- Operational episode data contain no lineage field. -/
structure Episode (n : Nat) where
  source : CarrierId
  target : CarrierId
  distinct : source ≠ target
  events : List (Event n)
  dependencies : List (Dependency n)
  activeSupport : Stage n → List CarrierId

namespace Episode

variable {n : Nat}

def sourceOnly (e : Episode n) (k : Stage n) : Prop :=
  e.activeSupport k = [e.source]

def targetOnly (e : Episode n) (k : Stage n) : Prop :=
  e.activeSupport k = [e.target]

def noGap (e : Episode n) : Prop :=
  ∀ k : Stage n, e.activeSupport k ≠ []

def mixedAt (e : Episode n) (k : Stage n) : Prop :=
  e.source ∈ e.activeSupport k ∧ e.target ∈ e.activeSupport k

def sourceAbsentAfter (e : Episode n) (k : Stage n) : Prop :=
  ∀ j : Stage n, k.val ≤ j.val → e.source ∉ e.activeSupport j

end Episode

end CSTTT
