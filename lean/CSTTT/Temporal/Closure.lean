import CSTTT.Core.Carrier
import CSTTT.Temporal.Signature

namespace CSTTT

/-- Carrier-local temporal semantics: order, ticks, progress, record, and maintenance. -/
structure TemporalClosureSpec (c : Carrier) (a : TemporalAlphabet) where
  signature : c.State → TemporalSignature a
  successor : c.State → c.State → Prop
  viableTick : c.State → Prop
  tickProgress : c.State → c.State → Prop
  recordPreorder : a.recordType → a.recordType → Prop
  endogenousRecordUpdate : c.State → c.State → Prop
  maintenanceResources : c.State → List ResourceId

/-- Evidence that a particular carrier state realizes the declared temporal package. -/
structure TemporalClosureWitness
    (c : Carrier) (a : TemporalAlphabet) (spec : TemporalClosureSpec c a) where
  state : c.State
  orderStable : Prop
  tickViable : spec.viableTick state
  genuineProgress : ∃ next : c.State, spec.successor state next ∧ spec.tickProgress state next
  arrowInternal : Prop
  recordAuditable : Prop
  ownerMatches : (spec.signature state).owner = c.id
  maintenanceOwned : Prop

/-- Structural realization only; no phenomenal interpretation is included. -/
def TemporalRealizedAt
    (c : Carrier) (a : TemporalAlphabet) (spec : TemporalClosureSpec c a) (x : c.State) : Prop :=
  ∃ w : TemporalClosureWitness c a spec, w.state = x

end CSTTT
