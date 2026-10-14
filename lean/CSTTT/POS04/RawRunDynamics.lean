import CSTTT.POS04.C6
import CSTTT.Transport.FutureDynamics

/-! Raw POS-04 action-row pushforward and counter/ledger updates owned by
the bridge. Definitions moved unchanged from FutureDynamics to avoid an
import cycle; no new model data or verdicts. -/
namespace CSTTT.POS04
open CSTTT.TransportTheory CSTTT.Objecthood.T1Audit

inductive SnapshotPosition where
  | afterFirst | endpoint
  deriving DecidableEq, Repr

def snapshotPositions : List SnapshotPosition := [.afterFirst, .endpoint]
def snapshotOccurrence : SnapshotPosition → Nat
  | .afterFirst => 1 | .endpoint => 2
def snapshotEvent : SnapshotPosition → EventId
  | .afterFirst => .mix1 | .endpoint => .mix2
abbrev SnapshotIndex := RouteId × SnapshotPosition

def rawFutureBudget (_ : C6State) : Nat := ledger.initialBudget

def rawFutureBudgetAfter (x : C6State) : Nat :=
  rawFutureBudget x - ledger.actionCost + ledger.rechargePerAction

/-- The exact raw action-row probability aggregated by M, including exits. -/
def pos04RawFutureRow (x : C6State) (a : Action) (c : OutcomeClass) : Rat :=
  if x.funded && rechargeAvailableAfterWithdrawal x.tag then
    (classMass x.tag x.factor a c : Rat) / 4 else 0

/-- Raw updates, separately stated from the candidate model's successor. -/
def pos04RawFutureUpdate (x : C6State) (a : Action) (c : OutcomeClass) : C6State :=
  { x with
    factor := classRepresentative c
    eventCount := x.eventCount + 1
    tickCount := x.tickCount + (match x.factor with
      | .inK s => tickIncrement x.tag s a
      | .p2w0 | .p5w1 => 0)
    funded := x.funded && decide (rawFutureBudgetAfter x > 0) }

def pos04RawFutureDynamics : RawFutureDynamics C6State Action OutcomeClass where
  outcomes := outcomeClasses
  actionRow := pos04RawFutureRow
  update := pos04RawFutureUpdate


end CSTTT.POS04
