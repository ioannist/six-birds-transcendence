import CSTTT.Transport.RecordArrow

/-! TTH-10 raw-event replacement for the old `StrictlyMonotoneOn` schema.
The translation equation and positive increment are independently checkable
on raw records; neither premise contains `TargetArrow`. -/
namespace CSTTT.RecordTheory

structure RawRecordTransport (SourceEvent TargetEvent : Type) where
  sourceEdges : List (SourceEvent × SourceEvent)
  targetEdges : List (TargetEvent × TargetEvent)
  mapEvent : SourceEvent → TargetEvent
  sourceRecord : SourceEvent → Nat
  targetRecord : TargetEvent → Nat
  translate : Nat → Nat
  increment : SourceEvent → SourceEvent → Nat

def SourceArrow {S T : Type} (m : RawRecordTransport S T) (a b : S) : Prop :=
  (a,b) ∈ m.sourceEdges ∧ m.sourceRecord a < m.sourceRecord b

def TargetArrow {S T : Type} (m : RawRecordTransport S T) (a b : T) : Prop :=
  (a,b) ∈ m.targetEdges ∧ m.targetRecord a < m.targetRecord b

/-- A supported edge maps to a supported edge, and record readouts commute
with a numerical translation. No target strictness is assumed. -/
def RecordMapStepLaw {S T : Type} (m : RawRecordTransport S T) : Prop :=
  (∀ a b, (a,b) ∈ m.sourceEdges →
    (m.mapEvent a,m.mapEvent b) ∈ m.targetEdges) ∧
  (∀ a, m.targetRecord (m.mapEvent a) = m.translate (m.sourceRecord a))

/-- This raw arithmetic law is independent of target-edge strictness. -/
def PositiveRecordIncrement {S T : Type} (m : RawRecordTransport S T) : Prop :=
  ∀ a b, SourceArrow m a b →
    m.translate (m.sourceRecord b) =
      m.translate (m.sourceRecord a) + m.increment a b ∧
    0 < m.increment a b

/-- TTH-10: target strictness follows from support, commuting readouts, and
an independently checked positive numerical increment. -/
theorem monotoneRecordDescentTransportsArrow_generic
    {S T : Type} (m : RawRecordTransport S T)
    (heq : RecordMapStepLaw m) (hinc : PositiveRecordIncrement m) :
    ∀ a b, SourceArrow m a b → TargetArrow m (m.mapEvent a) (m.mapEvent b) := by
  intro a b hab
  have hpositive := hinc a b hab
  refine ⟨heq.1 a b hab.1, ?_⟩
  rw [heq.2 a, heq.2 b, hpositive.1]
  omega

/-- The control rule copies a two-event edge but erases both target records
to zero. Its weak monotonicity is computed, while its strict arrow fails. -/
def weakCollapseControl : RawRecordTransport Bool Bool where
  sourceEdges := [(false,true)]
  targetEdges := [(false,true)]
  mapEvent := id
  sourceRecord := fun b => if b then 1 else 0
  targetRecord := fun _ => 0
  translate := fun _ => 0
  increment := fun _ _ => 0

def WeakRecordMonotone {S T : Type} (m : RawRecordTransport S T) : Prop :=
  ∀ a b, m.sourceRecord a ≤ m.sourceRecord b →
    m.targetRecord (m.mapEvent a) ≤ m.targetRecord (m.mapEvent b)

theorem weakRecordMonotonicityInsufficient_generic :
    ∃ m : RawRecordTransport Bool Bool,
      WeakRecordMonotone m ∧
      SourceArrow m false true ∧
      ¬ TargetArrow m (m.mapEvent false) (m.mapEvent true) := by
  refine ⟨weakCollapseControl, ?_, ?_, ?_⟩
  · intro a b _
    simp [weakCollapseControl]
  · simp [SourceArrow, weakCollapseControl]
  · simp [TargetArrow, weakCollapseControl]

end CSTTT.RecordTheory
