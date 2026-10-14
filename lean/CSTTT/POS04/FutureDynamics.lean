import CSTTT.POS04.FullFutureBridge
import CSTTT.POS04.RawRunDynamics
import CSTTT.Transport.FutureDynamics

/-! The actual POS-04 C6 quotient dynamics (`audit/M3_model_spec.md:22,30-33`).
The action law is the pushforward of `actionRow` by the linked M classes;
it is not a uniform choice of classes. The successor is the declared class
representative, lifted with raw tick increments, event/progress/record count,
retained residue, owner and maintenance. This is the published C6 quotient
execution, not equality of a representative with each underlying microstate.

The funded ledger has constant budget one: cost one and recharge one. C6State
stores the funded bit, not a separate budget counter. Below we check its raw
budget update and its preservation on the entire unbounded future closure.
No claim about unmodeled variable budgets is made. -/
namespace CSTTT.POS04
open CSTTT.TransportTheory CSTTT.Objecthood.T1Audit

theorem pos04_raw_future_budget_equation (x : C6State) :
    rawFutureBudgetAfter x = rawFutureBudget x := by rfl

theorem pos04_raw_future_weight_link (x : C6State) (a : Action) (c : OutcomeClass) :
    pos04FullFuture.weight x a c = pos04RawFutureDynamics.actionRow x a c := by
  simp only [pos04FullFuture, effectiveMass, pos04RawFutureDynamics, pos04RawFutureRow]
  split
  · rfl
  · simp [Rat.div_def]

theorem pos04_raw_future_successor_link (x : C6State) (a : Action) (c : OutcomeClass) :
    pos04FullFuture.next x a c = pos04RawFutureDynamics.update x a c := by
  simp [pos04FullFuture, c6Next, c6Delta, c6Tick, pos04RawFutureDynamics,
    pos04RawFutureUpdate, rawFutureBudgetAfter, rawFutureBudget, ledger]
  rfl

/-- Global equations imply the required equations throughout every raw
future closure, independently of a snapshot bound. -/
theorem pos04_future_dynamics_check (roots : List C6State) :
    FutureDynamicsCheck pos04FullFuture pos04RawFutureDynamics roots :=
  ⟨rfl, fun x _ a c => ⟨pos04_raw_future_weight_link x a c,
    pos04_raw_future_successor_link x a c⟩⟩

theorem pos04_future_closure_ledger (roots : List C6State)
    (hr : ∀ x ∈ roots, x.funded = true) (x : C6State)
    (hx : FutureClosure pos04RawFutureDynamics roots x) :
    x.funded = true ∧ rawFutureBudget x = 1 ∧
      rawFutureBudgetAfter x = rawFutureBudget x := by
  induction hx with
  | root x hm => exact ⟨hr x hm, rfl, rfl⟩
  | step hx a c hm ih =>
      refine ⟨?_, rfl, rfl⟩
      simp [pos04RawFutureDynamics, pos04RawFutureUpdate, rawFutureBudgetAfter,
        rawFutureBudget, ledger, ih.1]

/-- Canonical probabilities used here are the same T1 factor proved in L4/L5. -/
theorem raw_future_canonical_factor_link (tag : Tag) (s t : KState) :
    rowWeight (actionRow tag s (canonicalAction s)) t = taggedPNum tag s t :=
  canonical_action_row_agrees_with_tagged_P tag s t

/-- Fixed conversion of the already-declared full C6 interface: only the
owner representation changes from Tag to its existing CarrierId. -/
def c6ObservationToBridge (o : C6Observation) :
    TemporalSnapshotReadout PredictiveNow (List KState × List EventId) Bool :=
  ⟨o.predictive, o.eventOrder, o.tickPhase, o.cumulativeProgress,
    o.endogenousRecordCount, o.routeResidue, o.maintenanceState, tagCarrierId o.owner⟩

def c6CodeToBridge (q : C6Code) :
    TemporalRunCode PredictiveNow (List KState × List EventId) Bool :=
  ⟨q.predictive, q.eventCount, q.tickPhase, q.routeResidue, q.maintenance,
    tagCarrierId q.owner⟩

theorem tag_carrier_id_injective (a b : Tag) (h : tagCarrierId a = tagCarrierId b) : a = b := by
  cases a <;> cases b
  · rfl
  · exact False.elim ((by decide : tagCarrierId .source ≠ tagCarrierId .target) h)
  · exact False.elim ((by decide : tagCarrierId .target ≠ tagCarrierId .source) h)
  · rfl

theorem c6_code_to_bridge_injective (a b : C6Code) (h : c6CodeToBridge a = c6CodeToBridge b) :
    a = b := by
  cases a with
  | mk p n t r m owner =>
    cases b with
    | mk p' n' t' r' m' owner' =>
      simp only [c6CodeToBridge, TemporalRunCode.mk.injEq] at h
      simp only [C6Code.mk.injEq]
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        tag_carrier_id_injective owner owner' h.2.2.2.2.2⟩

/-- Readout coherence holds everywhere, including beyond the finite audit.
This rules out an independently capped future event-order display. -/
theorem pos04_bridge_observation_eq_c6 (v : ReceiverVariant) (x : C6State) :
    bridgeRunObservation (pos04RawBridge v) x = c6ObservationToBridge (observe .positive x) := by
  cases ht : x.tag <;>
    simp [bridgeRunObservation, pos04RawBridge, c6ObservationToBridge, observe,
      rechargeAvailableAfterWithdrawal, ht]

theorem pos04_bridge_code_eq_c6 (v : ReceiverVariant) (x : C6State) :
    bridgeRunCode (pos04RawBridge v) x = c6CodeToBridge (q x) := rfl

theorem pos04_bridge_code_reflects_c6 (v : ReceiverVariant) (x y : C6State)
    (h : bridgeRunCode (pos04RawBridge v) x = bridgeRunCode (pos04RawBridge v) y) :
    q x = q y :=
  c6_code_to_bridge_injective _ _ h

/-- One-step bisimulation on the DEFINED bridge functions. This reuses the
L6a/G1b full-interface bisimulation, not a candidate-supplied code/observer. -/
theorem pos04_defined_future_bisim (v : ReceiverVariant) : BridgeFutureBisim (pos04RawBridge v) := by
  intro x y hc
  have hq := pos04_bridge_code_reflects_c6 v x y hc
  have hb := pos04_full_one_step_bisim x y hq
  refine ⟨?_, ?_⟩
  · change bridgeRunObservation (pos04RawBridge v) x = bridgeRunObservation (pos04RawBridge v) y
    have ho : observe .positive x = observe .positive y := hb.1
    rw [pos04_bridge_observation_eq_c6, pos04_bridge_observation_eq_c6, ho]
  · intro a o
    refine ⟨(hb.2 a o).1, ?_⟩
    change bridgeRunCode (pos04RawBridge v) (pos04RawFutureUpdate x a o) =
      bridgeRunCode (pos04RawBridge v) (pos04RawFutureUpdate y a o)
    have hx : c6Next .positive x a o = pos04RawFutureUpdate x a o :=
      pos04_raw_future_successor_link x a o
    have hy : c6Next .positive y a o = pos04RawFutureUpdate y a o :=
      pos04_raw_future_successor_link y a o
    rw [← hx, ← hy, pos04_bridge_code_eq_c6, pos04_bridge_code_eq_c6]
    exact congrArg c6CodeToBridge (hb.2 a o).2

/-- Raw readout laws are global, hence cover every future closure. Their
recipes come from M3 spec temporal/ledger/route rules (§ new fields 3,4 and
route memory); the post-exit register is retained, not appended.
The supported step is funded; zero-mass enumerated simulator steps follow
the same counter rule without claiming realized progress on an exit. -/
theorem pos04_bridge_readout_updates (v : ReceiverVariant) (x : C6State)
    (a : Action) (o : OutcomeClass) : BridgeReadoutUpdateAt (pos04RawBridge v) x a o := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro s hs
    cases ht : x.tag with
    | target => simp [pos04RawBridge, ht] at hs
    | source =>
      cases hf : x.factor with
      | inK k =>
        simp [pos04RawBridge, ht, hf] at hs
        subst s
        simp [pos04RawBridge, ht, hf, predictiveNow]
      | p2w0 => simp [pos04RawBridge, ht, hf] at hs
      | p5w1 => simp [pos04RawBridge, ht, hf] at hs
  · intro s hs
    cases ht : x.tag with
    | source => simp [pos04RawBridge, ht] at hs
    | target =>
      cases hf : x.factor with
      | inK k =>
        simp [pos04RawBridge, ht, hf] at hs
        subst s
        simp [pos04RawBridge, ht, hf, predictiveNow]
      | p2w0 => simp [pos04RawBridge, ht, hf] at hs
      | p5w1 => simp [pos04RawBridge, ht, hf] at hs
  · rfl
  · rfl
  · rfl
  · intro hn
    cases hf : x.factor with
    | inK s => simp [pos04RawBridge, hf, tickIncrement]
    | p2w0 => simp [pos04RawBridge, effectiveMass, classMass, c6Row, hf] at hn
    | p5w1 => simp [pos04RawBridge, effectiveMass, classMass, c6Row, hf] at hn
  · rfl
  · rfl
  · rfl
  · rfl
  · intro s hs
    cases ht : x.tag with
    | source => simp [pos04RawBridge, ht]
    | target => simp [pos04RawBridge, ht] at hs
  · intro s hs
    cases ht : x.tag with
    | target => simp [pos04RawBridge, ht]
    | source => simp [pos04RawBridge, ht] at hs
  · simp [pos04RawBridge, writerForResidue, c6Writer, recordWriterAvailable]
  · simp [pos04RawBridge, pos04RawFutureUpdate, writerForResidue, c6Writer, recordWriterAvailable]
  · simp [pos04RawBridge, rechargeAvailableAfterWithdrawal]
  · simp [pos04RawBridge, pos04RawFutureUpdate, rechargeAvailableAfterWithdrawal,
      rawFutureBudgetAfter, rawFutureBudget, ledger]
  · simp [pos04RawBridge, rechargeAvailableAfterWithdrawal, writerForResidue,
      c6Writer, recordWriterAvailable]
  · simp [pos04RawBridge, pos04RawFutureUpdate, rawFutureBudgetAfter, rawFutureBudget,
      ledger, writerForResidue, c6Writer, recordWriterAvailable]

end CSTTT.POS04
