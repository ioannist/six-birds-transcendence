import CSTTT.POS04.Assigned.C6Guards
import CSTTT.POS04.FrozenSnapshots
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

/-- Total eight-field embedding: unlike the active-only snapshot decoder,
future exits remain distinct and the Tag owner is translated to its carrier id. -/
def frozenObservation6 (o : C6Observation) : BridgeRunObservation pos04SnapshotBridge :=
  ⟨o.predictive,o.eventOrder,o.tickPhase,o.cumulativeProgress,o.endogenousRecordCount,
    o.routeResidue,o.maintenanceState,tagCarrierId o.owner⟩

theorem frozenObservation6_injective : ∀ x y, frozenObservation6 x = frozenObservation6 y → x = y := by
  intro x y h
  have hp := congrArg TemporalSnapshotReadout.predictive h
  have hn := congrArg TemporalSnapshotReadout.order h
  have ht := congrArg TemporalSnapshotReadout.tickPhase h
  have hg := congrArg TemporalSnapshotReadout.progress h
  have hw := congrArg TemporalSnapshotReadout.record h
  have hr := congrArg TemporalSnapshotReadout.residue h
  have hf := congrArg TemporalSnapshotReadout.maintenance h
  have ho := congrArg TemporalSnapshotReadout.owner h
  have htag : x.owner = y.owner := by
    exact tag_carrier_id_injective _ _ ho
  cases x; cases y
  simp only [frozenObservation6] at hp hn ht hg hw hr hf
  cases hp; cases hn; cases ht; cases hg; cases hw; cases hr; cases hf; cases htag
  rfl

theorem frozen_observation6_link (x : C6State) :
    bridgeRunObservation pos04SnapshotBridge x = frozenObservation6 (observe .positive x) := by
  cases ht : x.tag <;> rfl

theorem frozen_weight6_link (x : C6State) (act : Action) (o : OutcomeClass) :
    (bridgeFutureModel pos04SnapshotBridge).weight x act o = pos04FullFuture.weight x act o := by
  change (bridgeRunDynamics pos04SnapshotBridge).actionRow x act o = _
  rw [pos04_snapshot_bridge_reference_eq]
  exact (pos04_raw_future_weight_link x act o).symm

theorem frozen_next6_link (x : C6State) (act : Action) (o : OutcomeClass) :
    (bridgeFutureModel pos04SnapshotBridge).next x act o = pos04FullFuture.next x act o := by
  change (bridgeRunDynamics pos04SnapshotBridge).update x act o = _
  rw [pos04_snapshot_bridge_reference_eq]
  exact (pos04_raw_future_successor_link x act o).symm

/-- Exact equality with G1c's bridge-owned future, with the owner type
translated injectively and every trace component retained. -/
theorem legacy_frozen_word_law6 (x : C6State) (word : List Action) (trace : List C6Observation) :
    fullFuture pos04FullFuture x word trace =
      bridgeFuture pos04SnapshotBridge x word (trace.map frozenObservation6) := by
  letI := bridgeRunObservationDecEq pos04SnapshotBridge
  change _ = fullFuture (bridgeFutureModel pos04SnapshotBridge) x word _
  induction word generalizing x trace with
  | nil =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      simp only [fullFuture,List.map_cons,List.cons.injEq,List.map_eq_nil_iff]
      change (if first = observe .positive x ∧ tail = [] then 1 else 0) =
        (if frozenObservation6 first = bridgeRunObservation pos04SnapshotBridge x ∧ tail = [] then 1 else 0)
      rw [frozen_observation6_link]
      have he : frozenObservation6 first = frozenObservation6 (observe .positive x) ↔ first = observe .positive x :=
        ⟨frozenObservation6_injective _ _,congrArg frozenObservation6⟩
      simp only [he]
  | cons act rest ih =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      simp only [fullFuture,List.map_cons]
      change (if first = observe .positive x then
        (outcomeClasses.map fun o => pos04FullFuture.weight x act o *
          fullFuture pos04FullFuture (pos04FullFuture.next x act o) rest tail).sum else 0) =
        (if frozenObservation6 first = bridgeRunObservation pos04SnapshotBridge x then
        (outcomeClasses.map fun o => (bridgeFutureModel pos04SnapshotBridge).weight x act o *
          fullFuture (bridgeFutureModel pos04SnapshotBridge)
            ((bridgeFutureModel pos04SnapshotBridge).next x act o) rest (tail.map frozenObservation6)).sum else 0)
      rw [frozen_observation6_link]
      have he : frozenObservation6 first = frozenObservation6 (observe .positive x) ↔ first = observe .positive x :=
        ⟨frozenObservation6_injective _ _,congrArg frozenObservation6⟩
      simp only [he,frozen_weight6_link,frozen_next6_link]
      by_cases hh : first = observe .positive x
      · simp only [hh,if_true]
        congr 1
        apply List.map_congr_left
        intro o _
        rw [ih]
      · simp only [hh,if_false]

theorem canonical_word_law6_G1c (tag : Tag) (x : Run6) (word : List Action) (trace : List C6Observation) :
    fullFuture (future6 canonical tag) x word trace =
      bridgeFuture pos04SnapshotBridge (legacyRun6 tag x) word (trace.map frozenObservation6) :=
  (canonical_word_law6 tag x word trace).trans (legacy_frozen_word_law6 _ _ _)

end CSTTT.POS04.Assigned
