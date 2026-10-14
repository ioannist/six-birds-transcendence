import CSTTT.Targets.ComputedFIACH.Assembly

/-! Named-readout regressions for the pending full generic lineage adapter.
A missing atomic table rejects the readout itself, not just a sufficient gate.
The gate and readout are intentionally NOT identified: the empty-interface
control below has the old named readout but fails the old C6-dependent gate.
The final adapter therefore needs two separate arbitrary-partial equivalences.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04LineageBoundary
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH
open CSTTT.TransportTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192

/-- This deletes the actual shared atomic table, through the staged namespace.
It cannot produce the first constructed corridor witness of the named readout. -/
theorem missing_atomic_readout_rejected (m : RawLaneModel) :
    ¬ StrictTemporalLineage {m with assignment := put m.assignment (swapCell .eventTable) none} := by
  intro h
  obtain ⟨a,ha,_⟩ := h.1 .a (by decide)
  have hn := acquisition_missing_dependency m .eventTable (by decide)
  rw [hn] at ha
  contradiction

/-- A raw assignment mutation, not a replacement predicate. The interface
cell is checked by package C6; it is not read by assignmentRawBridge. -/
def emptyInterface : RawLaneModel :=
  {baseline with assignment := put canonical .interface (some [])}

theorem unchanged_bridge : assignmentRawBridge emptyInterface = assignmentRawBridge baseline := rfl

theorem empty_interface_readout : StrictTemporalLineage emptyInterface := by
  refine ⟨fun r hr => acquisition_corridor_constructs _ (by unfold AcquisitionCorridorPass; decide +kernel) r hr,?_,?_,?_⟩
  · rw [unchanged_bridge]
    exact acquisition_bridge_frozen baseline baseline_full_assignment_bridge
  · unfold TypedAcquisitionEndpointPass
    decide +kernel
  · rw [unchanged_bridge]
    exact lineage_route_status baseline baseline_lineage_lane

theorem empty_interface_gate_rejected : ¬ LineageLane emptyInterface := by
  intro h
  have hb := (lineage_checked_parts _ h).2.1
  have hc := (acquisition_bridge_checked_parts _ hb).2.2.2.2.2.2.2.2.2.2 .target
  have hi := hc.1.2.2.2.2.1
  change ([] : List FutureObservable) = futureInterface at hi
  contradiction

theorem readout_does_not_imply_gate :
    ¬ (∀ m : RawLaneModel, StrictTemporalLineage m → LineageLane m) := by
  intro h
  exact empty_interface_gate_rejected (h emptyInterface empty_interface_readout)

end CSTTT.TargetTheory.GenericHandoff.POS04LineageBoundary
