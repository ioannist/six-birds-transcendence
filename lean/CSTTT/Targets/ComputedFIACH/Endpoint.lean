import CSTTT.Targets.ComputedFIACH.BridgeCoherence

/-! G6_lane_spec.md:125–139: typed receiver/corridor exit link, from the
same checked staged cells. Terminal classes are computed, not stored. The
coordinate-copy operation and designed route readout remain near-automatic;
this module does not claim independent physical corroboration. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory CSTTT.CorridorTheory.AtomicChain
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192

def typedAcquisitionEndpointAt (m : RawLaneModel) (a : Assignment) (r : RouteId) : Bool :=
  let ds := runInputs6 a .source
  let dt := runInputs6 a .target
  match routeTuple ds.base r,routeTuple dt.base r with
  | some (hist,path),some targetTuple =>
    match hist.getLast?,path.getLast? with
    | some s,some eid =>
      match event6 dt eid with
      | none => false
      | some e =>
        decide (targetTuple = (hist,path)) && active7 dt.base && phase2Check m r &&
        decide (acquisitionReceiver a (assignedRouteHistory a r) = some s) &&
        decide ((acquisitionTargetHistory a (assignedRouteHistory a r)).getLast? = some s) &&
        decide (predictive dt.base.base s = predictive ds.base.base s) &&
        decide (e.toStage = .targetExit) && e.targetSupport && !e.sourceSupport &&
        strictEvent6 dt e && decide (e.toStage ∈ dt.base.realized) &&
        decide (ds.resource.owner = .source) && decide (dt.resource.owner = .target) &&
        decide ((acquisitionAtomicLeg m a r).target = atomicCarrierCode .target) &&
        decide ((acquisitionAtomicLeg m a r).source = atomicCarrierCode .source) &&
        decide ((acquisitionAtomicLeg m a r).stages.getLast?.map (fun v => v.frontier.predictive) =
          some (acquisitionClass a r))
    | _,_ => false
  | _,_ => false

def typedAcquisitionEndpointCheck (m : RawLaneModel) : Bool :=
  match checkedAcquisition m with
  | none => false
  | some a => routeIds.all (typedAcquisitionEndpointAt m a)
def TypedAcquisitionEndpointPass (m : RawLaneModel) := typedAcquisitionEndpointCheck m = true

instance (m : RawLaneModel) : Decidable (RouteIndexed (assignmentRawBridge m)) := by
  unfold RouteIndexed RoutePairDomain
  dsimp only [assignmentRawBridge]
  infer_instance

def lineageLaneCheck (m : RawLaneModel) : Bool :=
  acquisitionCorridorCheck m && acquisitionBridgeCheck m && typedAcquisitionEndpointCheck m &&
    decide (RouteIndexed (assignmentRawBridge m))
def LineageLane (m : RawLaneModel) := lineageLaneCheck m = true

/-- Status is derived from a supported, nonempty, shared-endpoint comparison;
no absent comparison is declared flat. -/
theorem lineage_route_status (m : RawLaneModel) (h : LineageLane m) :
    routeStatusOfRaw (assignmentRawBridge m) = .routeIndexed := by
  unfold LineageLane lineageLaneCheck at h
  have hr : RouteIndexed (assignmentRawBridge m) := of_decide_eq_true (Bool.and_eq_true_iff.mp h).2
  simp [routeStatusOfRaw,hr]

theorem lineage_checked_parts (m : RawLaneModel) (h : LineageLane m) :
    AcquisitionCorridorPass m ∧ AcquisitionBridgePass m ∧ TypedAcquisitionEndpointPass m := by
  obtain ⟨hrest,_⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hcb,he⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hc,hb⟩ := Bool.and_eq_true_iff.mp hcb
  exact ⟨hc,hb,he⟩

theorem baseline_lineage_lane : LineageLane baseline := by
  unfold LineageLane lineageLaneCheck
  rw [show acquisitionCorridorCheck baseline = true from baseline_acquisition_corridor,
    show acquisitionBridgeCheck baseline = true from baseline_full_assignment_bridge]
  unfold typedAcquisitionEndpointCheck
  rw [baseline_acquisition]
  decide +kernel

theorem package_deletion_lineage_lane : LineageLane packageDeletion := by
  unfold LineageLane lineageLaneCheck
  rw [show acquisitionCorridorCheck packageDeletion = true from package_deletion_acquisition_corridor,
    show acquisitionBridgeCheck packageDeletion = true from package_deletion_full_assignment_bridge]
  unfold typedAcquisitionEndpointCheck
  rw [package_deletion_acquisition]
  decide +kernel

theorem lineage_deletion_not_lineage_lane : ¬ LineageLane lineageDeletion := by
  intro h
  exact lineage_deletion_acquisition_corridor (lineage_checked_parts lineageDeletion h).1

theorem withdrawal_deletion_lineage_lane : LineageLane withdrawalDeletion := by
  unfold LineageLane lineageLaneCheck
  rw [show acquisitionCorridorCheck withdrawalDeletion = true from withdrawal_deletion_acquisition_corridor,
    show acquisitionBridgeCheck withdrawalDeletion = true from withdrawal_deletion_full_assignment_bridge]
  unfold typedAcquisitionEndpointCheck
  rw [withdrawal_deletion_acquisition]
  decide +kernel

theorem reversed_histories_lineage_lane : LineageLane reversedHistories := by
  unfold LineageLane lineageLaneCheck
  rw [show acquisitionCorridorCheck reversedHistories = true from reversed_histories_corridor,
    show acquisitionBridgeCheck reversedHistories = true from reversed_histories_full_assignment_bridge]
  unfold typedAcquisitionEndpointCheck
  have hc : checkedAcquisition reversedHistories = some (image reversedHistories.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image reversedHistories.assignment) := by decide
    simp [h]
  rw [hc]
  decide +kernel

end CSTTT.TargetTheory.ComputedFIACH
