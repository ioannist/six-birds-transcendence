import CSTTT.Targets.ComputedFIACH.LineagePackage

/-! G6 four-snapshot seam. G6_lane_spec.md:115–139 and G6b CR1 retain
both routes at afterFirst AND endpoint. Each run, code, observer, future,
and finite alphabet is defined from the one staged assignment. No snapshot,
future model or positive bridge is supplied to the gate. The canonical G1c
adapter equations below are readout equalities, not positive-only conjuncts.
This module does not yet prove all RawBridge factor/record/route laws. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
local instance : DecidableEq (BridgeRunObservation pos04SnapshotBridge) :=
  bridgeRunObservationDecEq pos04SnapshotBridge

def acquisitionSnapshotIndices : List SnapshotIndex :=
  routeIds.flatMap fun r => snapshotPositions.map (r, ·)

/-- Copy raw wheel coordinates, not a stored class; the frozen receiver has
one content operation. Its near-automatic class mapping remains disclosed. -/
def acquisitionReceiver (a : Assignment) (h : HistoryId) : Option KState :=
  let d := (runInputs6 a .target).base
  if active7 d then
    match d.receiver.contentRule with
    | .copyTerminalPositionPhase => (d.histories h).getLast?
  else none

def acquisitionTargetHistory (a : Assignment) (h : HistoryId) : List KState :=
  let d := (runInputs6 a .source).base
  match acquisitionReceiver a h with
  | none => []
  | some s => (d.histories h).dropLast ++ [s]

def acquisitionHistory (a : Assignment) (t : Tag) (r : RouteId) : List KState :=
  match (runInputs6 a .source).base.routes.find? (fun v => v.id == r) with
  | none => []
  | some v => match t with
    | .source => (runInputs6 a .source).base.histories v.sourceHistory
    | .target => acquisitionTargetHistory a v.sourceHistory

def acquisitionPrefixTicks (a : Assignment) (t : Tag) (path : List KState) (n : Nat) : Nat :=
  let d := runInputs6 a t
  let pathPrefix := path.take (n+1)
  (pathPrefix.zip (pathPrefix.drop 1)).foldl (fun count pair =>
    count + d.ticks pair.1 (d.base.base.policy pair.1)) 0

/-- Run counters are actual history occurrences; they are never capped.
The full future retains unbounded counters after these finite audit roots. -/
def acquisitionSnapshotRun (a : Assignment) (t : Tag) (i : SnapshotIndex) : Run6 :=
  let path := acquisitionHistory a t i.1
  let n := snapshotOccurrence i.2
  let residue := (routeTuple (runInputs6 a t).base i.1).getD ([],[])
  ⟨.inK (path.getD n .p0w0),n,acquisitionPrefixTicks a t path n,residue,
    available8 (clause8 a t) t⟩
def acquisitionSnapshotObservation (a : Assignment) (t : Tag) (i : SnapshotIndex) :=
  (future6 a t).observe (acquisitionSnapshotRun a t i)
def acquisitionSnapshotReadout (a : Assignment) (t : Tag) (i : SnapshotIndex) :=
  frozenObservation6 (acquisitionSnapshotObservation a t i)

def acquisitionSnapshotMaps : SnapshotRawMaps CSTTT.POS04.PredictiveNow CSTTT.POS04.PredictiveNow
    (List KState × List EventId) Bool :=
  ⟨id,id,id,id,id,id,id,fun owner =>
    if owner = tagCarrierId .source then tagCarrierId .target else tagCarrierId .source⟩

/-- Reference checks and finite row bisimulation are the existing assigned C6
rules; snapshot equations check every one of the four raw contexts, including
intermediate ticks, record, maintenance and owner. Missing contexts reject. -/
def acquisitionSnapshotCheck (m : RawLaneModel) : Bool :=
  match checkedAcquisition m with
  | none => false
  | some a =>
    decide (C6Accept a .source ∧ C6Accept a .target) &&
    acquisitionSnapshotIndices.all (fun i =>
      let source := acquisitionHistory a .source i.1
      let target := acquisitionHistory a .target i.1
      let n := snapshotOccurrence i.2
      decide (n < source.length ∧ n < target.length) &&
      decide (mapSnapshotReadout acquisitionSnapshotMaps (acquisitionSnapshotReadout a .source i) =
        acquisitionSnapshotReadout a .target i))

def AcquisitionSnapshotPass (m : RawLaneModel) := acquisitionSnapshotCheck m = true

def acquisitionFrozenSignature (a : Assignment) (t : Tag)
    (i : Audited acquisitionSnapshotIndices) :
    CSTTT.TemporalSignature (snapshotAlphabet acquisitionSnapshotIndices (acquisitionSnapshotReadout a t)) :=
  frozenSnapshot (future6 a t) acquisitionSnapshotIndices (acquisitionSnapshotReadout a t) i

theorem acquisition_snapshot_roundtrip (a : Assignment) (t : Tag)
    (i : Audited acquisitionSnapshotIndices) :
    decodeFrozenSnapshot acquisitionSnapshotIndices (acquisitionSnapshotReadout a t)
      (acquisitionFrozenSignature a t i) = acquisitionSnapshotReadout a t i := rfl

theorem acquisition_snapshot_future (m : RawLaneModel) (h : AcquisitionSnapshotPass m) :
    ∃ a, checkedAcquisition m = some a ∧
      FullFutureSufficient (future6 a .source) ∧ FullFutureSufficient (future6 a .target) ∧
      SnapshotMapCheck acquisitionSnapshotIndices (acquisitionSnapshotReadout a .source)
        (acquisitionSnapshotReadout a .target) acquisitionSnapshotMaps := by
  unfold AcquisitionSnapshotPass acquisitionSnapshotCheck at h
  split at h
  · contradiction
  · rename_i a ha
    obtain ⟨hc,hs⟩ := Bool.and_eq_true_iff.mp h
    have hp : C6Accept a .source ∧ C6Accept a .target := of_decide_eq_true hc
    refine ⟨a,ha,c6_accept_sufficient hp.1,c6_accept_sufficient hp.2,?_⟩
    intro i hi
    have hx := List.all_eq_true.mp hs i hi
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hx).2

theorem acquisition_snapshots_missing_dependency (m : RawLaneModel) (k : Cell)
    (hk : k ∈ acquisitionDependencies) :
    ¬ AcquisitionSnapshotPass {m with assignment := put m.assignment (swapCell k) none} := by
  simp [AcquisitionSnapshotPass,acquisitionSnapshotCheck,acquisition_missing_dependency m k hk]

/-- Actual full-interface readouts equal G1c on BOTH tags at ALL FOUR
snapshots. These equalities are not used as fixed predicates under mutations. -/
theorem canonical_acquisition_snapshot_G1c (t : Tag) (i : SnapshotIndex) :
    acquisitionSnapshotObservation canonical t i =
      pos04FullFuture.observe (if t = .source then pos04SourceSnapshotRun i else pos04TargetSnapshotRun i) := by
  rcases i with ⟨r,p⟩
  cases t <;> cases r <;> cases p <;> decide

theorem baseline_acquisition_snapshots : AcquisitionSnapshotPass baseline := by
  unfold AcquisitionSnapshotPass acquisitionSnapshotCheck
  rw [baseline_acquisition]
  decide

theorem package_deletion_acquisition_snapshots : AcquisitionSnapshotPass packageDeletion := by
  unfold AcquisitionSnapshotPass acquisitionSnapshotCheck
  rw [package_deletion_acquisition]
  decide

theorem lineage_deletion_acquisition_snapshots : AcquisitionSnapshotPass lineageDeletion := by
  unfold AcquisitionSnapshotPass acquisitionSnapshotCheck
  have hc : checkedAcquisition lineageDeletion = some (image lineageDeletion.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image lineageDeletion.assignment) := by decide
    simp [h]
  rw [hc,lineage_staged_assignment]
  decide

theorem withdrawal_deletion_acquisition_snapshots : AcquisitionSnapshotPass withdrawalDeletion := by
  unfold AcquisitionSnapshotPass acquisitionSnapshotCheck
  rw [withdrawal_deletion_acquisition]
  decide

theorem reversed_histories_acquisition_snapshots : AcquisitionSnapshotPass reversedHistories := by
  unfold AcquisitionSnapshotPass acquisitionSnapshotCheck
  have hc : checkedAcquisition reversedHistories = some (image reversedHistories.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image reversedHistories.assignment) := by decide
    simp [h]
  rw [hc]
  decide

/-- Exact typed transport in the FROZEN target signature type, not merely
equality of a parallel eight-component display. The two sufficiency
propositions are proved from their own defined assignment dynamics. -/
theorem acquisition_snapshot_typed_transport (m : RawLaneModel)
    (h : AcquisitionSnapshotPass m) :
    ∃ a, checkedAcquisition m = some a ∧
      ∃ hc : SnapshotMapCheck acquisitionSnapshotIndices (acquisitionSnapshotReadout a .source)
          (acquisitionSnapshotReadout a .target) acquisitionSnapshotMaps,
        ∀ i : Audited acquisitionSnapshotIndices,
          transportFrozenSnapshot acquisitionSnapshotIndices (acquisitionSnapshotReadout a .source)
            (acquisitionSnapshotReadout a .target) acquisitionSnapshotMaps hc
            (acquisitionFrozenSignature a .source i) = acquisitionFrozenSignature a .target i := by
  obtain ⟨a,ha,hs,ht,hc⟩ := acquisition_snapshot_future m h
  refine ⟨a,ha,hc,?_⟩
  intro i
  have he := frozen_snapshot_transport (future6 a .source) acquisitionSnapshotIndices
    (acquisitionSnapshotReadout a .source) (acquisitionSnapshotReadout a .target)
    acquisitionSnapshotMaps hc i
  change transportFrozenSnapshot _ _ _ _ _ (frozenSnapshot _ _ _ _) = _
  rw [he]
  have hp : FullFutureSufficient (future6 a .source) = FullFutureSufficient (future6 a .target) :=
    propext ⟨fun _ => ht,fun _ => hs⟩
  simp only [acquisitionFrozenSignature,frozenSnapshot,TemporalSignature.mk.injEq,
    CSTTT.PredictiveNow.mk.injEq]
  simp only [hp,eq_self,and_true]

/-- Per-field closure sensitivity remains about the assignment's defined
readouts; a capped proposal is not an input to any acceptance function. -/
theorem acquisition_each_readout_guard (t : Tag) (f : Field6) :
    ¬ ProposedReadoutAgrees6 canonical t f (cappedReadout6 canonical t f) :=
  canonical_each_readout6_guard t f

/-- Missing one history occurrence cannot be certified via getD's default. -/
def truncatedAcquisitionHistories : RawLaneModel :=
  {baseline with assignment := mapCell canonical .histories (fun hs id => (hs id).take 1)}

theorem truncated_acquisition_snapshots_reject : ¬ AcquisitionSnapshotPass truncatedAcquisitionHistories := by
  unfold AcquisitionSnapshotPass acquisitionSnapshotCheck
  have hc : checkedAcquisition truncatedAcquisitionHistories =
      some (image truncatedAcquisitionHistories.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image truncatedAcquisitionHistories.assignment) := by decide
    simp [h]
  rw [hc]
  decide

theorem source_absent_acquisition_snapshots_reject : ¬ AcquisitionSnapshotPass sourceAbsent := by
  unfold AcquisitionSnapshotPass acquisitionSnapshotCheck
  have hc : checkedAcquisition sourceAbsent = some (image sourceAbsent.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image sourceAbsent.assignment) := by decide
    simp [h]
  rw [hc]
  decide

end CSTTT.TargetTheory.ComputedFIACH
