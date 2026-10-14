import CSTTT.Targets.ComputedFIACH.Acquisition

/-! G6_lane_spec.md:104–145,213–241; G6b interpretation A2.
The atomic projection reads ONE checked staged assignment. Owned vertices are
expanded from the assigned event support bits; intervention deletion therefore
removes the actual source vertex. Stage geometry is the declared four-stage
interface (entry, two mixed stages, exit), not inferred from intervention bits.
Snapshot counters are path ordinals; no unbounded clock is truncated here.
The assigned C6 run functions remain the post-exit dynamics. This adapter is
only the corridor part of lineage, not the unfinished G1c bridge adapter. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.CorridorTheory.AtomicChain
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

instance (d : RunInputs6) (t : Tag) : Decidable (Trace6 d t) := by
  unfold Trace6
  infer_instance

/-- Read the raw register AFTER the funded step, according to L5's enumerated
rule. The phase probe is deliberately designed, as disclosed by G6b. -/
def acquisitionRouteRead (e : WithdrawalEntry) : Option Nat :=
  match routeReadout with
  | .firstSourcePhaseAfterFundedStep => e.register.1.head?.map (fun s => ambientPhase (.inK s))
def acquisitionRouteOutput (m : RawLaneModel) (r : RouteId) : Option Nat :=
  let reads := (phase2Entries m r).map acquisitionRouteRead
  if reads.isEmpty then none
  else if reads.all (fun x => some x == reads.head?) then reads.head?.join else none

def acquisitionAvailable (m : RawLaneModel) (a : Assignment) : Bool :=
  let ds := runInputs6 a .source
  let dt := runInputs6 a .target
  active7 dt.base && decide (Trace6 ds .source) && decide (Trace6 dt .target) &&
  available8 (clause8 a .source) .source && available8 (clause8 a .target) .target &&
  routeIds.all (phase2Check m) &&
  decide (routeReadoutOwner = .target) &&
  (acquisitionRouteOutput m .a).isSome && (acquisitionRouteOutput m .b).isSome &&
  decide (acquisitionRouteOutput m .a ≠ acquisitionRouteOutput m .b)

def acquisitionResidue (a : Assignment) (r : RouteId) (i : Nat) : List String :=
  match routeTuple (runInputs6 a .source).base r with
  | none => []
  | some (hist,path) => hist.map stateName ++ (path.take i).map eventName

def acquisitionClass (a : Assignment) (r : RouteId) : Nat :=
  let d := (runInputs6 a .source).base
  match routeTuple d r with
  | none => 0
  | some (hist,_) => ((kernel.map (predictive d.base)).eraseDups).idxOf (predictive d.base (hist.getLastD .p0w0))

def acquisitionStages (m : RawLaneModel) (a : Assignment) (r : RouteId) : List RawStage :=
  stages.mapIdx fun i stage =>
    ⟨atomicPosSupport i,
      decide (stage ∈ (runInputs6 a .target).base.realized) && acquisitionAvailable m a,
      ⟨acquisitionClass a r,i,i,i,i,acquisitionResidue a r i,
       if acquisitionAvailable m a then "funded" else "",atomicPosOwner i⟩⟩
def acquisitionEvents (a : Assignment) : List RawEvent :=
  ⟨"source_live",atomicCarrierCode .source,0⟩ ::
  (runInputs6 a .target).base.events.flatMap fun e =>
    (if e.sourceSupport then
      [⟨eventName e.id ++ "-source",atomicCarrierCode .source,stages.idxOf e.toStage⟩] else []) ++
    (if e.targetSupport then
      [⟨eventName e.id ++ "-target",atomicCarrierCode .target,stages.idxOf e.toStage⟩] else [])
def acquisitionEdges (a : Assignment) : List RawDependency :=
  (acquisitionEvents a).flatMap fun p =>
    ((acquisitionEvents a).filter (fun c => c.stage == p.stage + 1)).map (fun c => ⟨p.id,c.id⟩)
def acquisitionUpdates (a : Assignment) (r : RouteId) : List ReadoutUpdate :=
  match routeTuple (runInputs6 a .target).base r with
  | none => []
  | some (_,path) => path.mapIdx fun i id =>
    ⟨0,1,1,1,1,[eventName id],"funded",atomicPosOwner (i+1)⟩
def acquisitionAtomicLeg (m : RawLaneModel) (a : Assignment) (r : RouteId) : FiniteAtomicLeg where
  interventionMode := .mixedSupport
  source := atomicCarrierCode .source
  target := atomicCarrierCode .target
  stages := acquisitionStages m a r
  events := acquisitionEvents a
  dependencies := acquisitionEdges a
  updates := acquisitionUpdates a r
  base := default
  sourceContribution := default
  targetContribution := default
  sourceAudit := "mix_2-source"
  targetAudit := "mix_2-target"
  laterAudit := "exit-target"

/-- No caller-supplied view or positive adapter enters certification. -/
def acquisitionCorridorCheck (m : RawLaneModel) : Bool :=
  match checkedAcquisition m with
  | none => false
  | some a => routeIds.all (fun r => AtomicLegCheck (acquisitionAtomicLeg m a r))
def AcquisitionCorridorPass (m : RawLaneModel) := acquisitionCorridorCheck m = true

theorem acquisition_corridor_constructs (m : RawLaneModel)
    (h : AcquisitionCorridorPass m) (r : RouteId) (hr : r ∈ routeIds) :
    ∃ a, checkedAcquisition m = some a ∧
      StrictCorridorWitness [acquisitionAtomicLeg m a r] := by
  unfold AcquisitionCorridorPass acquisitionCorridorCheck at h
  split at h
  · contradiction
  · rename_i a he
    have hp : AtomicLegPass (acquisitionAtomicLeg m a r) := List.all_eq_true.mp h r hr
    refine ⟨a,he,strictTemporalCorridorComposition_generic _ ?_⟩
    refine ⟨by simp, ?_, ?_⟩
    · simpa [chainCheck,AtomicLegPass] using hp
    · change some (atomicCarrierCode .source) ≠ some (atomicCarrierCode .target)
      decide

theorem acquisition_corridor_missing_dependency (m : RawLaneModel) (k : Cell)
    (hk : k ∈ acquisitionDependencies) :
    ¬ AcquisitionCorridorPass {m with assignment := put m.assignment (swapCell k) none} := by
  simp [AcquisitionCorridorPass,acquisitionCorridorCheck,acquisition_missing_dependency m k hk]

theorem baseline_acquisition : checkedAcquisition baseline = some canonical := by
  unfold checkedAcquisition baseline
  rw [image_canonical]
  have hc : Complete acquisitionDependencies canonical := by decide
  simp [hc]

theorem baseline_atomic_adapter (r : RouteId) :
    acquisitionAtomicLeg baseline canonical r = pos04AtomicLeg r := by
  cases r <;> decide

theorem baseline_acquisition_corridor : AcquisitionCorridorPass baseline := by
  unfold AcquisitionCorridorPass acquisitionCorridorCheck
  rw [baseline_acquisition]
  apply List.all_eq_true.mpr
  intro r _
  rw [baseline_atomic_adapter]
  exact pos04_atomic_leg_pass r

/-- The support-only registered intervention deletes the real source audit
vertex; it does not depend on a fixed positive corridor predicate. -/
theorem lineage_deletion_atomic_audit (r : RouteId) :
    auditCheck (acquisitionAtomicLeg lineageDeletion (image lineageDeletion.assignment) r) = false := by
  cases r <;> decide

theorem lineage_deletion_acquisition_corridor : ¬ AcquisitionCorridorPass lineageDeletion := by
  have hc : checkedAcquisition lineageDeletion = some (image lineageDeletion.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image lineageDeletion.assignment) := by decide
    simp [h]
  unfold AcquisitionCorridorPass acquisitionCorridorCheck
  rw [hc]
  decide

/-- The first-occurrence predictive identifier is computed from actual rows,
positions and hazards; on the audited assignment it is the imported M. -/
theorem acquisition_predictive_M_link (t : Tag) (s : KState) :
    ((kernel.map (predictive (runInputs6 canonical t).base.base)).eraseDups).idxOf
      (predictive (runInputs6 canonical t).base.base s) = taggedMClass t s := by
  cases t <;> cases s <;> decide

theorem baseline_acquisition_route_outputs :
    acquisitionRouteOutput baseline .a = some 0 ∧
    acquisitionRouteOutput baseline .b = some 1 := by decide

theorem package_deletion_acquisition :
    checkedAcquisition packageDeletion = some (image packageDeletion.assignment) := by
  unfold checkedAcquisition
  have hc : Complete acquisitionDependencies (image packageDeletion.assignment) := by decide
  simp [hc]
theorem package_deletion_atomic_adapter (r : RouteId) :
    acquisitionAtomicLeg packageDeletion (image packageDeletion.assignment) r = pos04AtomicLeg r := by
  cases r <;> decide

theorem package_deletion_acquisition_corridor : AcquisitionCorridorPass packageDeletion := by
  unfold AcquisitionCorridorPass acquisitionCorridorCheck
  rw [package_deletion_acquisition]
  apply List.all_eq_true.mpr
  intro r _
  rw [package_deletion_atomic_adapter]
  exact pos04_atomic_leg_pass r

theorem withdrawal_deletion_acquisition :
    checkedAcquisition withdrawalDeletion = some canonical := baseline_acquisition

theorem withdrawal_deletion_atomic_adapter (r : RouteId) :
    acquisitionAtomicLeg withdrawalDeletion canonical r = pos04AtomicLeg r := by
  cases r <;> decide

theorem withdrawal_deletion_acquisition_corridor : AcquisitionCorridorPass withdrawalDeletion := by
  unfold AcquisitionCorridorPass acquisitionCorridorCheck
  rw [withdrawal_deletion_acquisition]
  apply List.all_eq_true.mpr
  intro r _
  rw [withdrawal_deletion_atomic_adapter]
  exact pos04_atomic_leg_pass r

theorem source_absent_acquisition_corridor : ¬ AcquisitionCorridorPass sourceAbsent := by
  unfold AcquisitionCorridorPass acquisitionCorridorCheck
  have hc : checkedAcquisition sourceAbsent = some (image sourceAbsent.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image sourceAbsent.assignment) := by decide
    simp [h]
  rw [hc]
  decide

/-- Regression control, not a model repair: exchange the two supported raw
past histories. Definedness/distinction is invariant under this reversal. -/
def reversedHistories : RawLaneModel :=
  {baseline with assignment := mapCell canonical .histories (fun hs id =>
    match id with | .repA => hs .repB | .repB => hs .repA | other => hs other)}

theorem reversed_histories_outputs :
    acquisitionRouteOutput reversedHistories .a = some 1 ∧
    acquisitionRouteOutput reversedHistories .b = some 0 := by decide

theorem reversed_histories_corridor : AcquisitionCorridorPass reversedHistories := by
  unfold AcquisitionCorridorPass acquisitionCorridorCheck
  have hc : checkedAcquisition reversedHistories = some (image reversedHistories.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image reversedHistories.assignment) := by decide
    simp [h]
  rw [hc]
  decide

theorem acquisition_equal_route_outputs_reject (m : RawLaneModel) (a : Assignment)
    (h : acquisitionRouteOutput m .a = acquisitionRouteOutput m .b) :
    acquisitionAvailable m a = false := by simp [acquisitionAvailable,h]

theorem acquisition_undefined_route_output_reject (m : RawLaneModel) (a : Assignment)
    (h : acquisitionRouteOutput m .a = none) :
    acquisitionAvailable m a = false := by simp [acquisitionAvailable,h]

end CSTTT.TargetTheory.ComputedFIACH
