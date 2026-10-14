import CSTTT.Targets.GenericHandoff.ExecutedAcquisitionCorridor
import CSTTT.Targets.GenericHandoff.POS04AcquisitionCorridor

/-! Binding the POS-04 G4 predictive and history-residue seeds to actual
supported source execution. All four audit snapshots are computed by the
same actual-support fold. Event-path clock and phase-2/run clock remain distinct.
This does not claim the target/receiver or full G1c lineage adapter is complete.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ExecutedCorridor
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open RegisterInterpreter POS04RegisterDynamics CSTTT.TransportTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def actualFold (a : CSTTT.POS04.Assigned.Assignment) :
    Run6 → List (ComputedFIACH.LaneDisturbance × Action × Ambient) → Run6
  | x, [] => x
  | x, (_,act,o)::tail => actualFold a (actualUpdate6 (runInputs6 a .source) x act o) tail

theorem fold_equation (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete POS04ExecutionFrontier.dependencies a) (x : Run6)
    (word : List (ComputedFIACH.LaneDisturbance × Action × Ambient)) :
    AcquisitionExecution.foldHistory POS04ExecutionFrontier.acquisition a (POS04ExecutionFrontier.ready a hc).1
      (encode x) word = encode (actualFold a x word) := by
  induction word generalizing x with
  | nil => rfl
  | cons step tail ih =>
    rcases step with ⟨d,act,o⟩
    simp only [AcquisitionExecution.foldHistory,actualFold,POS04ExecutionFrontier.actual_update a hc,ih]

def observed (a : CSTTT.POS04.Assigned.Assignment) (i : RouteId × Nat) :=
  c6ObservationToBridge (observation6 (runInputs6 a .source) .source
    (actualFold a (ComputedFIACH.acquisitionInitialRun a .source i.1)
      (ExecutionFrontier.historyPrefix POS04ExecutionFrontier.raw a i)))

/-- Exact raw execution/readout equation for arbitrary partial assignments
once consumed inputs are present. All actual destinations are retained. -/
theorem snapshot_equation (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete POS04ExecutionFrontier.dependencies a) (i : RouteId × Nat) :
    ExecutionFrontier.observation POS04ExecutionFrontier.raw a (POS04ExecutionFrontier.ready a hc) i = observed a i := by
  unfold ExecutionFrontier.observation ExecutionFrontier.snapshot
  rw [POS04ExecutionFrontier.initial_eq a hc]
  change RegisterFuture.observation (ExecutionFrontier.temporal POS04ExecutionFrontier.raw) a _
    (AcquisitionExecution.foldHistory POS04ExecutionFrontier.acquisition a (POS04ExecutionFrontier.ready a hc).1
      (encode (ComputedFIACH.acquisitionInitialRun a .source i.1))
      (ExecutionFrontier.historyPrefix POS04ExecutionFrontier.raw a i)) = _
  rw [fold_equation a hc]
  change RegisterFuture.observation (POS04RegisterFuture.raw .source) a _ _ = _
  exact POS04RegisterFuture.observation_eq a .source
    (fun k hk => hc k (List.mem_append_left _ hk)) _

def coordinate : StaticView Cell Value (CSTTT.POS04.PredictiveNow → Nat) :=
  ⟨.map (fun (p : (KState → Action → List (Ambient × Nat)) × ((KState → Nat) × (Ambient → Bool))) =>
    let predict := POS04AcquisitionCorridor.rawPredictive p.1 p.2.1 p.2.2
    fun v => match v with
      | .active profile => (kernel.map predict).eraseDups.idxOf profile
      | .exit2 => (kernel.map predict).eraseDups.length
      | .exit5 => (kernel.map predict).eraseDups.length + 1)
    (.pair (.cell (Cell.rows Tag.source)) (.pair (.cell Cell.positions) (.cell Cell.hazards)))⟩

def raw : ExecutedAcquisitionCorridor.Raw Cell Value Register RegisterValue
    ComputedFIACH.LaneDisturbance Action Ambient CSTTT.POS04.PredictiveNow
      (List KState × List EventId) Bool CSTTT.POS04.Stage EventId RouteId RouteId :=
  ⟨POS04ExecutionFrontier.raw,⟨eventName,"source_live"⟩,POS04AcquisitionCorridor.seeds,
    coordinate,(fun residue => residue.1.map stateName),
    fun residue => residue.1.map stateName ++ residue.2.map eventName⟩

theorem corridor_shared : ExecutedAcquisitionCorridor.corridor raw = POS04AcquisitionCorridor.raw := rfl

def canonicalCoordinate : CSTTT.POS04.PredictiveNow → Nat :=
  fun v => match v with
  | .active profile => (kernel.map (POS04AcquisitionCorridor.rawPredictive
      (canonicalValue (.rows .source)) (canonicalValue .positions) (canonicalValue .hazards))).eraseDups.idxOf profile
  | .exit2 => (kernel.map (POS04AcquisitionCorridor.rawPredictive
      (canonicalValue (.rows .source)) (canonicalValue .positions) (canonicalValue .hazards))).eraseDups.length
  | .exit5 => (kernel.map (POS04AcquisitionCorridor.rawPredictive
      (canonicalValue (.rows .source)) (canonicalValue .positions) (canonicalValue .hazards))).eraseDups.length + 1

theorem coordinate_read : coordinate.read canonical = some canonicalCoordinate := rfl

theorem audited_values (i : Audited POS04ExecutionFrontier.raw.audit) :
    i.val = (.a,1) ∨ i.val = (.a,2) ∨ i.val = (.b,1) ∨ i.val = (.b,2) := by
  rcases i with ⟨⟨r,n⟩,hi⟩
  cases r <;> simpa [POS04ExecutionFrontier.raw,POS04ExecutionFrontier.audit,
    ComputedFIACH.acquisitionSnapshotIndices,routeIds,snapshotPositions,snapshotOccurrence] using hi

theorem coordinate_reflects (r s : RouteId) (n k : Nat)
    (hn : n = 1 ∨ n = 2) (hk : k = 1 ∨ k = 2) :
    canonicalCoordinate (observed canonical (r,n)).predictive =
      canonicalCoordinate (observed canonical (s,k)).predictive →
    (observed canonical (r,n)).predictive = (observed canonical (s,k)).predictive := by
  rcases hn with rfl | rfl <;> rcases hk with rfl | rfl
  all_goals cases r <;> cases s <;> decide +kernel

theorem audited_occurrences (i : Audited POS04ExecutionFrontier.raw.audit) : i.val.2 = 1 ∨ i.val.2 = 2 := by
  rcases audited_values i with hi | hi | hi | hi <;> simp [hi]

theorem canonical_seed_coherence
    (h : ExecutionFrontier.Ready POS04ExecutionFrontier.raw canonical)
    (v : AcquisitionCorridor.View CSTTT.POS04.Stage EventId RouteId RouteId)
    (hv : AcquisitionCorridor.read (ExecutedAcquisitionCorridor.corridor raw) canonical = some v) :
    ExecutedAcquisitionCorridor.SeedCoherence raw canonical h v := by
  have hval := Option.some.inj (hv.symm.trans (POS04AcquisitionCorridor.read_eq canonical (canonical_complete _)))
  subst v
  have hp : h = POS04ExecutionFrontier.ready canonical (canonical_complete _) := Subsingleton.elim _ _
  subst h
  refine ⟨canonicalCoordinate,coordinate_read,?_,?_⟩
  · intro i j he
    change canonicalCoordinate (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ i.val).predictive =
      canonicalCoordinate (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ j.val).predictive at he
    rw [snapshot_equation canonical (canonical_complete _),snapshot_equation canonical (canonical_complete _)] at he
    change (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ i.val).predictive =
      (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ j.val).predictive
    rw [snapshot_equation canonical (canonical_complete _),snapshot_equation canonical (canonical_complete _)]
    exact coordinate_reflects i.val.1 j.val.1 i.val.2 j.val.2
      (audited_occurrences i) (audited_occurrences j) he
  · intro histories he i hi hend
    have hword := POS04ExecutionFrontier.word_eq canonical (canonical_complete _)
    have hhist := Option.some.inj (he.symm.trans hword)
    subst histories
    change i.2 = _ at hend
    rcases i with ⟨r,n⟩
    have hn : n = 2 := by cases r <;> simpa using hend
    subst n
    change (POS04AcquisitionCorridor.view canonical).seeds.predictive r =
      canonicalCoordinate (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ (r,2)).predictive ∧
      (POS04AcquisitionCorridor.view canonical).seeds.history r =
        (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ (r,2)).residue.1.map stateName ∧
      (POS04AcquisitionCorridor.view canonical).seeds.history r ++
        ((POS04AcquisitionCorridor.view canonical).routes r).path.map eventName =
      (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ (r,2)).residue.1.map stateName ++
        (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ (r,2)).residue.2.map eventName
    rw [snapshot_equation canonical (canonical_complete _)]
    cases r <;> decide +kernel

theorem positive : ExecutedAcquisitionCorridor.Valid raw canonical :=
  ⟨POS04ExecutionFrontier.positive,POS04AcquisitionCorridor.positive,canonical_seed_coherence⟩

theorem missing_atomic_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ ExecutedAcquisitionCorridor.Valid raw (Assigned.put a .eventTable none) := by
  apply ExecutedAcquisitionCorridor.missing_atomic_guard
  simp [raw,POS04ExecutionFrontier.raw,POS04ExecutionFrontier.acquisition,
    POS04ExecutionFrontier.eventView,CellView.read]

/-- A false constant predictive seed is checked against the executed endpoint;
the actual row/updater, observer and coordinate instruction remain unchanged. -/
def falseSeed := {raw with seeds := ⟨.literal {
  predictive := fun _ => kernel.length
  history := (POS04AcquisitionCorridor.view canonical).seeds.history}⟩}

def falseSeedView : AcquisitionCorridor.View CSTTT.POS04.Stage EventId RouteId RouteId :=
  {POS04AcquisitionCorridor.view canonical with seeds := {
    predictive := fun _ => kernel.length
    history := (POS04AcquisitionCorridor.view canonical).seeds.history}}

theorem false_seed_read :
    AcquisitionCorridor.read (ExecutedAcquisitionCorridor.corridor falseSeed) canonical = some falseSeedView := rfl

theorem false_seed_rejected : ¬ ExecutedAcquisitionCorridor.Valid falseSeed canonical := by
  apply ExecutedAcquisitionCorridor.seed_mismatch_guard falseSeed canonical
    POS04ExecutionFrontier.canonical_ready falseSeedView false_seed_read
    _ (POS04ExecutionFrontier.word_eq canonical (canonical_complete _))
    ⟨(.a,2),by decide⟩ (by decide) canonicalCoordinate coordinate_read
  change ¬ (kernel.length = canonicalCoordinate
      (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ (.a,2)).predictive ∧ _)
  rw [snapshot_equation canonical (canonical_complete _)]
  decide +kernel

theorem missing_coordinate_rejected (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ coordinate.dependencies) :
    ¬ ExecutedAcquisitionCorridor.Valid raw (Assigned.put a k none) :=
  ExecutedAcquisitionCorridor.missing_coordinate_guard raw _ k hk (Assigned.put_same _ _ _)

end CSTTT.TargetTheory.GenericHandoff.POS04ExecutedCorridor
