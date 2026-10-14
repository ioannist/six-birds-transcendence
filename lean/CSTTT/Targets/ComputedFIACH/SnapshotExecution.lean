import CSTTT.Targets.ComputedFIACH.AcquisitionSnapshots

/-! G6_lane_spec.md:115–139. Execution links for the four audited snapshots.
The path, initial run, policy, probabilities and updater all read the same
checked staged assignment. No snapshot or execution candidate is an argument.
This is an execution seam, not yet the complete RawBridge adapter. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def historyAction6 (d : RunInputs6) (x : Run6) : Action :=
  match x.factor with
  | .inK s => d.base.base.policy s
  | .p2w0 | .p5w1 => .stay

def historyNext6 (d : RunInputs6) (x : Run6) (s : KState) : Run6 :=
  update6 d x (historyAction6 d x) (predictive6 d (.inK s))

/-- Require the raw successor itself, not merely a member of its M class.
The exact positive probability and representative equation link execution
to the defined future updater. Exit rows and disabled responses reject. -/
def historyStepCheck6 (d : RunInputs6) (x : Run6) (s : KState) : Bool :=
  decide (∃ e ∈ row6 d x.factor (historyAction6 d x), e.1 = .inK s ∧ e.2 > 0) &&
  decide (weight6 d x (historyAction6 d x) (predictive6 d (.inK s)) > 0) &&
  decide ((historyNext6 d x s).factor = .inK s)

def executeHistory6 (d : RunInputs6) (x : Run6) : List KState → Run6
  | [] => x
  | s :: rest => executeHistory6 d (historyNext6 d x s) rest

def historyExecutionCheck6 (d : RunInputs6) (x : Run6) : List KState → Bool
  | [] => true
  | s :: rest => historyStepCheck6 d x s &&
      historyExecutionCheck6 d (historyNext6 d x s) rest

/-- A supported execution records both the raw state edge and its strictly
positive probability. FutureClosure alone also contains zero-weight steps,
so it would be insufficient evidence for an actual acquisition path. -/
inductive SupportedHistoryExecution6 (d : RunInputs6) : Run6 → List KState → Run6 → Prop
  | nil (x) : SupportedHistoryExecution6 d x [] x
  | cons (x : Run6) (s : KState) (rest : List KState) (last : Run6)
      (edge : ∃ e ∈ row6 d x.factor (historyAction6 d x), e.1 = .inK s ∧ e.2 > 0)
      (weight : weight6 d x (historyAction6 d x) (predictive6 d (.inK s)) > 0)
      (factor : (historyNext6 d x s).factor = .inK s)
      (tail : SupportedHistoryExecution6 d (historyNext6 d x s) rest last) :
      SupportedHistoryExecution6 d x (s :: rest) last

theorem history_execution_supported (d : RunInputs6) (x : Run6) (path : List KState)
    (h : historyExecutionCheck6 d x path = true) :
    SupportedHistoryExecution6 d x path (executeHistory6 d x path) := by
  induction path generalizing x with
  | nil => exact .nil x
  | cons s rest ih =>
    obtain ⟨hs,hr⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hew,hfactor⟩ := Bool.and_eq_true_iff.mp hs
    obtain ⟨hedge,hweight⟩ := Bool.and_eq_true_iff.mp hew
    exact .cons x s rest _ (of_decide_eq_true hedge) (of_decide_eq_true hweight)
      (of_decide_eq_true hfactor) (ih _ hr)

theorem execute_history_counter (d : RunInputs6) (x : Run6) (path : List KState) :
    (executeHistory6 d x path).counter = x.counter + path.length := by
  induction path generalizing x with
  | nil => simp [executeHistory6]
  | cons s rest ih =>
    simpa [executeHistory6,historyNext6,update6,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using ih (historyNext6 d x s)

theorem execute_history_residue (d : RunInputs6) (x : Run6) (path : List KState) :
    (executeHistory6 d x path).residue = x.residue := by
  induction path generalizing x with
  | nil => rfl
  | cons s rest ih => exact ih (historyNext6 d x s)

theorem history_execution_closure (a : Assignment) (t : Tag) (x : Run6)
    (path : List KState) (hx : Closure6 a t x)
    (h : historyExecutionCheck6 (runInputs6 a t) x path = true) :
    Closure6 a t (executeHistory6 (runInputs6 a t) x path) := by
  induction path generalizing x with
  | nil => exact hx
  | cons s rest ih =>
    obtain ⟨_,hr⟩ := Bool.and_eq_true_iff.mp h
    exact ih (historyNext6 (runInputs6 a t) x s)
      (closure6_step hx (historyAction6 (runInputs6 a t) x)
        (predictive6 (runInputs6 a t) (.inK s))
        (outcomes6_cover (runInputs6 a t) (.inK s))) hr

def acquisitionInitialRun (a : Assignment) (t : Tag) (r : RouteId) : Run6 :=
  let d := runInputs6 a t
  ⟨.inK ((acquisitionHistory a t r).getD 0 .p0w0),0,0,
    (routeTuple d.base r).getD ([],[]),d.base.receiver.funded⟩

def acquisitionExecutionPrefix (a : Assignment) (t : Tag) (i : SnapshotIndex) : List KState :=
  ((acquisitionHistory a t i.1).drop 1).take (snapshotOccurrence i.2)

def acquisitionExecutedSnapshot (a : Assignment) (t : Tag) (i : SnapshotIndex) : Run6 :=
  executeHistory6 (runInputs6 a t) (acquisitionInitialRun a t i.1)
    (acquisitionExecutionPrefix a t i)

def acquisitionExecutionAtCheck (a : Assignment) (t : Tag) (i : SnapshotIndex) : Bool :=
  decide (acquisitionInitialRun a t i.1 ∈ roots6 a t) &&
  decide (snapshotOccurrence i.2 < (acquisitionHistory a t i.1).length) &&
  historyExecutionCheck6 (runInputs6 a t) (acquisitionInitialRun a t i.1)
    (acquisitionExecutionPrefix a t i) &&
  decide (acquisitionExecutedSnapshot a t i = acquisitionSnapshotRun a t i)

def acquisitionExecutionCheck (m : RawLaneModel) : Bool :=
  match checkedAcquisition m with
  | none => false
  | some a => tags.all fun t => acquisitionSnapshotIndices.all (acquisitionExecutionAtCheck a t)

def AcquisitionExecutionPass (m : RawLaneModel) := acquisitionExecutionCheck m = true

theorem acquisition_execution_at (a : Assignment) (t : Tag) (i : SnapshotIndex)
    (h : acquisitionExecutionAtCheck a t i = true) :
    acquisitionExecutedSnapshot a t i = acquisitionSnapshotRun a t i ∧
    Closure6 a t (acquisitionSnapshotRun a t i) := by
  obtain ⟨hrest,he⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hrootbound,hrun⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hroot,_⟩ := Bool.and_eq_true_iff.mp hrootbound
  have heq : acquisitionExecutedSnapshot a t i = acquisitionSnapshotRun a t i :=
    of_decide_eq_true he
  refine ⟨heq,?_⟩
  rw [← heq]
  exact history_execution_closure a t _ _
    (FutureClosure.root _ (of_decide_eq_true hroot)) hrun

theorem acquisition_execution_supported_at (a : Assignment) (t : Tag) (i : SnapshotIndex)
    (h : acquisitionExecutionAtCheck a t i = true) :
    SupportedHistoryExecution6 (runInputs6 a t) (acquisitionInitialRun a t i.1)
      (acquisitionExecutionPrefix a t i) (acquisitionSnapshotRun a t i) := by
  obtain ⟨hrest,he⟩ := Bool.and_eq_true_iff.mp h
  have hr := (Bool.and_eq_true_iff.mp hrest).2
  have heq : acquisitionExecutedSnapshot a t i = acquisitionSnapshotRun a t i :=
    of_decide_eq_true he
  rw [← heq]
  exact history_execution_supported _ _ _ hr

/-- The generic readout has no separately supplied snapshots, weights,
successors, code or observation. All four contexts execute the defined
assignment dynamics; observation equality covers every C6 component. -/
theorem acquisition_execution_sound (m : RawLaneModel) (h : AcquisitionExecutionPass m) :
    ∃ a, checkedAcquisition m = some a ∧
      ∀ t ∈ tags, ∀ i ∈ acquisitionSnapshotIndices,
        SupportedHistoryExecution6 (runInputs6 a t) (acquisitionInitialRun a t i.1)
          (acquisitionExecutionPrefix a t i) (acquisitionSnapshotRun a t i) ∧
        Closure6 a t (acquisitionSnapshotRun a t i) ∧
        (future6 a t).observe (acquisitionExecutedSnapshot a t i) =
          acquisitionSnapshotObservation a t i := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck at h
  split at h
  · contradiction
  · rename_i a ha
    refine ⟨a,ha,?_⟩
    intro t ht i hi
    have hc := List.all_eq_true.mp (List.all_eq_true.mp h t ht) i hi
    obtain ⟨he,hclosure⟩ := acquisition_execution_at a t i hc
    exact ⟨acquisition_execution_supported_at a t i hc,hclosure,congrArg _ he⟩

/-- Codec transport and unbounded word sufficiency remain separate from the
supported execution proof; the combined result consumes both raw subchecks. -/
def AcquisitionExecutedSnapshotPass (m : RawLaneModel) : Prop :=
  AcquisitionSnapshotPass m ∧ AcquisitionExecutionPass m

theorem acquisition_executed_snapshot_future (m : RawLaneModel)
    (h : AcquisitionExecutedSnapshotPass m) :
    ∃ a, checkedAcquisition m = some a ∧
      FullFutureSufficient (future6 a .source) ∧ FullFutureSufficient (future6 a .target) ∧
      ∀ t ∈ tags, ∀ i ∈ acquisitionSnapshotIndices,
        Closure6 a t (acquisitionSnapshotRun a t i) := by
  obtain ⟨a,ha,hs,ht,_⟩ := acquisition_snapshot_future m h.1
  obtain ⟨b,hb,hx⟩ := acquisition_execution_sound m h.2
  have hab : a = b := Option.some.inj (ha.symm.trans hb)
  subst b
  exact ⟨a,ha,hs,ht,fun t ht i hi => (hx t ht i hi).2.1⟩

theorem acquisition_execution_missing_dependency (m : RawLaneModel) (k : Cell)
    (hk : k ∈ acquisitionDependencies) :
    ¬ AcquisitionExecutionPass {m with assignment := put m.assignment (swapCell k) none} := by
  simp [AcquisitionExecutionPass,acquisitionExecutionCheck,acquisition_missing_dependency m k hk]

theorem baseline_acquisition_execution : AcquisitionExecutionPass baseline := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck
  rw [baseline_acquisition]
  decide +kernel

theorem package_deletion_acquisition_execution : AcquisitionExecutionPass packageDeletion := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck
  rw [package_deletion_acquisition]
  decide +kernel

theorem lineage_deletion_acquisition_execution : AcquisitionExecutionPass lineageDeletion := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck
  have hc : checkedAcquisition lineageDeletion = some (image lineageDeletion.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image lineageDeletion.assignment) := by decide
    simp [h]
  rw [hc,lineage_staged_assignment]
  decide +kernel

theorem withdrawal_deletion_acquisition_execution : AcquisitionExecutionPass withdrawalDeletion := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck
  rw [withdrawal_deletion_acquisition]
  decide +kernel

theorem reversed_histories_acquisition_execution : AcquisitionExecutionPass reversedHistories := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck
  have hc : checkedAcquisition reversedHistories = some (image reversedHistories.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image reversedHistories.assignment) := by decide
    simp [h]
  rw [hc]
  decide +kernel

/-- A raw transition corruption rejects even though every primitive cell
is present. This guard tests execution, independently of C6 acceptance. -/
def emptyAcquisitionRows : RawLaneModel :=
  {baseline with assignment := put canonical (.rows .target) (some (fun _ _ => []))}

theorem empty_acquisition_rows_reject_execution : ¬ AcquisitionExecutionPass emptyAcquisitionRows := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck
  have hc : checkedAcquisition emptyAcquisitionRows = some (image emptyAcquisitionRows.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image emptyAcquisitionRows.assignment) := by decide
    simp [h]
  rw [hc]
  decide +kernel

theorem truncated_acquisition_histories_reject_execution :
    ¬ AcquisitionExecutionPass truncatedAcquisitionHistories := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck
  have hc : checkedAcquisition truncatedAcquisitionHistories =
      some (image truncatedAcquisitionHistories.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image truncatedAcquisitionHistories.assignment) := by decide
    simp [h]
  rw [hc]
  decide +kernel

theorem source_absent_reject_execution : ¬ AcquisitionExecutionPass sourceAbsent := by
  unfold AcquisitionExecutionPass acquisitionExecutionCheck
  have hc : checkedAcquisition sourceAbsent = some (image sourceAbsent.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image sourceAbsent.assignment) := by decide
    simp [h]
  rw [hc]
  decide +kernel

end CSTTT.TargetTheory.ComputedFIACH
