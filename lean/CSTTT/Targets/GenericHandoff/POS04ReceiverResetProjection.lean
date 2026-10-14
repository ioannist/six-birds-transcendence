import CSTTT.Targets.GenericHandoff.POS04RuntimeEquivalenceBoundary
import CSTTT.Targets.GenericHandoff.POS04CompleteLineage

/-! TTH-06: receiver-reset projection and its supported-execution boundary.
Authority: G6_lane_spec.md §§3,4O. Reception retains only the actual factor
and raw route tuple, resetting probe-local counters/ticks and writing its own
funding value. The following projection proves that equation for ALL words,
not only the canonical histories. It does not manufacture a supported history:
support/activation/realization remain separate acquisition obligations.

The diagnostic `sourceRechargeUnavailable` changes ONE raw resource field,
before any computation: disable pre-stage target recharge (hence staged source
recharge), preserving its owner and every other primitive. Frozen AO accepts,
but the current shared enabled acquisition has NO supported arrival even though
all its inputs are present. Thus removing receiver-overwritten tick reads alone
cannot establish arbitrary-partial equivalence with that acquisition semantics.
No frozen predicate or missing-input gate is changed in this module.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ReceiverResetProjection
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04RouteExecution
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

abbrev Retained := Ambient × (List KState × List EventId)

def retain (x : Run6) : Retained := (x.factor,x.residue)

/-- The actual outcome is retained, never a predictive representative. -/
def retainedStep (x : Retained) (o : Ambient) : Retained := (o,x.2)

def retainedFold : Retained → List (LaneDisturbance × Action × Ambient) → Retained
  | x,[] => x
  | x,(_,_,o)::rest => retainedFold (retainedStep x o) rest

theorem actual_step_projects (d : RunInputs6) (x : Run6) (act : Action) (o : Ambient) :
    retain (actualUpdate6 d x act o) = retainedStep (retain x) o := rfl

/-- Unbounded word induction, independent of the values of overwritten fields.
This is an equation on the instruction fold, NOT a support-acceptance check. -/
theorem actual_fold_projects (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (x : Run6) (word : List (LaneDisturbance × Action × Ambient)) :
    retain (actualFold a tag x word) = retainedFold (retain x) word := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    exact ih (actualUpdate6 (runInputs6 a tag) x act o)

/-- The receiver is the sole consumed cell of the reset operation. None stays
None: the canonical receiver is never substituted for an absent receiver. -/
def receiveRetained (a : CSTTT.POS04.Assigned.Assignment) (x : Retained) : Option Frame :=
  (a .receiverInput).map fun receiver =>
    match receiver.contentRule,receiver.registerRule with
    | .copyTerminalPositionPhase,.copyRawRouteTuple =>
      (.target,⟨x.1,0,0,x.2,receiver.funded⟩)

def projectedReception (a : CSTTT.POS04.Assigned.Assignment) (x : Retained)
    (word : List (LaneDisturbance × Action × Ambient)) : Option Frame :=
  receiveRetained a (retainedFold x word)

theorem receiver_missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (x : Retained)
    (hm : a .receiverInput = none) : receiveRetained a x = none := by
  simp [receiveRetained,hm]

theorem source_ticks_not_consumed (a : CSTTT.POS04.Assigned.Assignment) (x : Retained)
    (word : List (LaneDisturbance × Action × Ambient)) :
    projectedReception (put a (.ticks .source) none) x word = projectedReception a x word := rfl

/-- The reported deletion is harmless to the RESET VALUE. This does not
claim a repaired multi-resource game before its support adapter is proved. -/
theorem missing_past_ticks_reset_value (x : Retained)
    (word : List (LaneDisturbance × Action × Ambient)) :
    projectedReception (image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment) x word =
      projectedReception canonical x word := rfl

/-- Full autonomy legitimately requires the package's source tick primitive;
complete lineage retains it for source run tick laws and execution transport.
Neither follows from the weaker receiver-reset value alone. -/
theorem missing_past_ticks_full_and_lineage_rejected :
    ¬ AF POS04RuntimeEquivalenceBoundary.missingPastTicks ∧
    ¬ POS04CompleteLineage.StrictTemporalLineage POS04RuntimeEquivalenceBoundary.missingPastTicks := by
  refine ⟨POS04RuntimeEquivalenceBoundary.legacy_full_rejects,?_⟩
  intro hl
  have hp := hl.2.2.2.2.2.1.1 (.ticks .source) (by simp [POS04RouteExecution.dependencies])
  change (image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment (.ticks .source)).isSome = true at hp
  rw [POS04RuntimeEquivalenceBoundary.staged_source_ticks_missing] at hp
  contradiction

theorem receive_expression_projects (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (x : Run6) (hist rid : RouteId) :
    (receiveProgram ()).eval a (frame tag x) (hist,rid) = receiveRetained a (retain x) := by
  cases hr : a .receiverInput <;> simp [receiveProgram,Expr.eval,receiveRetained,retain,hr,
    frame,RunFrame.pack]

/-- Equality with the full checked execution whenever that execution is
defined. Its completeness/support obligations are not silently discarded. -/
theorem checked_execution_reception_projects (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) (x : Run6)
    (word : List (LaneDisturbance × Action × Ambient)) (hist rid : RouteId) :
    (receiveProgram ()).eval a
      (AcquisitionExecution.foldHistory acquisition a (ready a hc) (frame tag x) word)
      (hist,rid) = projectedReception a (retain x) word := by
  rw [fold_eq a hc,receive_expression_projects,actual_fold_projects]
  rfl

theorem supported_execution_reception_projects (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) (x : Run6)
    (word : List (LaneDisturbance × Action × Ambient)) (final : Registers Unit FrameValue)
    (he : AcquisitionExecution.HistoryExecution acquisition a (ready a hc) (frame tag x) word final)
    (hist rid : RouteId) :
    (receiveProgram ()).eval a final (hist,rid) = projectedReception a (retain x) word := by
  rw [AcquisitionExecution.history_terminal_defined acquisition a (ready a hc) he]
  exact checked_execution_reception_projects a hc tag x word hist rid

theorem canonical_projected_arrival_value (rid : RouteId) :
    projectedReception canonical (retain (acquisitionInitialRun canonical .source rid))
      (wordFor canonical rid) = some (.target,arrivalFor rid) := by
  unfold projectedReception
  rw [← actual_fold_projects canonical .source,canonical_source_terminal]
  rfl

theorem missing_past_ticks_projected_arrival_value (rid : RouteId) :
    projectedReception (image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment)
      (retain (acquisitionInitialRun
        (image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment) .source rid))
      (wordFor (image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment) rid) =
      some (.target,arrivalFor rid) := by
  rw [missing_past_ticks_reset_value]
  exact canonical_projected_arrival_value rid

/-- Diagnostic rule: disable only staged source recharge. This is not a new
positive model or an edited frozen intervention/prediction. -/
def sourceRechargeUnavailable : RawLaneModel :=
  {baseline with assignment := (Assigned.put canonical (.resources .target)
    (some (⟨.target,false⟩ : ResourceData)))}

abbrev diagnosticAssignment := image sourceRechargeUnavailable.assignment

theorem diagnostic_owner_preserved :
    (diagnosticAssignment (.resources .source)).map ResourceData.owner = some Tag.source ∧
    (diagnosticAssignment (.resources .target)).map ResourceData.owner = some Tag.target := ⟨rfl,rfl⟩

theorem diagnostic_complete (k : Cell) : (diagnosticAssignment k).isSome = true := by
  simp only [diagnosticAssignment,image,exchangeAssignment,Option.isSome_map]
  by_cases he : swapCell k = .resources .target
  · rw [he]; rfl
  · change (Assigned.put canonical (.resources .target) (some _) (swapCell k)).isSome = true
    rw [Assigned.put_other _ _ _ _ he]
    rfl

theorem diagnostic_ready : AcquisitionExecution.Ready acquisition diagnosticAssignment :=
  ready diagnosticAssignment (by intro k _; exact diagnostic_complete k)

theorem diagnostic_legacy_operational_unchanged :
    operationalAutonomyCheck sourceRechargeUnavailable = operationalAutonomyCheck baseline := rfl

theorem diagnostic_legacy_operational_accepts : AO sourceRechargeUnavailable := by
  change operationalAutonomyCheck sourceRechargeUnavailable = true
  rw [diagnostic_legacy_operational_unchanged]
  exact baseline_AO

theorem diagnostic_legacy_operational_game_accepts :
    POS04OperationalGame.Autonomy sourceRechargeUnavailable :=
  (POS04OperationalGame.game_iff_ao _).mpr diagnostic_legacy_operational_accepts

theorem diagnostic_source_rows_empty (x : Run6) (d : LaneDisturbance) (act : Action) :
    AcquisitionExecution.rows acquisition diagnosticAssignment (frame .source x) d act = [] := by
  rw [rows_eq diagnosticAssignment (by intro k _; exact diagnostic_complete k)]
  change (if x.funded && false && decide (1 ≥ 1) then _ else []) = []
  simp

/-- No nonempty supported acquisition word; all primitives ARE present. -/
theorem diagnostic_no_source_history (h : AcquisitionExecution.Ready acquisition diagnosticAssignment)
    (x : Run6) (word : List (LaneDisturbance × Action × Ambient)) (nonempty : word ≠ [])
    (final : Registers Unit FrameValue) :
    ¬ AcquisitionExecution.HistoryExecution acquisition diagnosticAssignment h (frame .source x) word final := by
  intro he
  cases word with
  | nil => exact nonempty rfl
  | cons e rest =>
    cases he with
    | step _ _ hp _ =>
      unfold StrategyGame.PositiveSupport at hp
      rw [diagnostic_source_rows_empty] at hp
      simp at hp

theorem diagnostic_no_arrival (h : AcquisitionExecution.Ready acquisition diagnosticAssignment)
    (rid : RouteId) (arrived : Registers Unit FrameValue) :
    ¬ AcquisitionExecution.Arrival POS04ExecutionFrontier.schema acquisition diagnosticAssignment h rid arrived := by
  rintro ⟨histories,routes,events,realized,receiver,hh,hr,_,_,_,_,_,_,_,src,exec,_⟩
  have hhist := Option.some.inj
    (hh.symm.trans (words_read diagnosticAssignment (by intro k _; exact diagnostic_complete k)))
  have hroutes := Option.some.inj
    (hr.symm.trans (routes_read diagnosticAssignment (by intro k _; exact diagnostic_complete k)))
  subst histories
  subst routes
  rw [initial_eq diagnosticAssignment (by intro k _; exact diagnostic_complete k)] at exec
  exact diagnostic_no_source_history h _ _ (by cases rid <;> decide +kernel) src exec

theorem diagnostic_no_entry (h : AcquisitionExecution.Ready acquisition diagnosticAssignment)
    (entry : Registers Unit FrameValue) :
    ¬ AcquisitionExecution.Entry POS04ExecutionFrontier.schema acquisition diagnosticAssignment h entry := by
  rintro ⟨_,rid,arrived,_,_,_,ha,_⟩
  exact diagnostic_no_arrival h rid arrived ha

/-- Any projection retaining the CURRENT supported-entry semantics also has
no entry on this total diagnostic. Pure reset-value equality cannot overcome
a missing supported history. This is a negative proposal lemma, not a supplied
predicate or decoder in an accepted raw handoff. -/
theorem diagnostic_support_preserving_projection_empty {Projected : Type}
    (proposedEntries : Projected → Prop) (decode : Projected → Registers Unit FrameValue)
    (support : ∀ x, proposedEntries x →
      AcquisitionExecution.Entry POS04ExecutionFrontier.schema acquisition
        diagnosticAssignment diagnostic_ready (decode x)) :
    ¬ ∃ x, proposedEntries x := by
  rintro ⟨x,hx⟩
  exact diagnostic_no_entry diagnostic_ready (decode x) (support x hx)

theorem diagnostic_runtime_no_games :
    ¬ PackageRuntime.PostWithdrawalFullAutonomy
      (POS04ResourceRuntime.model (POS04ResourceRuntime.protocol sourceRechargeUnavailable))
      sourceRechargeUnavailable.assignment ∧
    ¬ PackageRuntime.PostWithdrawalOperationalAutonomy
      (POS04ResourceRuntime.model (POS04ResourceRuntime.protocol sourceRechargeUnavailable))
      sourceRechargeUnavailable.assignment := by
  constructor <;> rintro ⟨ha,hr,game⟩
  all_goals
    obtain ⟨entry,he⟩ := game.2.1
    have he' : AcquisitionExecution.Entry POS04ExecutionFrontier.schema acquisition
        diagnosticAssignment diagnostic_ready entry := by
      simpa only [PackageRuntime.Entries,RuntimeComponents.Entries,
        POS04ResourceRuntime.acquisition_eq,POS04ResourceRuntime.target_eq] using he
    exact diagnostic_no_entry diagnostic_ready entry he'

/-- The requested equivalence is still obstructed on a TOTAL assignment;
no removal of dead missing inputs can resolve this support mismatch. -/
theorem total_assignment_operational_obstruction :
    ∃ m : RawLaneModel, (∀ k, (m.assignment k).isSome = true) ∧ AO m ∧
      ¬ PackageRuntime.PostWithdrawalOperationalAutonomy
        (POS04ResourceRuntime.model (POS04ResourceRuntime.protocol m)) m.assignment := by
  refine ⟨sourceRechargeUnavailable,?_,diagnostic_legacy_operational_accepts,diagnostic_runtime_no_games.2⟩
  intro k
  by_cases he : k = .resources .target
  · subst k; rfl
  · rw [show sourceRechargeUnavailable.assignment k = canonical k from
      Assigned.put_other _ _ _ _ he]
    rfl

end CSTTT.TargetTheory.GenericHandoff.POS04ReceiverResetProjection
