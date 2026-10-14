import CSTTT.Targets.GenericHandoff.POS04ActualControls
import CSTTT.Targets.GenericHandoff.GameInvariantCompleteness

/-! Frozen Version O, G6_lane_spec.md:307–319. Only the operational ledger,
rows, ticks, route/writer and acquisition primitives are read. No predictive
hazards, M, channels or full C6 interface is consumed. All actual response
branches remain. No greatest set occurs in the game semantics. The older
POS04ActualGame.OperationalAutonomy is retained as a full-C6 schema, not O. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH
abbrev Run := Run6
abbrev Disturbance := LaneDisturbance

def dependencies := autonomyInputs ++ phase2Dependencies
structure Inputs where
  viability : ViabilityInputs
  ticks : KState → Action → Nat
  routes : List Route
  histories : HistoryId → List KState
  writers : Tag → RouteId → Bool

def inputs (m : RawLaneModel) : Inputs :=
  let a := decode dependencies (withdrawnAssignment m)
  ⟨viabilityInputs a .target,
   (a (.ticks .target)).getD (canonicalValue (.ticks .target)),
   (a .routeTable).getD (canonicalValue .routeTable),
   (a .histories).getD (canonicalValue .histories),
   (a .writers).getD (canonicalValue .writers)⟩
def tuple (d : Inputs) (id : RouteId) : Option (List KState × List EventId) :=
  (d.routes.find? (fun r => r.id == id)).map fun r => (d.histories r.sourceHistory,r.eventPath)
def writer (d : Inputs) (residue : List KState × List EventId) : Bool :=
  if tuple d .a = some residue then d.writers .target .a
  else if tuple d .b = some residue then d.writers .target .b else false

def rawRow (d : Inputs) : Ambient → Action → List (Ambient × Nat)
  | .inK s,a => d.viability.rows s a
  | _,_ => []
def tick (d : Inputs) : Ambient → Action → Nat
  | .inK s => d.ticks s
  | .p2w0 | .p5w1 => fun _ => 0

def rows (m : RawLaneModel) (r : Run) (_d : Disturbance) (a : Action) : List (Ambient × Rat) :=
  if Complete dependencies (image m.assignment) then
    (rawRow (inputs m) r.factor a).map fun e => (e.1,(e.2 : Rat)/4)
  else []
def update (m : RawLaneModel) (r : Run) (_d : Disturbance) (a : Action) (o : Ambient) : Run :=
  let d := inputs m
  ⟨o,r.counter+1,r.ticks+tick d r.factor a,r.residue,
    r.funded && decide (d.viability.budget.initialBudget - d.viability.budget.actionCost +
      d.viability.budget.rechargePerAction > 0)⟩
def record (m : RawLaneModel) (r : Run) :=
  if r.funded && writer (inputs m) r.residue then r.counter else 0

/-- Raw protocol checks independent of the safe set and chosen strategy. -/
def Protocol (m : RawLaneModel) : Prop :=
  Complete autonomyInputs (image m.assignment) ∧ withdrawalCheck m = true ∧
  advancementCheck m = true ∧ PUnchanged8 (withdrawnInputs m) ∧
  routeIds.all (phase2Check m) = true

def entryRun (m : RawLaneModel) (e : WithdrawalEntry) : Run :=
  ⟨e.factor,e.counter,e.ticks,e.register,(arrivalInputs m).base.receiver.funded⟩
/-- Every phase-2 entry is quantified; no invalid branch is filtered away. -/
def Entries (m : RawLaneModel) (r : Run) : Prop :=
  ∃ e ∈ entries m, r = entryRun m e

def Inside (_m : RawLaneModel) (r : Run) : Prop := ∃ s, r.factor = .inK s

def ResourceClosed (m : RawLaneModel) (r : Run) : Prop :=
  available8 (inputs m).viability .target = true ∧
  Ledger8 (inputs m).viability ∧ r.funded = true ∧ writer (inputs m) r.residue = true

def Legal (m : RawLaneModel) (r : Run) (_d : Disturbance) (a : Action) : Prop :=
  a ∈ actions ∧ ∃ s, r.factor = .inK s ∧ rowClosed8 (inputs m).viability s a kernel = true

def StepLaw (m : RawLaneModel) (r : Run) (d : Disturbance) (a : Action) (o : Ambient) : Prop :=
  (update m r d a o).funded = true ∧
  (update m r d a o).counter = r.counter+1 ∧
  (update m r d a o).ticks = r.ticks+1 ∧
  record m (update m r d a o) = record m r+1 ∧
  (update m r d a o).residue = r.residue ∧ (inputs m).viability.resource.owner = .target

abbrev Certificate (m : RawLaneModel) :=
  StrategyGame.InvariantCertificate (rows m) (update m) (Entries m) (Protocol m)
    (Inside m) (ResourceClosed m) (Legal m) (StepLaw m)
def Autonomy (m : RawLaneModel) : Prop :=
  StrategyGame.GameReadout (rows m) (update m) (Entries m) (Protocol m)
    (Inside m) (ResourceClosed m) (Legal m) (StepLaw m)

theorem soundness (m : RawLaneModel) (h : Certificate m) : Autonomy m :=
  StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ h

theorem dependencies_no_hazards : Cell.hazards ∉ dependencies := by decide

theorem inputs_locality {m n : RawLaneModel}
    (h : Agrees dependencies (withdrawnAssignment m) (withdrawnAssignment n)) : inputs m = inputs n := by
  unfold inputs
  rw [decoder_locality h]

theorem missing_dependency_rejects (m : RawLaneModel) (k : Cell) (hk : k ∈ dependencies)
    (hm : image m.assignment k = none) : ¬ Autonomy m := by
  intro h
  have hp := h.1
  rcases List.mem_append.mp hk with hk | hk
  · have hc := hp.1 k hk
    rw [hm] at hc
    contradiction
  · have he := List.all_eq_true.mp hp.2.2.2.2 RouteId.a (by decide)
    have hf := phase2_missing_staged_cell m k hk hm .a
    rw [hf] at he
    contradiction

theorem protocol_complete (m : RawLaneModel) (h : Protocol m) :
    Complete dependencies (image m.assignment) := by
  intro k hk
  rcases List.mem_append.mp hk with hk | hk
  · exact h.1 k hk
  · have hp := List.all_eq_true.mp h.2.2.2.2 RouteId.a (by decide)
    by_cases hc : phase2Complete m = true
    · exact (of_decide_eq_true hc : Complete phase2Dependencies (image m.assignment)) k hk
    · have hf : phase2Complete m = false := Bool.eq_false_iff.mpr hc
      simp [phase2Check,hf] at hp

/-- Same assigned rows/ledger as O, without predictive defaults. -/
theorem viability_eq (m : RawLaneModel) : (inputs m).viability = withdrawnInputs m := by
  unfold inputs withdrawnInputs clause8 viabilityInputs decode
  simp only [show Cell.rows .target ∈ dependencies from by decide,
    show Cell.policy ∈ dependencies from by decide,
    show Cell.resources .target ∈ dependencies from by decide,
    show Cell.maintenance ∈ dependencies from by decide,
    show Cell.rows .target ∈ clauseScope .target .c8 from by decide,
    show Cell.policy ∈ clauseScope .target .c8 from by decide,
    show Cell.resources .target ∈ clauseScope .target .c8 from by decide,
    show Cell.maintenance ∈ clauseScope .target .c8 from by decide,if_true]

/-- Exact operational projections, even when unused C6 cells are absent. -/
theorem operational_projections (m : RawLaneModel) :
    (inputs m).ticks = (runInputs6 (withdrawnAssignment m) .target).ticks ∧
    (inputs m).histories = (runInputs6 (withdrawnAssignment m) .target).base.histories ∧
    (inputs m).routes = (runInputs6 (withdrawnAssignment m) .target).base.routes ∧
    (inputs m).writers = (runInputs6 (withdrawnAssignment m) .target).base.writers := by
  unfold inputs runInputs6 extraInputs decode
  simp only [show Cell.ticks .target ∈ dependencies from by decide,
    show Cell.histories ∈ dependencies from by decide,
    show Cell.routeTable ∈ dependencies from by decide,
    show Cell.writers ∈ dependencies from by decide,
    show Cell.ticks .target ∈ clauseScope .target .c6 from by decide,
    show Cell.histories ∈ clauseScope .target .c6 from by decide,
    show Cell.routeTable ∈ clauseScope .target .c6 from by decide,
    show Cell.writers ∈ clauseScope .target .c6 from by decide,if_true]
  trivial

theorem tuple_eq (m : RawLaneModel) (r : RouteId) :
    tuple (inputs m) r = routeTuple (runInputs6 (withdrawnAssignment m) .target).base r := by
  simp only [tuple,routeTuple,(operational_projections m).2.1,(operational_projections m).2.2.1]

theorem writer_eq (m : RawLaneModel) (residue : List KState × List EventId) :
    writer (inputs m) residue = writer6 (runInputs6 (withdrawnAssignment m) .target) .target residue := by
  simp only [writer,writer6,tuple_eq,(operational_projections m).2.2.2]

theorem actual_update_eq (m : RawLaneModel) (r : Run) (d : Disturbance) (a : Action) (o : Ambient) :
    update m r d a o = actualUpdate6 (runInputs6 (withdrawnAssignment m) .target) r a o := by
  simp only [update,actualUpdate6,budgetAfter6,budget6,viability_eq,withdrawnInputs,
    tick,delta6,(operational_projections m).1]
  congr 1 <;> try rfl
  cases r.factor <;> rfl

end CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame
