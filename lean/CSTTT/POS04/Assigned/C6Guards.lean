import CSTTT.POS04.Assigned.C6Adapters
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

theorem c6_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c6) : ¬ C6Accept (put a k none) tag := by
  intro h
  exact missing_cell_rejected _ a k hk h.1.1.1

/-- A single raw tick entry breaks the equal-code p0 bisimulation, not just
its trace flag. Thus no bounded-word test is used to reject this control. -/
theorem neg_future6_bisim_fails : ¬ FiniteBisim6 (runInputs6 (futureBreak6 canonical) .target) := by
  intro h
  have he := (h (.inK .p0w0) (by decide) (.inK .p0w1) (by decide) .stay (by decide) (by decide)).2
  change (1 : Nat) = 2 at he
  contradiction

def assignedCounterexampleTrace6 : List C6Observation :=
  let a := futureBreak6 canonical
  let d := runInputs6 a .target
  let x := initial6 a .target .p0w0 .a
  [observation6 d .target x,
   observation6 d .target (update6 d x .stay (legacyOutcome6 .target .m1))]

/-- Actual word-law failure, not the invalid inference that a failed
sufficient bisimulation test by itself disproves future sufficiency. -/
theorem neg_future6_word_distinguishes :
    (future6 (futureBreak6 canonical) .target).code
      (initial6 (futureBreak6 canonical) .target .p0w0 .a) =
    (future6 (futureBreak6 canonical) .target).code
      (initial6 (futureBreak6 canonical) .target .p0w1 .a) ∧
    fullFuture (future6 (futureBreak6 canonical) .target)
      (initial6 (futureBreak6 canonical) .target .p0w0 .a) [.stay] assignedCounterexampleTrace6 ≠
    fullFuture (future6 (futureBreak6 canonical) .target)
      (initial6 (futureBreak6 canonical) .target .p0w1 .a) [.stay] assignedCounterexampleTrace6 := by
  decide +kernel

theorem neg_future6_not_sufficient : ¬ FullFutureSufficient (future6 (futureBreak6 canonical) .target) := by
  intro h
  exact neg_future6_word_distinguishes.2
    (h _ _ neg_future6_word_distinguishes.1 [.stay] assignedCounterexampleTrace6)

def noStrict6 (a : Assignment) := mapCell a .eventTable (fun es => es.map fun e =>
  if e.id = .mix1 then {e with strictStep := false} else e)
def noAtomic6 (a : Assignment) := mapCell a .eventTable (fun es => es.map fun e =>
  if e.id = .mix1 then {e with atomic := false} else e)
def wrongEndpoint6 (a : Assignment) := mapCell a .eventTable (fun es => es.map fun e =>
  if e.id = .mix1 then {e with toStage := .targetExit} else e)
def truncatedPath6 (a : Assignment) := mapCell a .routeTable (fun rs => rs.map fun r =>
  {r with eventPath := r.eventPath.take 2})
def emptyInterface6 (a : Assignment) := put a .interface (some [])

/-- Generic rejection helpers expose exactly the failed raw check. -/
theorem c6_paths_reject {a : Assignment} {tag : Tag}
    (h : paths6 (runInputs6 a tag) = false) : ¬ C6Accept a tag := by
  intro hp
  have he := hp.1.2.2.1.2.2.2.2.2.1
  rw [h] at he
  contradiction

theorem c6_events_guard (tag : Tag) : ¬ C6Accept (emptyEvents canonical) tag :=
  c6_paths_reject (by cases tag <;> decide)
theorem c6_strict_step_guard (tag : Tag) : ¬ C6Accept (noStrict6 canonical) tag :=
  c6_paths_reject (by cases tag <;> decide)
theorem c6_atomic_guard (tag : Tag) : ¬ C6Accept (noAtomic6 canonical) tag :=
  c6_paths_reject (by cases tag <;> decide)
theorem c6_endpoint_guard (tag : Tag) : ¬ C6Accept (wrongEndpoint6 canonical) tag :=
  c6_paths_reject (by cases tag <;> decide)
theorem c6_route_path_guard (tag : Tag) : ¬ C6Accept (truncatedPath6 canonical) tag :=
  c6_paths_reject (by cases tag <;> decide)

theorem c6_histories_guard (tag : Tag) : ¬ C6Accept (emptyHistories canonical) tag :=
  c6_paths_reject (by cases tag <;> decide)
theorem c6_routes_guard (tag : Tag) : ¬ C6Accept (cappedRoutes canonical) tag :=
  c6_paths_reject (by cases tag <;> decide)
theorem c6_realization_guard (tag : Tag) : ¬ C6Accept (noRealization canonical) tag :=
  c6_paths_reject (by cases tag <;> decide)

theorem c6_receiver_funding_guard (tag : Tag) : ¬ C6Accept (unfundedReceiver canonical) tag := by
  intro h
  have he := h.1.2.2.1.1
  cases tag <;> change false = true at he <;> contradiction

theorem c6_resource_funding_guard (tag : Tag) : ¬ C6Accept (noRecharge8 canonical tag) tag := by
  intro h
  have he := h.1.2.2.1.2.1
  cases tag <;> change false = true at he <;> contradiction

theorem c6_owner_guard (tag : Tag) : ¬ C6Accept (wrongOwner8 canonical tag) tag := by
  intro h
  have he := h.1.2.2.1.2.2.2.2.2.2
  cases tag <;> contradiction

theorem c6_initial_budget_guard (tag : Tag) : ¬ C6Accept (zeroBudget8 canonical) tag := by
  intro h
  have he := h.1.2.2.1.2.2.1
  cases tag <;> change (0 : Nat) ≥ 1 at he <;> omega

theorem c6_action_cost_guard (tag : Tag) : ¬ C6Accept (doubledCost8 canonical) tag := by
  intro h
  have he := h.1.2.2.1.2.2.1
  cases tag <;> change (1 : Nat) ≥ 2 at he <;> omega

theorem c6_budget_conservation_guard (tag : Tag) : ¬ C6Accept (zeroReturn8 canonical) tag := by
  intro h
  exact assigned_ledger6_guard tag h.1.2.2.2.1

theorem c6_interface_guard (tag : Tag) : ¬ C6Accept (emptyInterface6 canonical) tag := by
  intro h
  have he := h.1.2.2.2.2.1
  cases tag <;> contradiction

theorem c6_writers_guard (tag : Tag) : ¬ C6Accept (noWriters canonical) tag := by
  intro h
  have he := h.1.2.2.1.2.2.2.2.1
  have hf : writers6 (runInputs6 (noWriters canonical) tag) tag = false := by cases tag <;> decide
  rw [hf] at he
  contradiction

theorem c6_rows_guard (tag : Tag) : ¬ C6Accept (noRows canonical tag) tag := by
  intro h
  have he := h.1.2.1.2 .p1w0 .p2w1
  cases tag <;> change (0 : Nat) = 4 at he <;> contradiction

theorem c6_policy_guard (tag : Tag) : ¬ C6Accept (stayPolicy canonical) tag := by
  intro h
  have he := h.1.2.1.2 .p1w0 .p2w1
  cases tag <;> change (0 : Nat) = 4 at he <;> contradiction

theorem c6_P_guard (tag : Tag) : ¬ C6Accept (zeroP canonical) tag := by
  intro h
  have he := h.1.2.1.2 .p1w0 .p2w1
  cases tag <;> change (4 : Nat) = 0 at he <;> contradiction

theorem c6_M_guard (tag : Tag) : ¬ C6Accept (flatM canonical) tag := by
  intro h
  have he := congrFun h.1.2.1.1.1 .p1w0
  cases tag <;> change (0 : Nat) = 1 at he <;> contradiction

theorem c6_positions_guard (tag : Tag) : ¬ C6Accept (flatPositions canonical) tag := by
  intro h
  have hr : predictive (runInputs6 (flatPositions canonical) tag).base.base .p0w0 =
      predictive (runInputs6 (flatPositions canonical) tag).base.base .p3w0 := by
    cases tag <;> decide
  have he := (h.1.2.1.1.2 .p0w0 .p3w0).mp hr
  cases tag <;> change (0 : Nat) = 4 at he <;> contradiction

theorem c6_hazards_guard (tag : Tag) : ¬ C6Accept (noHazards canonical) tag := by
  intro h
  have hr : predictive (runInputs6 (noHazards canonical) tag).base.base .p1w0 =
      predictive (runInputs6 (noHazards canonical) tag).base.base .p1w1 := by
    cases tag <;> decide
  have he := (h.1.2.1.1.2 .p1w0 .p1w1).mp hr
  cases tag <;> change (1 : Nat) = 2 at he <;> contradiction

/-- Eddy's raw zero budget/price/return intervention; only the shared ledger
cell changes. No stored funding bit or code is changed. -/
def zeroLedger6 (a : Assignment) := mapCell a .maintenance (fun l =>
  {l with initialBudget := 0, actionCost := 0, rechargePerAction := 0})

theorem c6_zero_ledger_rejected (tag : Tag) : ¬ C6Accept (zeroLedger6 canonical) tag := by
  intro h
  have he := h.1.2.2.2.2.2.1
  cases tag <;> change (0 : Nat) = 1 at he <;> contradiction

end CSTTT.POS04.Assigned
