import CSTTT.POS04.Data

/-! Structural checks for the frozen FIACH-POS-04 raw declaration.
These establish only table identity, references, and finite well-formedness.
Clause and handoff predicates belong to later packets. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

theorem index_stateAt (i : I) : index (stateAt i) = i := by
  decide +revert

theorem stateAt_index (s : KState) : stateAt (index s) = s := by
  cases s <;> decide

/-- Each tagged factor is the exact T1 canonical transition table. -/
theorem tag_isomorphism (tag : Tag) (i j : I) :
    taggedPNum tag (stateAt i) (stateAt j) = pNum i j := by
  simp [taggedPNum, index_stateAt]

theorem swap_tag_involutive (tag : Tag) : swapTag (swapTag tag) = tag := by
  cases tag <;> rfl

theorem swap_tagged_involutive (x : TaggedState) :
    swapTagged (swapTagged x) = x := by
  cases x with
  | mk tag s => cases tag <;> rfl

theorem tag_swap_preserves_P (tag : Tag) (s t : KState) :
    taggedPNum (swapTag tag) s t = taggedPNum tag s t := by rfl

theorem tag_swap_preserves_M (tag : Tag) (s : KState) :
    taggedMClass (swapTag tag) s = taggedMClass tag s := by rfl

theorem declared_cu_is_t1 :
    ∀ i j : I,
      sum7 (fun k => cIndicator i k * uPrototypeNum k j) = CU.num i j := by
  decide

theorem t1_slip_entries :
    pNum (index .p2w1) (index .p1w0) = slipAdvanceNum ∧
    pNum (index .p2w1) (index .p1w1) = slipHoldNum ∧
    pNum (index .p5w0) (index .p1w1) = slipAdvanceNum ∧
    pNum (index .p5w0) (index .p1w0) = slipHoldNum := by decide

theorem tagged_rows_stochastic (tag : Tag) (s : KState) :
    sum10 (fun j => taggedPNum tag s (stateAt j)) = 4 := by
  simp only [taggedPNum, index_stateAt]
  exact p_rows_stochastic (index s)

theorem tagged_canonical_row_is_t1 (tag : Tag) (s : KState) :
    actionRow tag s (canonicalAction s) = canonicalRow s := by
  simp [actionRow]

/-- The canonical raw action table used by later lanes is pointwise the
tagged T1 transition table, including its zero entries. -/
theorem canonical_action_row_agrees_with_tagged_P (tag : Tag) (s t : KState) :
    rowWeight (actionRow tag s (canonicalAction s)) t = taggedPNum tag s t := by
  cases tag <;> cases s <;> cases t <;> decide

theorem ambient_states_distinct : ambientStates.Nodup := by decide

theorem hazard_rule_matches_ambient_exits :
    isLethalHazard .p2w0 = true ∧ isLethalHazard .p5w1 = true ∧
    ∀ s : KState, isLethalHazard (.inK s) = false := by
  constructor
  · decide
  constructor
  · decide
  · intro s; cases s <;> decide

theorem kernel_states_in_ambient :
    ∀ s ∈ kernel, Ambient.inK s ∈ ambientStates := by decide

theorem action_targets_in_ambient :
    ∀ tag : Tag, ∀ s : KState, ∀ a : Action,
      ∀ entry ∈ actionRow tag s a, entry.1 ∈ ambientStates ∧ entry.2 > 0 := by
  intro tag s a
  cases tag <;> cases s <;> cases a <;> decide

/-- T1 C1 is transported along each tag isomorphism. No rational entry or
fixed-point system is recomputed in this proof. -/
theorem c1_probability_each_tag (tag : Tag) :
    TaggedProbability tag taggedPi := by
  simpa [TaggedProbability, taggedPi] using pi_probability

theorem c1_fixed_each_tag (tag : Tag) :
    TaggedFixed tag taggedPi := by
  simpa [TaggedFixed, taggedPi] using pi_fixed

theorem c1_unique_each_tag (tag : Tag) (μ : TaggedIndex → Rat)
    (hp : TaggedProbability tag μ) (hf : TaggedFixed tag μ) :
    ∀ i : I, μ (tag,i) = taggedPi (tag,i) := by
  have h := pi_unique (fun i => μ (tag,i)) hp hf
  intro i
  exact congrFun h i

theorem c1_nonuniform_each_tag (tag : Tag) :
    (fun i : I => taggedPi (tag,i)) ≠ uniform := by
  simpa [taggedPi] using pi_nonuniform

theorem c1_core_mass_each_tag (tag : Tag) :
    taggedCoreMass tag = 77/80 := by
  simpa [taggedCoreMass, taggedPi] using pi_core_mass

theorem c1_retention_each_tag (tag : Tag) :
    taggedCoreMass tag ≥ 3/4 := by
  simpa [taggedCoreMass, taggedPi] using pi_core_retention

theorem c1_tv_each_tag (tag : Tag) :
    taggedTV tag = 3/80 := by
  simpa [taggedTV, taggedPi] using pi_tv_from_core_uniform

theorem c1_defect_each_tag (tag : Tag) :
    taggedDefect tag = 78795/524288 := by
  simpa [taggedDefect] using e2eps_defect

theorem stages_distinct : stages.Nodup := by decide
theorem event_ids_distinct : eventIds.Nodup := by decide
theorem event_references_resolve :
    ∀ e ∈ events, e.fromStage ∈ stages ∧ e.toStage ∈ stages := by decide
theorem events_strict_and_atomic :
    ∀ e ∈ events, e.strictStep = true ∧ e.atomic = true := by decide
theorem events_realized :
    ∀ e ∈ events, e.fromStage ∈ realizedStages ∧ e.toStage ∈ realizedStages := by decide
theorem event_lookup_complete :
    ∀ id ∈ eventIds, (eventOf id).id = id := by decide

def supportedHistory (tag : Tag) (id : HistoryId) : Bool :=
  ((sourceHistory id).zip ((sourceHistory id).drop 1)).all fun pair =>
    decide (taggedPNum tag pair.1 pair.2 > 0)

theorem source_histories_supported :
    ∀ tag : Tag, ∀ id : HistoryId, supportedHistory tag id = true := by
  intro tag id
  cases tag <;> cases id <;> decide

theorem source_history_states_in_ambient :
    ∀ id : HistoryId, ∀ s ∈ sourceHistory id,
      Ambient.inK s ∈ ambientStates := by
  intro id
  cases id <;> decide

theorem target_histories_are_tag_swap (id : HistoryId) :
    taggedHistory .target id = (taggedHistory .source id).map swapTagged := by
  cases id <;> decide

def routeReferencesResolve (id : RouteId) : Bool :=
  let route := routeOf id
  decide (route.sourceHistory ∈ historyIds) &&
    route.eventPath.all (fun event => decide (event ∈ eventIds))

theorem route_references_resolve :
    ∀ id : RouteId, routeReferencesResolve id = true := by
  intro id
  cases id <;> decide

def routeEventsCompose (id : RouteId) : Bool :=
  let path := (routeOf id).eventPath
  decide ((path.head?).map (fun e => (eventOf e).fromStage) = some Stage.sourceLive) &&
    ((path.zip (path.drop 1)).all fun pair =>
      decide ((eventOf pair.1).toStage = (eventOf pair.2).fromStage)) &&
    decide ((path.getLast?).map (fun e => (eventOf e).toStage) = some Stage.targetExit)

theorem route_event_paths_compose :
    ∀ id : RouteId, routeEventsCompose id = true := by
  intro id
  cases id <;> decide

theorem route_event_paths_realized :
    ∀ id : RouteId, ((routeOf id).eventPath).all (fun event =>
      decide ((eventOf event).fromStage ∈ realizedStages ∧
              (eventOf event).toStage ∈ realizedStages)) = true := by
  intro id
  cases id <;> decide

theorem route_histories_supported :
    ∀ tag : Tag, ∀ id : RouteId,
      supportedHistory tag (routeOf id).sourceHistory = true := by
  intro tag id
  cases tag <;> cases id <;> decide

theorem route_tuples_are_raw :
    ∀ id : RouteId,
      routeRegister id =
        (sourceHistory (routeOf id).sourceHistory, (routeOf id).eventPath) := by
  intro id
  rfl

theorem canonical_action_rows_scaled_stochastic :
    ∀ s : KState,
      (canonicalRow s).foldl (fun n x => n + x.2) 0 = 4 := by
  intro s
  cases s <;> decide

theorem every_action_row_shape :
    ∀ tag : Tag, ∀ s : KState, ∀ a : Action,
      actionRow tag s a = [] ∨
        (actionRow tag s a).foldl (fun n x => n + x.2) 0 = 4 := by
  intro tag s a
  cases tag <;> cases s <;> cases a <;> decide

set_option maxRecDepth 8192 in
theorem coordinates_count : coordinates.length = 160 := by decide
set_option maxRecDepth 8192 in
theorem coordinates_distinct : coordinates.Nodup := by decide
theorem staged_map_count : stagedClauseMap.length = 8 := by decide
theorem clause_coordinates_complete (tag : Tag) (s : KState) (c : Clause) :
    ⟨tag,s,c⟩ ∈ coordinates := by
  cases tag <;> cases s <;> cases c <;> decide

theorem c7_reassembly_typed :
    ∀ tag : Tag, ∀ id : AssemblageId, reassembly tag id = id := by
  intro tag id
  rfl

def couplingWellFormed (id : AssemblageId) : Bool :=
  let pairs := coupling id
  pairs.length == 2 && pairs.Nodup &&
    ((pairs.map Prod.fst) == [0,1]) &&
    pairs.all (fun pair => pair.2 ∈ ([0,1] : List (Fin 2)))

theorem c7_couplings_wellformed :
    ∀ id : AssemblageId, couplingWellFormed id = true := by
  intro id
  cases id <;> decide

theorem c7_reassembly_consistent :
    ∀ tag : Tag, ∀ id : AssemblageId,
      coupling (reassembly tag id) = coupling id := by
  intro tag id
  rfl

theorem realized_stages_resolve :
    ∀ stage ∈ realizedStages, stage ∈ stages := by decide

theorem receiver_raw_fields :
    receiver.latentFactor = .p0w0 ∧ receiver.funded = true ∧
    receiver.initialBudget = 1 ∧ receiver.sourcePresent = true ∧
    receiver.targetReceiverFunded = true ∧ receiver.mixedEventRequired = true := by
  decide

theorem ledger_raw_fields :
    ledger.actionCost = 1 ∧ ledger.rechargePerAction = 1 ∧
    ledger.initialBudget = 1 ∧ ledger.sourceAvailableAfterWithdrawal = false := by
  decide

theorem resources_target_owned :
    resourceOwner .target = .target ∧
    rechargeAvailableAfterWithdrawal .target = true := by decide

end CSTTT.POS04
