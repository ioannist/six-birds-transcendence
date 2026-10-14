import CSTTT.Targets.GenericHandoff.HistoricalSupport
import CSTTT.Targets.GenericHandoff.POS04ReceiverResetProjection
import CSTTT.Targets.GenericHandoff.POS04ExactGameControls
import CSTTT.Targets.GenericHandoff.POS04GameAutonomyTransport

/-! Historical-support F/O autonomy, G6_lane_spec.md §§3,4F,4O and the
manager/Eddy historical-support ruling. Source histories are validated against
RAW source action support. Their actual factor and raw provenance are retained;
the receiver resets probe-local counters/ticks, then every funded TARGET
response branch is executed. Source funding/ticks are not acquisition inputs.
Full autonomy additionally preserves the assigned package, so deleting a source
package primitive can still reject F. Complete lineage is unchanged and keeps
its stronger actual funded-source execution requirement.

No dynamics, observation, entry set, or verdict is supplied. Target game rules
reuse the proved exact assigned O/F interpreters; only their entry construction
is replaced by explicit recorded-history folding, reception, and actual target
updating. All equivalences below quantify arbitrary partial assignments. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalAutonomy
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH
open RegisterInterpreter POS04OperationalGame
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Frozen O's exact live acquisition/response cells, not the full source
updater's dependency set. Withdrawal metadata remain raw RawLaneModel fields. -/
def dependencies : List Cell := phase2Dependencies

def sourceTerminal (policy : KState → Action) (history : List KState) : Option KState :=
  match history with
  | [] => none
  | first::rest => some (HistoricalSupport.fold first (HistoricalSupport.word policy (first::rest)))

theorem source_terminal_eq (policy : KState → Action) (history : List KState) :
    sourceTerminal policy history = history.getLast? := by
  cases history with
  | nil => rfl
  | cons first rest =>
    rw [sourceTerminal,HistoricalSupport.fold_word_terminal policy first rest .p0w0]
    induction rest generalizing first with
    | nil => rfl
    | cons next rest ih => simpa using ih next

theorem source_terminal_nonempty (policy : KState → Action) (history : List KState)
    (hn : history ≠ []) : sourceTerminal policy history = some (history.getLastD .p0w0) := by
  cases history with
  | nil => exact (hn rfl).elim
  | cons first rest =>
    rw [sourceTerminal,HistoricalSupport.fold_word_terminal policy first rest .p0w0]

/-- Raw recorded factor/provenance, followed by receiver reset. Completeness
and the frozen activation/realization/source-support check precede all helper
decoding. An absent cell never supplies an accepted canonical fallback. -/
def arrival (m : RawLaneModel) (rid : RouteId) : Option Run6 :=
  if phase2Check m rid then
    let d := arrivalInputs m
    match routeTuple d.base rid with
    | none => none
    | some (history,path) =>
      match sourceTerminal (clauseExtra (image m.assignment) .source .c6).base.policy history with
      | none => none
      | some last =>
        (POS04ReceiverResetProjection.receiveRetained (image m.assignment)
          (.inK last,(history,path))).map Prod.snd
  else none

/-- Every row element is retained with its exact numerator. No exit branch
is filtered, and the result is the actual updater's outcome, not reception. -/
def phase2Execution (m : RawLaneModel) (rid : RouteId) : List (Nat × Run6) :=
  match arrival m rid with
  | none => []
  | some received =>
    match received.factor with
    | .inK s =>
      let d := arrivalInputs m
      (d.base.base.rows s (d.base.base.policy s)).map fun branch =>
        (branch.2,actualUpdate6 d received (d.base.base.policy s) branch.1)
    | _ => []

def executionEntries (m : RawLaneModel) : List (Nat × Run6) :=
  routeIds.flatMap (phase2Execution m)

def HistoricalEntries (m : RawLaneModel) (r : Run6) : Prop :=
  ∃ numerator, (numerator,r) ∈ executionEntries m

def FullAutonomy (m : RawLaneModel) : Prop :=
  StrategyGame.GameReadout (POS04OperationalGame.rows m) (POS04OperationalGame.update m)
    (HistoricalEntries m) (POS04OperationalGame.Protocol m)
    (POS04FullGame.PackageAt m) (POS04OperationalGame.ResourceClosed m)
    (POS04OperationalGame.Legal m) (POS04OperationalGame.StepLaw m)

def OperationalAutonomy (m : RawLaneModel) : Prop :=
  StrategyGame.GameReadout (POS04OperationalGame.rows m) (POS04OperationalGame.update m)
    (HistoricalEntries m) (POS04OperationalGame.Protocol m)
    (POS04OperationalGame.Inside m) (POS04OperationalGame.ResourceClosed m)
    (POS04OperationalGame.Legal m) (POS04OperationalGame.StepLaw m)

/-- Every consumed cell is present BEFORE helpers are used; activation,
realization and raw source support come from the assigned acquisition check. -/
theorem phase2_facts (m : RawLaneModel) (rid : RouteId) (history : List KState)
    (path : List EventId) (hp : phase2Check m rid = true)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,path)) :
    Complete dependencies (image m.assignment) ∧ history ≠ [] ∧
    active7 (arrivalInputs m).base = true ∧ path6 (arrivalInputs m) rid = true ∧
    pathSupported (clauseExtra (image m.assignment) .source .c6) history = true := by
  have hc : phase2Complete m = true := by
    by_cases h : phase2Complete m = true
    · exact h
    · have hf : phase2Complete m = false := Bool.eq_false_iff.mpr h
      simp [phase2Check,hf] at hp
  have hf : active7 (arrivalInputs m).base = true ∧
      path6 (arrivalInputs m) rid = true ∧
      pathSupported (clauseExtra (image m.assignment) .source .c6) history = true := by
    unfold phase2Check at hp
    split at hp
    · simp at hp
    · simp only [ht] at hp
      split at hp <;> try contradiction
      split at hp <;> try contradiction
      all_goals simp only [Bool.and_eq_true] at hp
      all_goals first
        | exact False.elim (Bool.noConfusion hp.2)
        | exact ⟨hp.1.1.1,hp.1.1.2,hp.1.2⟩
  have hpath := hf.2.1
  simp only [path6,ht,Bool.and_eq_true] at hpath
  have hn : history ≠ [] := List.isEmpty_eq_false_iff.mp (by simpa using hpath.1.1.1.1)
  exact ⟨(of_decide_eq_true hc : Assigned.Complete phase2Dependencies (image m.assignment)),hn,hf⟩

theorem phase2_target_facts (m : RawLaneModel) (rid : RouteId) (history : List KState)
    (path : List EventId) (hp : phase2Check m rid = true)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,path)) :
    available8 (clause8 (image m.assignment) .target) .target = true ∧
    let row := (arrivalInputs m).base.base.rows (history.getLastD .p0w0)
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0))
    row.isEmpty = false ∧ (row.map Prod.snd).sum = 4 ∧
      ∀ e ∈ row, e.2 > 0 ∧ e.1 ∈ ambientStates := by
  unfold phase2Check at hp
  split at hp
  · simp at hp
  · simp only [ht] at hp
    split at hp <;> try contradiction
    split at hp <;> try contradiction
    all_goals simp only [Bool.and_eq_true] at hp
    all_goals first
      | exact False.elim (Bool.noConfusion hp.2)
      | exact ⟨hp.2.1.1.1.1.2,by simpa using hp.2.1.1.2,
          of_decide_eq_true hp.2.1.2,fun e he => of_decide_eq_true (List.all_eq_true.mp hp.2.2 e he)⟩

theorem arrival_computed (m : RawLaneModel) (rid : RouteId) (history : List KState)
    (path : List EventId) (hp : phase2Check m rid = true)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,path)) :
    arrival m rid = some ⟨.inK (history.getLastD .p0w0),0,0,(history,path),
      (arrivalInputs m).base.receiver.funded⟩ := by
  obtain ⟨hc,hn,_⟩ := phase2_facts m rid history path hp ht
  have hr : image m.assignment .receiverInput = some (arrivalInputs m).base.receiver :=
    POS04RegisterDynamics.cell_value (hc .receiverInput (by simp [dependencies,phase2Dependencies]))
  simp only [arrival,hp,if_true,ht,source_terminal_nonempty _ _ hn,
    POS04ReceiverResetProjection.receiveRetained,hr,Option.map_some]

theorem protocol_arrival_budget (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    budgetAfter6 (arrivalInputs m) > 0 := by
  have hl := (protocol_resources m hp).2.1
  change (inputs m).viability.resource.rechargeAvailable = true ∧
    (inputs m).viability.budget.initialBudget = 1 ∧
    (inputs m).viability.budget.actionCost = 1 ∧
    (inputs m).viability.budget.rechargePerAction = 1 ∧ _ at hl
  have he : (arrivalInputs m).ledger = (inputs m).viability.budget := rfl
  change (arrivalInputs m).ledger.initialBudget - (arrivalInputs m).ledger.actionCost +
    (arrivalInputs m).ledger.rechargePerAction > 0
  rw [he,hl.2.1,hl.2.2.1,hl.2.2.2.1]
  decide

/-- The acquired run executes the actual enabled target row. This law needs
only acquisition's own raw gate, not AF, AO, or a funded source assumption. -/
theorem target_response_row (m : RawLaneModel) (rid : RouteId) (history : List KState)
    (path : List EventId) (hp : phase2Check m rid = true)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,path)) :
    let received : Run6 := ⟨.inK (history.getLastD .p0w0),0,0,(history,path),
      (arrivalInputs m).base.receiver.funded⟩
    actualRows6 (arrivalInputs m) received
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) =
      ((arrivalInputs m).base.base.rows (history.getLastD .p0w0)
        ((arrivalInputs m).base.base.policy (history.getLastD .p0w0))).map
        (fun e => (e.1,(e.2 : Rat)/4)) := by
  have ha := (phase2_facts m rid history path hp ht).2.2.1
  have hf : (arrivalInputs m).base.receiver.funded = true := by
    simp only [active7,Bool.and_eq_true] at ha
    exact ha.1.2
  have hav := (phase2_target_facts m rid history path hp ht).1
  simp only [available8,Bool.and_eq_true] at hav
  have hen : enabled6 (arrivalInputs m)
      ⟨.inK (history.getLastD .p0w0),0,0,(history,path),(arrivalInputs m).base.receiver.funded⟩ = true := by
    change ((arrivalInputs m).base.receiver.funded &&
      (clause8 (image m.assignment) .target).resource.rechargeAvailable &&
      decide ((clause8 (image m.assignment) .target).budget.initialBudget ≥
        (clause8 (image m.assignment) .target).budget.actionCost)) = true
    rw [hf]
    simpa only [Bool.true_and,Bool.and_eq_true] using hav.1.1
  simp only [actualRows6,hen,if_true,row6]

theorem target_response_all_support (m : RawLaneModel) (rid : RouteId) (history : List KState)
    (path : List EventId) (hp : phase2Check m rid = true)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,path))
    (branch : Ambient × Nat)
    (hb : branch ∈ (arrivalInputs m).base.base.rows (history.getLastD .p0w0)
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0))) :
    (branch.2,actualUpdate6 (arrivalInputs m)
      ⟨.inK (history.getLastD .p0w0),0,0,(history,path),(arrivalInputs m).base.receiver.funded⟩
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) branch.1)
      ∈ phase2Execution m rid ∧
    StrategyGame.PositiveSupport
      (fun x (_ : LaneDisturbance) act => actualRows6 (arrivalInputs m) x act)
      ⟨.inK (history.getLastD .p0w0),0,0,(history,path),(arrivalInputs m).base.receiver.funded⟩
      .nominal ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) branch.1 := by
  constructor
  · rw [phase2Execution,arrival_computed m rid history path hp ht]
    exact List.mem_map.mpr ⟨branch,hb,rfl⟩
  · refine ⟨(branch.2 : Rat)/4,?_,ScaledRows.positive 4 branch.2 (by decide)
      ((phase2_target_facts m rid history path hp ht).2.2.2 branch hb).1⟩
    dsimp only
    rw [target_response_row m rid history path hp ht]
    exact List.mem_map.mpr ⟨branch,hb,rfl⟩

/-- Equality covers every row branch, including exits. The ledger law is an
independently computed protocol requirement, not an assumed entry result. -/
theorem phase2_execution_eq (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (rid : RouteId) : phase2Execution m rid =
      (phase2Entries m rid).map (fun e => (e.numerator,entryRun m e)) := by
  by_cases hc : phase2Check m rid = true
  · cases ht : routeTuple (arrivalInputs m).base rid with
    | none => simp [phase2Execution,arrival,hc,phase2Entries,ht]
    | some residue =>
      rcases residue with ⟨history,path⟩
      rw [phase2Execution,arrival_computed m rid history path hc ht]
      simp only [phase2Entries,hc,if_true,ht,List.map_map,Function.comp_def]
      apply List.map_congr_left
      intro branch _
      simp only [actualUpdate6,entryRun,protocol_arrival_budget m hp,decide_true,
        Bool.and_true,Nat.zero_add]
      rfl
  · have hf : phase2Check m rid = false := Bool.eq_false_iff.mpr hc
    simp [phase2Execution,arrival,phase2Entries,hf]

theorem execution_entries_eq (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    executionEntries m = (entries m).map (fun e => (e.numerator,entryRun m e)) := by
  simp only [executionEntries,entries,List.map_flatMap]
  apply congrArg (fun f => routeIds.flatMap f)
  funext rid
  exact phase2_execution_eq m hp rid

theorem entries_iff (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6) :
    HistoricalEntries m r ↔ POS04OperationalGame.Entries m r := by
  rw [HistoricalEntries,execution_entries_eq m hp]
  constructor
  · rintro ⟨n,hm⟩
    obtain ⟨e,he,heq⟩ := List.mem_map.mp hm
    exact ⟨e,he,(congrArg Prod.snd heq).symm⟩
  · rintro ⟨e,he,rfl⟩
    exact ⟨e.numerator,List.mem_map.mpr ⟨e,he,rfl⟩⟩

/-- Protocol is read from each game's own raw subcheck. No AF/AO verdict
is supplied as a certificate field; strategy soundness is the committed game
induction, with the newly constructed entry semantics substituted by proof. -/
theorem full_game_iff (m : RawLaneModel) : FullAutonomy m ↔ POS04FullGame.Autonomy m := by
  constructor <;> intro h
  all_goals
    have he : HistoricalEntries m = POS04OperationalGame.Entries m :=
      funext fun r => propext (entries_iff m h.1 r)
  · unfold FullAutonomy at h
    rw [he] at h
    exact h
  · change StrategyGame.GameReadout _ _ _ _ _ _ _ _
    rw [he]
    exact h

theorem operational_game_iff (m : RawLaneModel) :
    OperationalAutonomy m ↔ POS04OperationalGame.Autonomy m := by
  constructor <;> intro h
  all_goals
    have he : HistoricalEntries m = POS04OperationalGame.Entries m :=
      funext fun r => propext (entries_iff m h.1 r)
  · unfold OperationalAutonomy at h
    rw [he] at h
    exact h
  · change StrategyGame.GameReadout _ _ _ _ _ _ _ _
    rw [he]
    exact h

theorem full_game_iff_af (m : RawLaneModel) : FullAutonomy m ↔ AF m :=
  (full_game_iff m).trans (POS04FullGame.game_iff_af m)

theorem operational_game_iff_ao (m : RawLaneModel) : OperationalAutonomy m ↔ AO m :=
  (operational_game_iff m).trans (POS04OperationalGame.game_iff_ao m)

theorem full_implies_package (m : RawLaneModel) (h : FullAutonomy m) : PackageLane m.assignment :=
  POS04FullGame.full_implies_arrival m ((full_game_iff m).mp h)

theorem full_implies_operational (m : RawLaneModel) (h : FullAutonomy m) : OperationalAutonomy m :=
  (operational_game_iff m).mpr (POS04ExactGames.full_implies_operational m ((full_game_iff m).mp h))

/-- Response probabilities are the actual enabled target probabilities on
EVERY resource-safe run, not just at canonical entries. -/
theorem responses_are_actual_rows (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (r : Run6) (hr : POS04OperationalGame.ResourceClosed m r) (d : LaneDisturbance) (act : Action) :
    POS04OperationalGame.rows m r d act =
      actualRows6 (runInputs6 (withdrawnAssignment m) .target) r act := by
  have hav := hr.1
  simp only [available8,Bool.and_eq_true] at hav
  have hen : enabled6 (runInputs6 (withdrawnAssignment m) .target) r = true := by
    change (r.funded && (inputs m).viability.resource.rechargeAvailable &&
      decide ((inputs m).viability.budget.initialBudget ≥ (inputs m).viability.budget.actionCost)) = true
    rw [hr.2.2.1]
    simpa only [Bool.true_and,Bool.and_eq_true] using hav.1.1
  simp only [POS04OperationalGame.rows,if_pos (protocol_complete m hp),actualRows6,hen,if_true]
  cases r.factor <;> rfl

/-- TTH-05 uses the actual strategy-invariant image, with all support
branches and every entry. The historical acquisition has no role in supplying
post-withdrawal resources. These reuse the proved finite-factor lifting laws. -/
theorem full_each_entry_exact (m : RawLaneModel) (hg : FullAutonomy m) :
    ∃ cert : POS04FullGame.Certificate m,
      ∀ entry, HistoricalEntries m entry →
        Nonempty (CSTTT.AutonomyTheory.ExactAutonomyCertificate
          (GameAutonomyTransport.projectedData (POS04GameAutonomyTransport.factor m) cert
            POS04GameAutonomyTransport.project entry)) := by
  obtain ⟨cert,hcert⟩ := POS04GameAutonomyTransport.full_game_each_entry_exact m ((full_game_iff m).mp hg)
  exact ⟨cert,fun entry he => hcert entry ((entries_iff m hg.1 entry).mp he)⟩

theorem full_each_entry_words (m : RawLaneModel) (hg : FullAutonomy m) :
    ∃ cert : POS04FullGame.Certificate m,
      ∀ entry, HistoricalEntries m entry → ∀ word : List LaneDisturbance,
        ∃ y, CSTTT.AutonomyTheory.ControlledRun
          (GameAutonomyTransport.projectedData (POS04GameAutonomyTransport.factor m) cert
            POS04GameAutonomyTransport.project entry)
          (POS04GameAutonomyTransport.project entry) word y ∧ packageAtCheck m y = true := by
  obtain ⟨cert,hcert⟩ := POS04GameAutonomyTransport.full_game_each_entry_words m ((full_game_iff m).mp hg)
  exact ⟨cert,fun entry he => hcert entry ((entries_iff m hg.1 entry).mp he)⟩

theorem exact_dependency_scope (k : Cell) :
    k ∈ POS04OperationalGame.dependencies ↔ k ∈ dependencies := by
  simp [POS04OperationalGame.dependencies,dependencies,autonomyInputs,phase2Dependencies,clauseScope]
  grind

theorem all_consumed_missing_inputs_reject (m : RawLaneModel) (k : Cell)
    (hk : k ∈ POS04OperationalGame.dependencies) (hm : image m.assignment k = none) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m :=
  ⟨fun h => (POS04ExactGames.missing_input_rejects_both m k hk hm).1 ((full_game_iff m).mp h),
   fun h => (POS04ExactGames.missing_input_rejects_both m k hk hm).2 ((operational_game_iff m).mp h)⟩

theorem source_ticks_not_in_scope : Cell.ticks .source ∉ dependencies := by decide
theorem source_resources_not_in_scope : Cell.resources .source ∉ dependencies := by decide
theorem hazards_not_in_scope : Cell.hazards ∉ dependencies := by decide

theorem execution_entries_positive (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (e : Nat × Run6) (he : e ∈ executionEntries m) :
    e.1 > 0 ∧ e.2.funded = true ∧ writer (inputs m) e.2.residue = true := by
  rw [execution_entries_eq m hp] at he
  obtain ⟨raw,hr,rfl⟩ := List.mem_map.mp he
  have hf := entry_facts m hp raw hr
  exact ⟨hf.1,hf.2.2.2.2,hf.2.2.2.1⟩

theorem source_history_eq (a : CSTTT.POS04.Assigned.Assignment) (rid : RouteId)
    (history : List KState) (path : List EventId)
    (ht : routeTuple (runInputs6 a .target).base rid = some (history,path)) :
    acquisitionHistory a .source rid = history := by
  have hrs : (runInputs6 a .source).base.routes = (runInputs6 a .target).base.routes := rfl
  have hhs : (runInputs6 a .source).base.histories = (runInputs6 a .target).base.histories := rfl
  unfold acquisitionHistory
  rw [hrs,hhs]
  cases hr : (runInputs6 a .target).base.routes.find? (fun v => v.id == rid) with
  | none => simp [routeTuple,hr] at ht
  | some route =>
    have heq : ((runInputs6 a .target).base.histories route.sourceHistory,route.eventPath) =
        (history,path) := Option.some.inj (by simpa only [routeTuple,hr,Option.map_some] using ht)
    exact congrArg Prod.fst heq

theorem retained_fold_lift (first : KState) (rawWord : List (Action × KState))
    (residue : List KState × List EventId) :
    POS04ReceiverResetProjection.retainedFold (.inK first,residue)
      (rawWord.map fun e => (LaneDisturbance.nominal,e.1,Ambient.inK e.2)) =
      (.inK (HistoricalSupport.fold first rawWord),residue) := by
  induction rawWord generalizing first with
  | nil => rfl
  | cons step rest ih => exact ih step.2

theorem full_source_fold_coordinates (a : CSTTT.POS04.Assigned.Assignment) (rid : RouteId)
    (history : List KState) (path : List EventId)
    (ht : routeTuple (runInputs6 a .target).base rid = some (history,path)) (hn : history ≠ []) :
    POS04ReceiverResetProjection.retain
      (POS04RouteExecution.actualFold a .source (acquisitionInitialRun a .source rid)
        (POS04RouteExecution.wordFor a rid)) = (.inK (history.getLastD .p0w0),(history,path)) := by
  rw [POS04ReceiverResetProjection.actual_fold_projects]
  have hs := source_history_eq a rid history path ht
  have hts : routeTuple (runInputs6 a .source).base rid = some (history,path) := ht
  simp only [POS04ReceiverResetProjection.retain,acquisitionInitialRun,hs,hts,Option.getD_some,
    POS04RouteExecution.wordFor]
  cases history with
  | nil => exact (hn rfl).elim
  | cons first rest =>
    rw [show ((first::rest).zip ((first::rest).drop 1)).map
      (fun e => (LaneDisturbance.nominal,(runInputs6 a .source).base.base.policy e.1,Ambient.inK e.2)) =
      (HistoricalSupport.word (runInputs6 a .source).base.base.policy (first::rest)).map
        (fun e => (LaneDisturbance.nominal,e.1,Ambient.inK e.2)) from by
      simp only [HistoricalSupport.word,List.map_map,Function.comp_def]]
    change POS04ReceiverResetProjection.retainedFold (.inK first,(first::rest,path))
      ((HistoricalSupport.word (runInputs6 a .source).base.base.policy (first::rest)).map
        fun e => (LaneDisturbance.nominal,e.1,Ambient.inK e.2)) = _
    rw [retained_fold_lift,HistoricalSupport.fold_word_terminal _ first rest .p0w0]

/-- Necessary stronger-source conditions are CHECKED: complete full updater
inputs and supportedWord on every actual history step. That recursive check
tests enabled source rows (source funding, recharge, affordability), declared
actions/disturbances, and positive actual-outcome probabilities at each step.
It is not a supplied source-execution-success flag. -/
def FundedSourceExecution (a : CSTTT.POS04.Assigned.Assignment) (rid : RouteId) : Prop :=
  Complete POS04RouteExecution.dependencies a ∧
    POS04RouteExecution.supportedWord a .source (acquisitionInitialRun a .source rid)
      (POS04RouteExecution.wordFor a rid) = true

theorem funded_source_executes (a : CSTTT.POS04.Assigned.Assignment) (rid : RouteId)
    (hs : FundedSourceExecution a rid) :
    AcquisitionExecution.HistoryExecution POS04RouteExecution.acquisition a
      (POS04RouteExecution.ready a hs.1)
      (POS04RouteExecution.frame .source (acquisitionInitialRun a .source rid))
      (POS04RouteExecution.wordFor a rid)
      (AcquisitionExecution.foldHistory POS04RouteExecution.acquisition a
        (POS04RouteExecution.ready a hs.1)
        (POS04RouteExecution.frame .source (acquisitionInitialRun a .source rid))
        (POS04RouteExecution.wordFor a rid)) :=
  AcquisitionExecution.history_check_executes _ _ _ _ _
    ((POS04RouteExecution.supported_word_iff a hs.1 .source _ _).mpr hs.2)

/-- Every supported full execution has the SAME received value as the
historical interpreter, under the full source-execution conditions. Historical
support alone is deliberately not asserted to imply funded source execution. -/
theorem reception_agrees_funded_execution (m : RawLaneModel) (rid : RouteId)
    (hp : phase2Check m rid = true)
    (hs : FundedSourceExecution (image m.assignment) rid) :
    (POS04RouteExecution.receiveProgram ()).eval (image m.assignment)
      (AcquisitionExecution.foldHistory POS04RouteExecution.acquisition (image m.assignment)
        (POS04RouteExecution.ready (image m.assignment) hs.1)
        (POS04RouteExecution.frame .source (acquisitionInitialRun (image m.assignment) .source rid))
        (POS04RouteExecution.wordFor (image m.assignment) rid)) (rid,rid) =
      (arrival m rid).map (fun x => (Tag.target,x)) := by
  cases ht : routeTuple (arrivalInputs m).base rid with
  | none => simp [phase2Check,ht] at hp
  | some residue =>
    rcases residue with ⟨history,path⟩
    have hf := phase2_facts m rid history path hp ht
    rw [POS04RouteExecution.fold_eq _ hs.1,POS04ReceiverResetProjection.receive_expression_projects,
      full_source_fold_coordinates _ rid history path ht hf.2.1]
    rw [arrival_computed m rid history path hp ht]
    have hr : image m.assignment .receiverInput = some (arrivalInputs m).base.receiver :=
      POS04RegisterDynamics.cell_value (hf.1 .receiverInput (by simp [dependencies,phase2Dependencies]))
    simp [POS04ReceiverResetProjection.receiveRetained,hr]

/-- Together with the reception equation, these equalities cover the exact
target row and updater for ALL target outcomes, hence every supported branch.
They require the stronger runtime's full input completeness; reception already
accounts for the additional funded source-history condition. -/
theorem target_step_agrees_runtime (m : RawLaneModel)
    (hc : Complete POS04RouteExecution.dependencies (image m.assignment))
    (received : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    AcquisitionExecution.rows POS04RouteExecution.acquisition (image m.assignment)
      (POS04RouteExecution.frame .target received) d act = actualRows6 (arrivalInputs m) received act ∧
    AcquisitionExecution.update POS04RouteExecution.acquisition (image m.assignment)
      (POS04RouteExecution.ready _ hc) (POS04RouteExecution.frame .target received) d act o =
      POS04RouteExecution.frame .target (actualUpdate6 (arrivalInputs m) received act o) :=
  ⟨POS04RouteExecution.rows_eq _ hc .target received d act,
    POS04RouteExecution.update_eq _ hc .target received d act o⟩

/-- Agreement as a genuine stronger-runtime ARRIVAL, not just a pure fold.
Besides funded source execution, the stronger runtime must check its own raw
path/activation conditions (in particular mix on THIS path). All these checks
interpret the same assignment. They are not added to the frozen F/O gates. -/
theorem stronger_arrival_agreement (m : RawLaneModel) (rid : RouteId)
    (hp : phase2Check m rid = true)
    (hs : FundedSourceExecution (image m.assignment) rid)
    (hpath : AcquisitionExecution.PathCheck POS04ExecutionFrontier.schema
      (POS04RouteExecution.eventsFor (image m.assignment))
      ((image m.assignment .realized).getD (canonicalValue .realized))
      (POS04RouteExecution.pathsFor (image m.assignment) rid).path)
    (hactive : AcquisitionExecution.Activated
      (POS04RouteExecution.receiverFor (image m.assignment))
      (POS04RouteExecution.eventsFor (image m.assignment))
      ((image m.assignment .realized).getD (canonicalValue .realized))
      (POS04RouteExecution.pathsFor (image m.assignment) rid).path) :
    ∃ received, arrival m rid = some received ∧
      AcquisitionExecution.Arrival POS04ExecutionFrontier.schema POS04RouteExecution.acquisition
        (image m.assignment) (POS04RouteExecution.ready _ hs.1) rid
        (POS04RouteExecution.frame .target received) := by
  refine ⟨POS04RouteExecution.arrivalRun (image m.assignment) rid,?_,?_⟩
  · cases ht : routeTuple (arrivalInputs m).base rid with
    | none => simp [phase2Check,ht] at hp
    | some residue =>
      rcases residue with ⟨history,path⟩
      have hf := phase2_facts m rid history path hp ht
      have hcoord := full_source_fold_coordinates (image m.assignment) rid history path ht hf.2.1
      have hfactor := congrArg Prod.fst hcoord
      have hresidue := congrArg Prod.snd hcoord
      change (POS04RouteExecution.actualFold _ _ _ _).factor = _ at hfactor
      change (POS04RouteExecution.actualFold _ _ _ _).residue = _ at hresidue
      rw [arrival_computed m rid history path hp ht,POS04RouteExecution.arrivalRun,hfactor,hresidue]
      rfl
  · apply (POS04RouteExecution.arrival_readout_iff _ hs.1 rid _).mpr
    exact ⟨by cases rid <;> decide,hpath,hactive,hs.2,rfl⟩

theorem positive_games : FullAutonomy baseline ∧ OperationalAutonomy baseline :=
  ⟨(full_game_iff_af _).mpr baseline_AF,(operational_game_iff_ao _).mpr baseline_AO⟩

theorem missing_past_ticks_historical_operational :
    OperationalAutonomy POS04RuntimeEquivalenceBoundary.missingPastTicks :=
  (operational_game_iff_ao _).mpr POS04RuntimeEquivalenceBoundary.legacy_operational_accepts

theorem missing_past_ticks_historical_full_rejects :
    ¬ FullAutonomy POS04RuntimeEquivalenceBoundary.missingPastTicks :=
  fun h => POS04RuntimeEquivalenceBoundary.legacy_full_rejects ((full_game_iff_af _).mp h)

theorem source_recharge_unavailable_historical_operational :
    OperationalAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable :=
  (operational_game_iff_ao _).mpr POS04ReceiverResetProjection.diagnostic_legacy_operational_accepts

theorem source_recharge_unavailable_historical_full :
    FullAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable := by
  apply (full_game_iff_af _).mpr
  unfold AF
  decide +kernel

theorem source_recharge_unavailable_no_complete_lineage :
    ¬ POS04CompleteLineage.StrictTemporalLineage POS04ReceiverResetProjection.sourceRechargeUnavailable := by
  intro hl
  have hc := hl.2.2.2.2.2.1.1
  have hr := hl.2.2.2.2.2.1.2
  change POS04RouteReadout.RouteReadout POS04ReceiverResetProjection.diagnosticAssignment at hr
  have hp := (POS04RouteReadout.route_readout_iff _ hc).mpr hr
  obtain ⟨ready,r,s,_,_,_,_,rr,sr,nr,ns,endpoint,_,_,hret,_⟩ := hp
  obtain ⟨entry,he⟩ := hret.2.1
  obtain ⟨arrived,d,act,o,ha,_,_⟩ := RouteComponent.result_actual_update _ _ _ _ r entry he
  exact POS04ReceiverResetProjection.diagnostic_no_arrival ready.1 r arrived ha

theorem source_recharge_unavailable_no_funded_execution (rid : RouteId) :
    ¬ FundedSourceExecution POS04ReceiverResetProjection.diagnosticAssignment rid := by
  intro hs
  exact POS04ReceiverResetProjection.diagnostic_no_source_history
    (POS04RouteExecution.ready _ hs.1) _ _ (by cases rid <;> decide +kernel) _
    (funded_source_executes _ rid hs)

theorem positive_funded_source_execution (rid : RouteId) :
    FundedSourceExecution canonical rid :=
  ⟨canonical_complete _,by cases rid <;> decide +kernel⟩

theorem source_recharge_unavailable_arrival (rid : RouteId) :
    arrival POS04ReceiverResetProjection.sourceRechargeUnavailable rid = some (POS04RouteExecution.arrivalFor rid) := by
  cases rid <;> decide +kernel

theorem missing_past_ticks_historical_arrival (rid : RouteId) :
    arrival POS04RuntimeEquivalenceBoundary.missingPastTicks rid = some (POS04RouteExecution.arrivalFor rid) := by
  cases rid <;> decide +kernel

theorem registered_game_vectors :
    (¬ FullAutonomy packageDeletion ∧ OperationalAutonomy packageDeletion) ∧
    (FullAutonomy lineageDeletion ∧ OperationalAutonomy lineageDeletion) ∧
    (¬ FullAutonomy withdrawalDeletion ∧ ¬ OperationalAutonomy withdrawalDeletion) := by
  exact ⟨⟨fun h => package_deletion_not_AF ((full_game_iff_af _).mp h),
    (operational_game_iff_ao _).mpr package_deletion_AO⟩,
    ⟨(full_game_iff_af _).mpr lineage_deletion_AF,(operational_game_iff_ao _).mpr lineage_deletion_AO⟩,
    ⟨fun h => withdrawal_deletion_not_AF ((full_game_iff_af _).mp h),
      fun h => withdrawal_deletion_not_AO ((operational_game_iff_ao _).mp h)⟩⟩

/-- Source absence, ownership, withdrawal, ledger, ticks and writer controls
are semantic game negatives, not a failed sufficient constructor. -/
theorem source_absent_no_games (m : RawLaneModel)
    (h : (arrivalInputs m).base.receiver.sourcePresent = false) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have old := POS04ExactGames.source_absent_rejects_both m h
  exact ⟨fun hf => old.1 ((full_game_iff m).mp hf),fun ho => old.2 ((operational_game_iff m).mp ho)⟩

theorem invalid_ledger_no_games (m : RawLaneModel) (h : ¬ Ledger8 (withdrawnInputs m)) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have old := POS04OperationalGame.invalid_ledger_rejected m h
  exact ⟨fun hf => old ((operational_game_iff m).mp (full_implies_operational m hf)),
    fun ho => old ((operational_game_iff m).mp ho)⟩

theorem wrong_owner_no_games (m : RawLaneModel) (h : (withdrawnInputs m).resource.owner ≠ .target) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have old := POS04OperationalGame.wrong_owner_rejected m h
  exact ⟨fun hf => old ((operational_game_iff m).mp (full_implies_operational m hf)),
    fun ho => old ((operational_game_iff m).mp ho)⟩

theorem invalid_withdrawal_no_games (m : RawLaneModel) (h : withdrawalCheck m = false) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have old := POS04OperationalGame.invalid_withdrawal_rejected m h
  exact ⟨fun hf => old ((operational_game_iff m).mp (full_implies_operational m hf)),
    fun ho => old ((operational_game_iff m).mp ho)⟩

theorem wrong_tick_no_games (m : RawLaneModel) (s : KState) (act : Action)
    (hn : ((withdrawnInputs m).rows s act).isEmpty = false)
    (bad : (inputs m).ticks s act ≠ 1) : ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have old := POS04OperationalGame.wrong_tick_rejected m s act hn bad
  exact ⟨fun hf => old ((operational_game_iff m).mp (full_implies_operational m hf)),
    fun ho => old ((operational_game_iff m).mp ho)⟩

theorem writer_unavailable_no_games (m : RawLaneModel)
    (bad : ∀ residue, writer (inputs m) residue = false) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have old := POS04OperationalGame.missing_writer_rejected m bad
  exact ⟨fun hf => old ((operational_game_iff m).mp (full_implies_operational m hf)),
    fun ho => old ((operational_game_iff m).mp ho)⟩

/-- Sensitivity rules, declared before their checks: erase every recorded
source row; or remove mix2 from the realized-stage cell. Neither changes the
receiver operation, raw target responses or withdrawal metadata. -/
def erasedSourceRows : RawLaneModel :=
  {baseline with assignment := (put canonical (.rows .target) (some (fun _ _ => [])))}
def unrealizedMix2 : RawLaneModel :=
  {baseline with assignment := mapCell canonical .realized (fun ss => ss.filter (fun s => s != .mix2))}

theorem erased_source_histories_rejected : executionEntries erasedSourceRows = [] := by
  unfold executionEntries
  apply List.flatMap_eq_nil_iff.mpr
  intro rid _
  have hp : phase2Check erasedSourceRows rid = false := by cases rid <;> decide +kernel
  simp [phase2Execution,arrival,hp]

theorem unrealized_path_rejected : executionEntries unrealizedMix2 = [] := by
  unfold executionEntries
  apply List.flatMap_eq_nil_iff.mpr
  intro rid _
  have hp : phase2Check unrealizedMix2 rid = false := by cases rid <;> decide +kernel
  simp [phase2Execution,arrival,hp]

theorem no_entries_no_games (m : RawLaneModel) (hn : executionEntries m = []) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have bad : ∀ r, ¬ HistoricalEntries m r := by simp [HistoricalEntries,hn]
  exact ⟨StrategyGame.no_entries_no_game bad,StrategyGame.no_entries_no_game bad⟩

theorem raw_source_and_realization_guards :
    (¬ FullAutonomy erasedSourceRows ∧ ¬ OperationalAutonomy erasedSourceRows) ∧
    (¬ FullAutonomy unrealizedMix2 ∧ ¬ OperationalAutonomy unrealizedMix2) :=
  ⟨no_entries_no_games _ erased_source_histories_rejected,no_entries_no_games _ unrealized_path_rejected⟩

theorem missing_acquisition_rejected (m : RawLaneModel) (k : Cell)
    (hk : k ∈ dependencies) (hm : image m.assignment k = none) :
    executionEntries m = [] := by
  unfold executionEntries
  apply List.flatMap_eq_nil_iff.mpr
  intro rid _
  have hf := phase2_missing_staged_cell m k hk hm rid
  simp [phase2Execution,arrival,hf]

theorem missing_acquisition_no_games (m : RawLaneModel) (k : Cell)
    (hk : k ∈ dependencies) (hm : image m.assignment k = none) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have hn : ∀ r, ¬ HistoricalEntries m r := by
    simp [HistoricalEntries,missing_acquisition_rejected m k hk hm]
  exact ⟨StrategyGame.no_entries_no_game hn,StrategyGame.no_entries_no_game hn⟩

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalAutonomy
