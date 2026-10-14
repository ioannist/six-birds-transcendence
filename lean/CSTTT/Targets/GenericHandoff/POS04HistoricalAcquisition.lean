import CSTTT.Targets.GenericHandoff.HistoricalAcquisition
import CSTTT.Targets.GenericHandoff.POS04HistoricalAutonomy

/-! Typed raw POS-04 instance of historical acquisition. This is the
ACQUISITION component instance, not yet the package/resource-game equivalence
or RawHandoff assembly. Tables and programs reuse the declared POS-04 cells.
The K-only historical table retains precisely edges whose destination is a
recorded K coordinate; target execution separately keeps ALL ambient outcomes.
In particular no exit is filtered from the phase-2 response. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalAcquisition
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter RegisterInitialization POS04RegisterDynamics
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Exact rational pullback of the raw action support to recorded K histories.
The phase-2 execution uses enabledRow below, without this pullback. -/
def historyRows (rs : KState → Action → List (Ambient × Nat)) :
    KState → Action → List (KState × Rat) := fun s act =>
  (rs s act).filterMap fun e => match e.1 with
  | .inK t => some (t,(e.2 : Rat)/4)
  | _ => none


/-- All matching row entries contribute to frozen rowWeight. In particular,
a zero first entry does not hide a later positive duplicate destination. -/
theorem row_weight_support_iff (row : List (Ambient × Nat)) (t : KState) :
    rowWeight row t > 0 ↔ ∃ n, (Ambient.inK t,n) ∈ row ∧ n > 0 := by
  rw [POS04ObjecthoodQuotient.rowWeight_sum]
  induction row with
  | nil => simp
  | cons e rest ih =>
    rcases e with ⟨o,n⟩
    simp only [List.map_cons,List.sum_cons]
    by_cases ho : o = Ambient.inK t
    · subst o
      simp only [ite_true]
      constructor
      · intro h
        by_cases hn : n > 0
        · exact ⟨n,List.mem_cons_self,hn⟩
        · have hr : (rest.map fun e => if e.1 = .inK t then e.2 else 0).sum > 0 := by omega
          obtain ⟨w,hw,hp⟩ := ih.mp hr
          exact ⟨w,List.mem_cons_of_mem _ hw,hp⟩
      · rintro ⟨w,hw,hp⟩
        simp only [List.mem_cons] at hw
        rcases hw with hw | hw
        · have hn : w = n := congrArg Prod.snd hw
          omega
        · have hr := ih.mpr ⟨w,hw,hp⟩
          omega
    · simp only [ho,ite_false,Nat.zero_add]
      constructor
      · intro h
        obtain ⟨w,hw,hp⟩ := ih.mp h
        exact ⟨w,List.mem_cons_of_mem _ hw,hp⟩
      · rintro ⟨w,hw,hp⟩
        simp only [List.mem_cons] at hw
        rcases hw with hw | hw
        · exact False.elim (ho (congrArg Prod.fst hw).symm)
        · exact ih.mpr ⟨w,hw,hp⟩

/-- Rational historical support and the frozen aggregate support coincide
for ARBITRARY rows (including duplicate destinations and zero entries). -/
theorem historical_row_support_iff (rs : KState → Action → List (Ambient × Nat))
    (s t : KState) (act : Action) :
    (∃ w, (t,w) ∈ historyRows rs s act ∧ 0 < w) ↔ rowWeight (rs s act) t > 0 := by
  rw [row_weight_support_iff]
  constructor
  · rintro ⟨w,hw,hpos⟩
    obtain ⟨e,he,hfilter⟩ := List.mem_filterMap.mp hw
    rcases e with ⟨o,n⟩
    cases o with
    | inK u =>
      have eq : (u,(n : Rat)/4) = (t,w) := Option.some.inj hfilter
      have eu : u = t := congrArg Prod.fst eq
      subst u
      have ew : w = (n : Rat)/4 := (congrArg Prod.snd eq).symm
      subst w
      refine ⟨n,he,?_⟩
      by_cases hn : n > 0
      · exact hn
      · have hz : n = 0 := by omega
        subst n
        change (0 : Rat) < 0/4 at hpos
        rw [show (0 : Rat)/4 = 0 from by decide +kernel] at hpos
        exact False.elim ((show ¬ (0 : Rat) < 0 from by decide +kernel) hpos)
    | _ => cases hfilter
  · rintro ⟨n,hn,hpos⟩
    exact ⟨(n : Rat)/4,List.mem_filterMap.mpr ⟨(.inK t,n),hn,rfl⟩,
      ScaledRows.positive 4 n (by decide) hpos⟩


/-- Exact recorded-history adapter, not only a canonical support theorem.
The indexed generic policy agrees with the frozen per-factor policy here. -/
theorem recorded_support_iff (d : ExtraInputs) (history : List KState) :
    HistoricalAcquisition.RecordedSupport (historyRows d.base.rows)
      (fun _ => d.base.policy) history ↔ pathSupported d history = true := by
  have zipped (es : List (KState × KState)) :
      (∀ indexed ∈ es.zipIdx, rowWeight (d.base.rows indexed.1.1 (d.base.policy indexed.1.1)) indexed.1.2 > 0) ↔
      (∀ edge ∈ es, rowWeight (d.base.rows edge.1 (d.base.policy edge.1)) edge.2 > 0) := by
    constructor
    · intro h edge he
      have hm : edge ∈ es.zipIdx.map Prod.fst := by simpa only [List.zipIdx_map_fst] using he
      obtain ⟨indexed,hi,eq⟩ := List.mem_map.mp hm
      subst edge
      exact h indexed hi
    · intro h indexed hi
      apply h indexed.1
      have hm : indexed.1 ∈ es.zipIdx.map Prod.fst := List.mem_map.mpr ⟨indexed,hi,rfl⟩
      simpa only [List.zipIdx_map_fst] using hm
  simp only [HistoricalAcquisition.RecordedSupport,historical_row_support_iff]
  rw [zipped]
  simp [pathSupported,List.all_eq_true,Bool.and_eq_true]

/-- First-record lookup is frozen event6's PATH interpretation. Activation
instead scans ALL non-exit records, the frozen mixed7 interpretation. -/
def eventProjection (e : CSTTT.POS04.Event) : AcquisitionExecution.Event CSTTT.POS04.Stage :=
  ⟨e.fromStage,e.toStage,e.sourceSupport,e.targetSupport,
    e.strictStep && decide (stages.idxOf e.toStage = stages.idxOf e.fromStage + 1),e.atomic,
    stages.idxOf e.toStage - stages.idxOf e.fromStage⟩

/-- The path interpreter also checks frozen strictEvent6's UNIT event clock
law. Generic positive increments alone would accept a skipped POS-04 stage. -/
theorem path_event_rule_iff (d : RunInputs6) (e : CSTTT.POS04.Event) :
    (e.atomic = true ∧ (eventProjection e).strictStep = true ∧
      e.fromStage ∈ d.base.realized ∧ e.toStage ∈ d.base.realized ∧
      (eventProjection e).orderAdvance > 0 ∧
      stages.idxOf e.toStage = stages.idxOf e.fromStage + (eventProjection e).orderAdvance) ↔
    strictEvent6 d e = true := by
  simp only [eventProjection,strictEvent6,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨ha,⟨hs,hu⟩,hf,ht,_,_⟩
    exact ⟨⟨⟨⟨ha,hs⟩,hf⟩,ht⟩,hu⟩
  · rintro ⟨⟨⟨⟨ha,hs⟩,hf⟩,ht⟩,hu⟩
    exact ⟨ha,⟨hs,hu⟩,hf,ht,by omega,by omega⟩

def activationRecords (es : List CSTTT.POS04.Event) :=
  (es.filter (fun e => e.id != .exit)).map eventProjection


/-- Exact frozen activation semantics for arbitrary raw records, including
repeated IDs and records not named by the selected route. -/
theorem activation_iff_active7 (d : ExtraInputs) :
    HistoricalAcquisition.Activated (POS04ExecutionFrontier.receiverView.project d.receiver)
      (activationRecords d.events) d.realized ↔ active7 d = true := by
  have scanned : (∃ e ∈ activationRecords d.events,
      e.fromStage ∈ d.realized ∧ e.toStage ∈ d.realized ∧
      e.sourceSupport = true ∧ e.targetSupport = true ∧ e.atomic = true) ↔ mixed7 d = true := by
    constructor
    · rintro ⟨e,he,hfrom,hto,hs,ht,ha⟩
      obtain ⟨r,hr,eq⟩ := List.mem_map.mp he
      subst e
      obtain ⟨hr,eligible⟩ := List.mem_filter.mp hr
      apply List.any_eq_true.mpr
      refine ⟨r,hr,?_⟩
      change r.fromStage ∈ d.realized at hfrom
      change r.toStage ∈ d.realized at hto
      change r.sourceSupport = true at hs
      change r.targetSupport = true at ht
      change r.atomic = true at ha
      simp [eligible,hs,ht,ha,hfrom,hto]
    · intro hm
      obtain ⟨r,hr,hflags⟩ := List.any_eq_true.mp hm
      simp only [Bool.and_eq_true] at hflags
      obtain ⟨⟨⟨⟨⟨eligible,ha⟩,hs⟩,ht⟩,hfrom⟩,hto⟩ := hflags
      exact ⟨eventProjection r,List.mem_map.mpr
        ⟨r,List.mem_filter.mpr ⟨hr,eligible⟩,rfl⟩,
        of_decide_eq_true hfrom,of_decide_eq_true hto,hs,ht,ha⟩
  cases hm : d.receiver.mixedEventRequired <;>
    simp [HistoricalAcquisition.Activated,POS04ExecutionFrontier.receiverView,
      active7,hm,scanned,Bool.and_eq_true,and_assoc]

def raw : HistoricalAcquisition.Raw Cell Value Register RegisterValue
    LaneDisturbance Action Ambient KState KState CSTTT.POS04.Stage EventId RouteId RouteId where
  histories := ⟨POS04ExecutionFrontier.pathExpr⟩
  sourceRows := ⟨.map historyRows (.cell (Cell.rows .source))⟩
  targetCoordinate := ⟨.literal id⟩
  targetRows := ⟨.map historyRows (.cell (Cell.rows .target))⟩
  sourcePolicy := ⟨.map (fun p => fun (_ : RouteId) (_ : Nat) => p) (.cell Cell.policy)⟩
  targetPolicy := ⟨.map (fun p => fun (_ : RouteId) (_ : Nat) => p) (.cell Cell.policy)⟩
  routes := POS04ExecutionFrontier.routeView
  events := ⟨.eventTable,fun es id => (es.find? (fun e => e.id == id)).map eventProjection⟩
  activationEvents := ⟨.map activationRecords (.cell Cell.eventTable)⟩
  realized := ⟨.realized,id⟩
  receiver := POS04ExecutionFrontier.receiverView
  reset := fun k => match k with
    | .factor => .environment (fun input => Ambient.inK input.1)
    | .counter | .ticks => .literal (0 : Nat)
    | .residue => .environment (fun input => (input.2.1,input.2.2.1))
    | .funded => .map Receiver.funded (.cell Cell.receiverInput)
  response := POS04ExecutionFrontier.acquisition.arrivalResponse
  execution := ⟨[.nominal],actions,ambientStates,POS04RegisterFuture.enabledRow .target,program .target⟩

/-- Computed dependency union, including every register's reset and update.
This is not a copied twelve-cell list. Writer/withdrawal checks belong to the
resource/game binding; this acquisition component does not certify them alone. -/
def scope : List Cell := raw.dependencies ++
  ([Register.factor,.counter,.ticks,.residue,.funded].flatMap fun r => (raw.reset r).dependencies) ++
  raw.execution.row.dependencies ++
  ([Register.factor,.counter,.ticks,.residue,.funded].flatMap fun r => (raw.execution.program r).dependencies)

theorem no_source_ticks : Cell.ticks .source ∉ scope := by decide
theorem no_source_resources : Cell.resources .source ∉ scope := by decide
theorem no_hazards : Cell.hazards ∉ scope := by decide

theorem ready (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete scope a) :
    HistoricalAcquisition.Ready raw a := by
  refine ⟨fun k hk => hc k (by simp [scope,hk]),?_,?_,?_⟩
  · intro r k hk
    apply hc k
    cases r <;> simp_all [scope,raw,Expr.dependencies]
  · intro k hk; exact hc k (by simp [scope,hk])
  · intro r k hk
    apply hc k
    cases r <;> simp_all [scope,raw,program,Expr.dependencies]

theorem canonical_ready : HistoricalAcquisition.Ready raw canonical :=
  ready _ (fun _ _ => rfl)

/-- All partial-assignment acquisition dependencies are exact syntactic reads.
Deleting ANY consumed cell rejects before canonical decoder helpers exist. -/
theorem missing_scope_rejected (a : CSTTT.POS04.Assigned.Assignment)
    (k : Cell) (hk : k ∈ scope) (hm : a k = none) : ¬ HistoricalAcquisition.Ready raw a := by
  intro h
  simp only [scope,List.mem_append] at hk
  rcases hk with ((hk | hk) | hk) | hk
  · exact HistoricalAcquisition.missing_dependency_rejected raw a k hk hm h
  · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hk
    exact HistoricalAcquisition.missing_reset_rejected raw a r k hr hm h
  · exact HistoricalAcquisition.missing_target_row_rejected raw a k hk hm h
  · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hk
    exact HistoricalAcquisition.missing_target_update_rejected raw a r k hr hm h

theorem reset_computed (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready raw a)
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId)
    (receiver : Receiver) (hr : a .receiverInput = some receiver) :
    HistoricalAcquisition.reset raw a h input =
      encode ⟨.inK input.1,0,0,(input.2.1,input.2.2.1),receiver.funded⟩ := by
  funext reg
  have he := RegisterInitialization.initial_eq raw.reset a h.2.1 input reg
  apply Option.some.inj
  cases reg <;> simpa [HistoricalAcquisition.reset,raw,RegisterInitialization.evaluate,Expr.eval,encode,hr] using he.symm

/-- Exact actual updater agreement for ALL assigned data/ambient branches,
not just a canonical terminal or a selected predictive representative. -/
theorem updater_computed (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready raw a) (x : Run6)
    (d : LaneDisturbance) (act : Action) (o : Ambient) :
    HistoricalAcquisition.update raw a h (encode x) d act o =
      encode (actualUpdate6 (runInputs6 a .target) x act o) := by
  have hc : Complete (coreDependencies .target) a := by
    intro k hk
    simp [coreDependencies] at hk
    rcases hk with hk | hk | hk <;> subst k
    · exact h.2.2.1 _ (by simp [raw,POS04RegisterFuture.enabledRow,rowExpression,Expr.dependencies])
    · exact h.2.2.2 .ticks _ (by simp [raw,program,Expr.dependencies])
    · exact h.2.2.2 .funded _ (by simp [raw,program,Expr.dependencies])
  exact checked_actual a .target hc x d act o

/-- A real instantiated reception on the frozen different-past source
histories. This theorem claims acquisition only; complete lineage remains the
separate funded-execution predicate. -/
theorem canonical_arrival (rid : RouteId) :
    HistoricalAcquisition.Arrival POS04ExecutionFrontier.schema raw canonical canonical_ready rid
      (encode (POS04RouteExecution.arrivalFor rid)) := by
  let hs := POS04ExecutionFrontier.historyPath sourceHistory routes
  let rs : RouteId → AcquisitionExecution.Route RouteId EventId :=
    fun r => ⟨r,(routeOf r).eventPath⟩
  let ev : EventId → Option (AcquisitionExecution.Event CSTTT.POS04.Stage) :=
    fun id => some ((POS04ExecutionFrontier.eventView).project events id)
  let e := POS04ExecutionFrontier.eventView.project events
  have edge (s t : KState)
      (h : (s,t) ∈ [(KState.p1w0,.p2w1),(.p2w1,.p1w0),(.p1w1,.p5w0),(.p5w0,.p1w0)]) :
      ∃ weight, (t,weight) ∈ historyRows (actionRow .source) s (canonicalAction s) ∧ 0 < weight := by
    refine ⟨(rowWeight (actionRow .source s (canonicalAction s)) t : Rat)/4,?_,?_⟩
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    all_goals rcases h with h | h | h | h
    all_goals cases h
    all_goals decide +kernel
  have triple (s t u : KState)
      (h1 : (s,t) ∈ [(KState.p1w0,.p2w1),(.p2w1,.p1w0),(.p1w1,.p5w0),(.p5w0,.p1w0)])
      (h2 : (t,u) ∈ [(KState.p1w0,.p2w1),(.p2w1,.p1w0),(.p1w1,.p5w0),(.p5w0,.p1w0)]) :
      HistoricalAcquisition.RecordedSupport (historyRows (actionRow .source))
        (fun _ => canonicalAction) [s,t,u] := by
    refine ⟨by simp,?_⟩
    intro indexed hi
    change indexed ∈ [((s,t),0),((t,u),1)] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with hi | hi <;> subst indexed
    · exact edge s t h1
    · exact edge t u h2
  have support (r : RouteId) : HistoricalAcquisition.RecordedSupport
      (historyRows (actionRow .source)) (fun _ => canonicalAction) (hs r) := by
    cases r
    · exact triple .p1w0 .p2w1 .p1w0 (by decide) (by decide)
    · exact triple .p1w1 .p5w0 .p1w0 (by decide) (by decide)
  have path (r : RouteId) : HistoricalAcquisition.PathCheck POS04ExecutionFrontier.schema ev realizedStages (rs r).path := by
    refine ⟨.mix1,[.mix2,.exit],by cases r <;> rfl,⟨e .mix1,rfl,rfl⟩,?_,?_,.exit,e .exit,
      by cases r <;> rfl,rfl,rfl,rfl,rfl⟩
    · intro id hid
      refine ⟨?_,e id,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
      all_goals cases id <;> decide +kernel
    · intro pair hp
      rcases pair with ⟨i,j⟩
      refine ⟨e i,e j,rfl,rfl,?_⟩
      cases r <;> cases i <;> cases j <;>
        simp_all [rs,routeOf,routes,e,POS04ExecutionFrontier.eventView,events,stages]
  refine ⟨hs,historyRows (actionRow .source),(fun _ _ => canonicalAction),id,
    historyRows (actionRow .target),(fun _ _ => canonicalAction),rs,ev,realizedStages,
    POS04ExecutionFrontier.receiverView.project receiver,
    (hs rid).headD .p0w0,(hs rid).drop 1,
    rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,rfl,rfl,?_,?_,?_,?_,?_,path rid,?_,?_⟩
  · change some (POS04ExecutionFrontier.routeView.project routes) = some rs
    apply congrArg some
    funext r; cases r <;> rfl
  · change some _ = some ev
    apply congrArg some
    funext id; cases id <;> rfl
  · cases rid <;> decide
  · cases rid <;> decide
  · cases rid <;> rfl
  · cases rid
    · exact support .a
    · exact support .b
  · cases rid
    · simpa using support .a
    · simpa using support .b
  · exact ⟨activationRecords events,rfl,rfl,rfl,rfl,fun _ => ⟨e .mix1,List.mem_map.mpr ⟨eventOf .mix1,List.mem_filter.mpr ⟨by decide,rfl⟩,rfl⟩,
      by decide,by decide,rfl,rfl,rfl⟩⟩
  · rw [HistoricalAcquisition.recorded_word_terminal (default := .p0w0)]
    rw [reset_computed (receiver := receiver) (hr := rfl)]
    cases rid <;> rfl

theorem ready_iff (a : CSTTT.POS04.Assigned.Assignment) :
    HistoricalAcquisition.Ready raw a ↔ Complete scope a := by
  constructor
  · intro h k hk
    simp only [scope,List.mem_append] at hk
    rcases hk with ((hk | hk) | hk) | hk
    · exact h.1 k hk
    · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hk
      exact h.2.1 r k hr
    · exact h.2.2.1 k hk
    · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hk
      exact h.2.2.2 r k hr
  · exact ready a

/-- Runtime table equivalence for ARBITRARY partial assignments on exactly
this interpreter's consumed scope. No temporal/hazard completeness is added. -/
theorem actual_row (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready raw a) (x : Run6) (d : LaneDisturbance) (act : Action) :
    HistoricalAcquisition.rows raw a (encode x) d act = actualRows6 (runInputs6 a .target) x act := by
  have hc := (ready_iff a).mp h
  have hres := cell_value (hc (Cell.resources .target) (by decide))
  have hl := cell_value (hc Cell.maintenance (by decide))
  have hrow := row_eval a .target (hc (Cell.rows .target) (by decide)) x d act
  have he : raw.execution.row.eval a (encode x) (d,act) =
      some (actualRows6 (runInputs6 a .target) x act) := by
    simp only [raw,POS04RegisterFuture.enabledRow,Expr.eval,encode]
    rw [hres,hl,hrow]
    rfl
  simp only [HistoricalAcquisition.rows,he,Option.getD_some]

/-- Positive actual phase-2 entry. Its outcome is the frozen row branch,
not a class representative chosen to preserve safety. -/
theorem canonical_entry (rid : RouteId) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw canonical canonical_ready
      (encode (POS04RouteExecution.resultFor rid)) := by
  have domain : HistoricalAcquisition.DomainCheck POS04ExecutionFrontier.schema raw := by
    refine ⟨by decide,by decide,?_,?_,by decide,?_⟩
    · intro r; cases r <;> decide
    · intro r; cases r <;> decide
    · intro d; cases d; decide
  have rr : raw.routes.read canonical = some (fun r => ⟨r,[.mix1,.mix2,.exit]⟩) := by
    change some (POS04ExecutionFrontier.routeView.project routes) = _
    apply congrArg some
    funext r; cases r <;> rfl
  have rsp : raw.response.eval canonical (encode (POS04RouteExecution.arrivalFor rid)) (rid,rid) =
      some (LaneDisturbance.nominal,Action.cw) := by cases rid <;> rfl
  have norm : StrategyGame.Normalized (HistoricalAcquisition.rows raw canonical)
      (encode (POS04RouteExecution.arrivalFor rid)) .nominal .cw := by
    simp only [StrategyGame.Normalized,StrategyGame.PositiveSupport,
      actual_row canonical canonical_ready]
    refine ⟨?_,?_,Ambient.inK .p2w1,1,?_,by decide⟩
    all_goals cases rid <;> decide +kernel
  have pos : StrategyGame.PositiveSupport (HistoricalAcquisition.rows raw canonical)
      (encode (POS04RouteExecution.arrivalFor rid)) .nominal .cw (.inK .p2w1) := by
    refine ⟨1,?_,by decide⟩
    rw [actual_row canonical canonical_ready]
    cases rid <;> decide +kernel
  have he := HistoricalAcquisition.every_supported_branch_is_entry POS04ExecutionFrontier.schema
    raw canonical canonical_ready domain rid _ (canonical_arrival rid)
    (fun r => ⟨r,[.mix1,.mix2,.exit]⟩) rr (.nominal,.cw) rsp (by decide) (by decide) norm _ pos
  rw [updater_computed] at he
  exact he

theorem entries_nonempty : ∃ r, HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw canonical canonical_ready r :=
  ⟨_,canonical_entry .a⟩

/-- Genuine missing-input negative: no ready entry exists. -/
theorem missing_consumed_no_entries (a : CSTTT.POS04.Assigned.Assignment)
    (k : Cell) (hk : k ∈ scope) :
    ¬ ∃ h : HistoricalAcquisition.Ready raw (Assigned.put a k none),
      ∃ r, HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw (Assigned.put a k none) h r := by
  rintro ⟨h,_⟩
  exact missing_scope_rejected _ k hk (Assigned.put_same _ _ _) h

/-- Per-field availability guard for actual activation, not merely a
successful decoder or a sibling corridor result. -/
theorem absent_source_no_entries :
    ¬ ∃ h : HistoricalAcquisition.Ready raw
        (Assigned.put canonical .receiverInput (some {receiver with sourcePresent := false})),
      ∃ r, HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw
        (Assigned.put canonical .receiverInput (some {receiver with sourcePresent := false})) h r := by
  rintro ⟨h,r,he⟩
  exact HistoricalAcquisition.source_absent_no_entry _ _ _ h
    (POS04ExecutionFrontier.receiverView.project {receiver with sourcePresent := false}) rfl rfl r he

/-- Partial-assignment invariance follows from the actual recipe dependencies.
This includes every target update and the entry relation, not only reception. -/
theorem entries_locality {a b : CSTTT.POS04.Assigned.Assignment}
    (ha : HistoricalAcquisition.Ready raw a) (hb : HistoricalAcquisition.Ready raw b)
    (he : Agrees scope a b) (r : Registers Register RegisterValue) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw a ha r ↔
      HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw b hb r := by
  apply HistoricalAcquisition.locality raw POS04ExecutionFrontier.schema ha hb
  · intro k hk; exact he k (by simp [scope,hk])
  · intro reg k hk
    exact he k (by
      unfold scope
      apply List.mem_append_left
      apply List.mem_append_left
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨reg,by cases reg <;> simp,hk⟩)
  · intro k hk; exact he k (by simp [scope,hk])
  · intro reg k hk
    exact he k (List.mem_append_right _ (List.mem_flatMap.mpr ⟨reg,by cases reg <;> simp,hk⟩))


/-- Dependency projection is proved for every partial assignment, not
inferred from the canonical arrival. Every unconsumed cell may be replaced. -/
theorem replacement_ready (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready raw a) (k : Cell) (hk : k ∉ scope) (v : Option (Value k)) :
    HistoricalAcquisition.Ready raw (Assigned.put a k v) := by
  apply ready
  intro j hj
  rw [Assigned.put_other a k j v (fun eq => hk (eq ▸ hj))]
  exact (ready_iff a).mp h j hj

theorem unconsumed_replacement_entries (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready raw a) (k : Cell) (hk : k ∉ scope) (v : Option (Value k))
    (r : Registers Register RegisterValue) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw a h r ↔
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw (Assigned.put a k v)
      (replacement_ready a h k hk v) r := by
  apply entries_locality
  intro j hj
  exact (Assigned.put_other a k j v (fun eq => hk (eq ▸ hj))).symm

/-- Missing past ticks do not prevent this historical-support reception or
any actual target branch. The separate funded-lineage interpreter reads them. -/
theorem missing_past_ticks_entry (rid : RouteId) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw
      (Assigned.put canonical (.ticks .source) none)
      (replacement_ready canonical canonical_ready _ no_source_ticks none)
      (encode (POS04RouteExecution.resultFor rid)) :=
  (unconsumed_replacement_entries canonical canonical_ready _ no_source_ticks none _).mp
    (canonical_entry rid)

/-- Disabling source recharge leaves historical acquisition unchanged.
This does not assert a funded source trajectory or complete lineage. -/
theorem unavailable_source_recharge_entry (rid : RouteId) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw
      (Assigned.put canonical (.resources .source) (some ⟨.source,false⟩))
      (replacement_ready canonical canonical_ready _ no_source_resources (some ⟨.source,false⟩))
      (encode (POS04RouteExecution.resultFor rid)) :=
  (unconsumed_replacement_entries canonical canonical_ready _ no_source_resources _ _).mp
    (canonical_entry rid)

/-- Arbitrary partial data: every ACTUAL positive target branch is retained
with its actual updater. Neither historical pullback nor a class quotient
filters the phase-2 support. -/
theorem actual_supported_branch_entry (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready raw a) (rid : RouteId) (received : Run6)
    (ha : HistoricalAcquisition.Arrival POS04ExecutionFrontier.schema raw a h rid (encode received))
    (rs : RouteId → AcquisitionExecution.Route RouteId EventId)
    (hr : raw.routes.read a = some rs) (da : LaneDisturbance × Action)
    (hrsp : raw.response.eval a (encode received) ((rs rid).history,rid) = some da)
    (hn : StrategyGame.Normalized (fun x d act => HistoricalAcquisition.rows raw a x d act)
      (encode received) da.1 da.2)
    (o : Ambient) (hp : StrategyGame.PositiveSupport
      (fun x (_ : LaneDisturbance) act => actualRows6 (runInputs6 a .target) x act)
      received da.1 da.2 o) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw a h
      (encode (actualUpdate6 (runInputs6 a .target) received da.2 o)) := by
  have hd : HistoricalAcquisition.DomainCheck POS04ExecutionFrontier.schema raw := by
    refine ⟨by decide,by decide,?_,?_,by decide,?_⟩
    · intro r; cases r <;> decide
    · intro r; cases r <;> decide
    · intro d; cases d; decide
  have hp' : StrategyGame.PositiveSupport (HistoricalAcquisition.rows raw a)
      (encode received) da.1 da.2 o := by
    simpa only [StrategyGame.PositiveSupport,actual_row a h] using hp
  have he := HistoricalAcquisition.every_supported_branch_is_entry _ raw a h hd rid _ ha rs hr da hrsp
    (by cases da.1; decide) (by cases da.2 <;> decide) hn o hp'
  rw [updater_computed] at he
  exact he

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalAcquisition
