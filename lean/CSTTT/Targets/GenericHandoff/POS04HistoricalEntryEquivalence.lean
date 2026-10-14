import CSTTT.Targets.GenericHandoff.POS04HistoricalRuntimeInstance

/-! Arbitrary-partial acquisition adapters for the nominal historical F/O
runtime. All views read the shared staged assignment; the extracted protocol
is evidence on raw data, not an entry or autonomy verdict. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalEntryEquivalence
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter RegisterInitialization
open POS04RouteExecution POS04ResourceRuntime
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

abbrev model (m : RawLaneModel) := POS04HistoricalRuntime.model (protocol m)
abbrev raw (m : RawLaneModel) := HistoricalPackageRuntime.acquisition (model m)
abbrev data (m : RawLaneModel) := arrivalInputs m
abbrev ready (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :=
  POS04HistoricalRuntime.acquisition_ready_of_protocol m hp

theorem histories_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (raw m).histories.read (image m.assignment) =
      some (POS04ExecutionFrontier.historyPath (data m).base.histories (data m).base.routes) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hh := POS04RegisterDynamics.cell_value (hc .histories (by decide))
  have hr := POS04RegisterDynamics.cell_value (hc .routeTable (by decide))
  change POS04ExecutionFrontier.pathExpr.eval (image m.assignment) noRegisters () = _
  simp only [POS04ExecutionFrontier.pathExpr,Expr.eval]
  rw [hh,hr]
  rfl

theorem routes_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (raw m).routes.read (image m.assignment) =
      some (POS04ExecutionFrontier.routeView.project (data m).base.routes) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc .routeTable (by decide))
  change (image m.assignment .routeTable).map _ = _
  rw [hr]
  rfl

theorem source_rows_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (raw m).sourceRows.read (image m.assignment) =
      some (POS04HistoricalAcquisition.historyRows (clauseExtra (image m.assignment) .source .c6).base.rows) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc (.rows .source) (by decide))
  change (image m.assignment (.rows .source)).map _ = _
  rw [hr]
  rfl

theorem target_rows_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (raw m).targetRows.read (image m.assignment) =
      some (POS04HistoricalAcquisition.historyRows (data m).base.base.rows) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc (.rows .target) (by decide))
  change (image m.assignment (.rows .target)).map _ = _
  rw [hr]
  rfl

theorem policy_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (raw m).sourcePolicy.read (image m.assignment) = some (fun (_ : RouteId) (_ : Nat) => (data m).base.base.policy) ∧
    (raw m).targetPolicy.read (image m.assignment) = some (fun (_ : RouteId) (_ : Nat) => (data m).base.base.policy) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc .policy (by decide))
  constructor
  all_goals change (image m.assignment .policy).map _ = _; rw [hr]; rfl

theorem events_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (raw m).events.read (image m.assignment) =
      some (fun id => (event6 (data m) id).map POS04HistoricalAcquisition.eventProjection) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc .eventTable (by decide))
  change (image m.assignment .eventTable).map _ = _
  rw [hr]
  rfl

theorem realized_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (raw m).realized.read (image m.assignment) = some (data m).base.realized := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc .realized (by decide))
  change (image m.assignment .realized).map id = _
  rw [hr]
  rfl

theorem receiver_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (raw m).receiver.read (image m.assignment) =
      some (POS04ExecutionFrontier.receiverView.project (data m).base.receiver) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc .receiverInput (by decide))
  change (image m.assignment .receiverInput).map _ = _
  rw [hr]
  rfl

theorem activation_read (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    (raw m).activationEvents.read (image m.assignment) =
      some (POS04HistoricalAcquisition.activationRecords (data m).base.events) := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hr := POS04RegisterDynamics.cell_value (hc .eventTable (by decide))
  change (image m.assignment .eventTable).map _ = _
  rw [hr]
  rfl

theorem tuple_views (m : RawLaneModel) (rid : RouteId) (history : List KState) (path : List EventId)
    (ht : routeTuple (data m).base rid = some (history,path)) :
    POS04ExecutionFrontier.historyPath (data m).base.histories (data m).base.routes rid = history ∧
    (POS04ExecutionFrontier.routeView.project (data m).base.routes rid).path = path := by
  unfold routeTuple at ht
  cases hf : (data m).base.routes.find? (fun r => r.id == rid) with
  | none => simp [hf] at ht
  | some r =>
    rw [hf] at ht
    have he := Option.some.inj ht
    exact ⟨by simpa [POS04ExecutionFrontier.historyPath,hf] using congrArg Prod.fst he,
      by simpa [POS04ExecutionFrontier.routeView,hf] using congrArg Prod.snd he⟩

theorem phase2_boundary (m : RawLaneModel) (rid : RouteId) (history : List KState) (path : List EventId)
    (hp : phase2Check m rid = true) (ht : routeTuple (data m).base rid = some (history,path)) :
    ∃ first last start finish, path.head? = some first ∧ path.getLast? = some last ∧
      event6 (data m) first = some start ∧ event6 (data m) last = some finish ∧
      start.fromStage = .sourceLive ∧ finish.toStage = .targetExit ∧
      finish.targetSupport = true ∧ finish.sourceSupport = false := by
  unfold phase2Check at hp
  split at hp
  · simp at hp
  · simp only [ht] at hp
    cases hf : path.head? with
    | none => simp [hf] at hp
    | some first =>
      cases hl : path.getLast? with
      | none => simp [hf,hl] at hp
      | some last =>
        cases hs : event6 (data m) first with
        | none => simp [hf,hl,hs] at hp
        | some start =>
          cases he : event6 (data m) last with
          | none => simp [hf,hl,hs,he] at hp
          | some finish =>
            simp only [hf,hl,hs,he,Bool.and_eq_true] at hp
            refine ⟨first,last,start,finish,rfl,rfl,hs,he,?_,?_,?_,?_⟩
            all_goals grind

/-- The strict realized raw path follows from the same route check used by
frozen acquisition. The unit clock equation is checked, not assumed. -/
theorem phase2_raw_path (m : RawLaneModel) (rid : RouteId) (history : List KState) (path : List EventId)
    (hp : phase2Check m rid = true) (ht : routeTuple (data m).base rid = some (history,path)) :
    HistoricalAcquisition.PathCheck POS04ExecutionFrontier.schema
      (fun id => (event6 (data m) id).map POS04HistoricalAcquisition.eventProjection)
      (data m).base.realized path := by
  obtain ⟨_,_,_,hpath,_⟩ := POS04HistoricalAutonomy.phase2_facts m rid history path hp ht
  simp only [path6,ht,Bool.and_eq_true] at hpath
  obtain ⟨⟨⟨⟨_,_⟩,_⟩,hsteps⟩,hadj⟩ := hpath
  obtain ⟨first,last,start,finish,hfirst,hlast,hstart,hfinish,hfrom,hto,hft,hfs⟩ :=
    phase2_boundary m rid history path hp ht
  obtain ⟨rest,hr⟩ := List.head?_eq_some_iff.mp hfirst
  refine ⟨first,rest,hr,⟨POS04HistoricalAcquisition.eventProjection start,?_,hfrom⟩,?_,?_,
    last,POS04HistoricalAcquisition.eventProjection finish,hlast,?_,hto,hft,hfs⟩
  · simp only [hstart,Option.map_some]
  · intro id hm
    have hs := List.all_eq_true.mp hsteps id hm
    cases he : event6 (data m) id with
    | none => simp [he] at hs
    | some e =>
      have hstrict : strictEvent6 (data m) e = true := by simpa [he] using hs
      obtain ⟨ha,hs,hf,ht,hadvance,hclock⟩ :=
        (POS04HistoricalAcquisition.path_event_rule_iff (data m) e).mpr hstrict
      refine ⟨(by cases id <;> decide),POS04HistoricalAcquisition.eventProjection e,
        (by simp only [he,Option.map_some]),hf,ht,?_,?_,ha,hs,hadvance,hclock⟩
      · change e.fromStage ∈ stages; cases e.fromStage <;> decide
      · change e.toStage ∈ stages; cases e.toStage <;> decide
  · intro pair hm
    have hs := List.all_eq_true.mp hadj pair hm
    cases he : event6 (data m) pair.1 with
    | none => simp [he] at hs
    | some e =>
      cases hf : event6 (data m) pair.2 with
      | none => simp [he,hf] at hs
      | some f =>
        refine ⟨POS04HistoricalAcquisition.eventProjection e,POS04HistoricalAcquisition.eventProjection f,
          (by simp only [he,Option.map_some]),(by simp only [hf,Option.map_some]),?_⟩
        exact of_decide_eq_true (by simpa [he,hf] using hs)
  · simp only [hfinish,Option.map_some]

def rawReady (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    HistoricalAcquisition.Ready (raw m) (image m.assignment) := by
  simpa only [HistoricalPackageRuntime.AcquisitionReady,POS04HistoricalRuntime.target_eq] using ready m hp

def registerReady (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    HistoricalAcquisition.Ready POS04HistoricalAcquisition.raw (image m.assignment) := by
  apply POS04HistoricalAcquisition.ready
  intro k hk
  exact POS04OperationalGame.protocol_complete m hp k
    (List.mem_append_right _ ((by decide : POS04HistoricalAcquisition.scope ⊆ phase2Dependencies) hk))

theorem protocol_route_tuple (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (rid : RouteId) :
    ∃ history path, routeTuple (data m).base rid = some (history,path) := by
  have hphase := List.all_eq_true.mp hp.2.2.2.2 rid (by cases rid <;> decide)
  cases ht : routeTuple (data m).base rid with
  | some residue => exact ⟨residue.1,residue.2,rfl⟩
  | none =>
    unfold phase2Check at hphase
    split at hphase
    · simp at hphase
    · simp [ht] at hphase

def received (m : RawLaneModel) (history : List KState) (path : List EventId) : Run6 :=
  ⟨.inK (history.getLastD .p0w0),0,0,(history,path),(data m).base.receiver.funded⟩

/-- Actual terminal coordinates and provenance, never a stored class or
baseline endpoint. This construction works for any nominal-protocol assignment. -/
theorem protocol_arrival (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (rid : RouteId) (history : List KState) (path : List EventId)
    (ht : routeTuple (data m).base rid = some (history,path)) :
    HistoricalAcquisition.Arrival POS04ExecutionFrontier.schema (raw m) (image m.assignment)
      (rawReady m hp) rid (frame .target (received m history path)) := by
  have hphase := List.all_eq_true.mp hp.2.2.2.2 rid (by cases rid <;> decide)
  obtain ⟨_,hne,hactive,hpath,hsource⟩ := POS04HistoricalAutonomy.phase2_facts m rid history path hphase ht
  have htarget : pathSupported (data m).base history = true := by
    simp only [path6,ht,Bool.and_eq_true] at hpath
    exact hpath.1.1.1.2
  obtain ⟨first,rest,hlist⟩ := List.exists_cons_of_ne_nil hne
  let hs := POS04ExecutionFrontier.historyPath (data m).base.histories (data m).base.routes
  let rs := POS04ExecutionFrontier.routeView.project (data m).base.routes
  let pol : RouteId → Nat → KState → Action := fun _ _ => (data m).base.base.policy
  refine ⟨hs,POS04HistoricalAcquisition.historyRows (clauseExtra (image m.assignment) .source .c6).base.rows,
    pol,id,POS04HistoricalAcquisition.historyRows (data m).base.base.rows,pol,rs,
    (fun id => (event6 (data m) id).map POS04HistoricalAcquisition.eventProjection),
    (data m).base.realized,POS04ExecutionFrontier.receiverView.project (data m).base.receiver,
    first,rest,histories_read m hp,source_rows_read m hp,(policy_read m hp).1,rfl,
    target_rows_read m hp,(policy_read m hp).2,routes_read m hp,events_read m hp,
    realized_read m hp,receiver_read m hp,(by cases rid <;> decide),(by change rid ∈ routeIds; cases rid <;> decide),?_,?_,?_,?_,?_,?_⟩
  · change hs rid = first::rest
    exact (tuple_views m rid history path ht).1.trans hlist
  · simpa only [hlist] using
      (POS04HistoricalAcquisition.recorded_support_iff (clauseExtra (image m.assignment) .source .c6) history).mpr hsource
  · simpa only [List.map_id_fun,hlist] using
      (POS04HistoricalAcquisition.recorded_support_iff (data m).base history).mpr htarget
  · change HistoricalAcquisition.PathCheck _ _ _ (rs rid).path
    rw [(tuple_views m rid history path ht).2]
    exact phase2_raw_path m rid history path hphase ht
  · exact ⟨POS04HistoricalAcquisition.activationRecords (data m).base.events,activation_read m hp,
      (POS04HistoricalAcquisition.activation_iff_active7 (data m).base).mpr hactive⟩
  · rw [POS04HistoricalRuntime.reset_link _ _ (rawReady m hp) (registerReady m hp),
      POS04HistoricalAcquisition.reset_computed (image m.assignment) (registerReady m hp) _ (data m).base.receiver
        (POS04RegisterDynamics.cell_value (POS04OperationalGame.protocol_complete m hp .receiverInput (by decide))),
      POS04RegisterDynamics.decode_encode,HistoricalAcquisition.recorded_word_terminal _ _ _ .p0w0,
      (tuple_views m rid history path ht).2,← hlist]
    rfl

theorem arrival_unique (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (rid : RouteId) (history : List KState) (path : List EventId)
    (ht : routeTuple (data m).base rid = some (history,path)) (arrived : Registers Unit FrameValue)
    (ha : HistoricalAcquisition.Arrival POS04ExecutionFrontier.schema (raw m) (image m.assignment)
      (rawReady m hp) rid arrived) : arrived = frame .target (received m history path) := by
  rcases ha with ⟨hs,sr,sp,coord,tr,tp,rs,ev,real,rec,first,rest,
    hh,hr,hsp,hcoord,htr,htp,hrs,hev,hreal,hrec,hrid,hhid,hlist,hss,hts,hpath,hact,hreset⟩
  have hehs := Option.some.inj (hh.symm.trans (histories_read m hp))
  have hers := Option.some.inj (hrs.symm.trans (routes_read m hp))
  have hep := Option.some.inj (hsp.symm.trans (policy_read m hp).1)
  subst hs; subst rs; subst sp
  change POS04ExecutionFrontier.historyPath (data m).base.histories (data m).base.routes rid = first::rest at hlist
  have hehist : history = first::rest := (tuple_views m rid history path ht).1.symm.trans hlist
  rw [hreset,POS04HistoricalRuntime.reset_link _ _ (rawReady m hp) (registerReady m hp),
    POS04HistoricalAcquisition.reset_computed (image m.assignment) (registerReady m hp) _ (data m).base.receiver
      (POS04RegisterDynamics.cell_value (POS04OperationalGame.protocol_complete m hp .receiverInput (by decide))),
    POS04RegisterDynamics.decode_encode,HistoricalAcquisition.recorded_word_terminal _ _ _ .p0w0,
    (tuple_views m rid history path ht).2,← hehist]
  rfl

theorem response_computed (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (rid : RouteId) (history : List KState) (path : List EventId) :
    (raw m).response.eval (image m.assignment) (frame .target (received m history path))
      (rid,rid) = some (.nominal,(data m).base.base.policy (history.getLastD .p0w0)) := by
  change (lift POS04ExecutionFrontier.acquisition.arrivalResponse).eval _ _ _ = _
  rw [POS04RouteExecution.lift,frame,RunFrame.evaluation]
  simp only [POS04ExecutionFrontier.acquisition,Expr.eval,received]
  rw [POS04RegisterDynamics.cell_value (POS04OperationalGame.protocol_complete m hp .policy (by decide))]
  rfl

theorem response_rows (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (rid : RouteId) (history : List KState) (path : List EventId)
    (ht : routeTuple (data m).base rid = some (history,path)) :
    HistoricalAcquisition.rows (raw m) (image m.assignment)
      (frame .target (received m history path)) .nominal
      ((data m).base.base.policy (history.getLastD .p0w0)) =
      ((data m).base.base.rows (history.getLastD .p0w0)
        ((data m).base.base.policy (history.getLastD .p0w0))).map (fun e => (e.1,(e.2 : Rat)/4)) := by
  rw [POS04HistoricalRuntime.rows_eq _ _ (rawReady m hp)]
  exact POS04HistoricalAutonomy.target_response_row m rid history path
    (List.all_eq_true.mp hp.2.2.2.2 rid (by cases rid <;> decide)) ht

theorem response_normalized (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (rid : RouteId) (history : List KState) (path : List EventId)
    (ht : routeTuple (data m).base rid = some (history,path)) :
    StrategyGame.Normalized (HistoricalAcquisition.rows (raw m) (image m.assignment))
      (frame .target (received m history path)) .nominal
      ((data m).base.base.policy (history.getLastD .p0w0)) := by
  have hphase := List.all_eq_true.mp hp.2.2.2.2 rid (by cases rid <;> decide)
  have hn := POS04HistoricalProtocol.response_normalized m rid history path hphase ht
  unfold StrategyGame.Normalized StrategyGame.PositiveSupport at hn ⊢
  rw [response_rows m hp rid history path ht]
  simpa only [POS04HistoricalProtocol.response_rows m rid history path hphase ht] using hn

/-- Every actual support element is retained, including exits. -/
theorem branch_entry (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (rid : RouteId) (history : List KState) (path : List EventId)
    (ht : routeTuple (data m).base rid = some (history,path)) (branch : Ambient × Nat)
    (hb : branch ∈ (data m).base.base.rows (history.getLastD .p0w0)
      ((data m).base.base.policy (history.getLastD .p0w0))) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema (raw m) (image m.assignment) (rawReady m hp)
      (frame .target (actualUpdate6 (data m) (received m history path)
        ((data m).base.base.policy (history.getLastD .p0w0)) branch.1)) := by
  have hphase := List.all_eq_true.mp hp.2.2.2.2 rid (by cases rid <;> decide)
  have domain : HistoricalAcquisition.DomainCheck POS04ExecutionFrontier.schema (raw m) := by
    refine ⟨by decide,by decide,?_,?_,(by change ([LaneDisturbance.nominal] : List _) ≠ []; decide),?_⟩
    · intro r; cases r <;> decide
    · intro r; cases r <;> decide
    · intro d; cases d; change LaneDisturbance.nominal ∈ [LaneDisturbance.nominal]; decide
  have hs : StrategyGame.PositiveSupport (HistoricalAcquisition.rows (raw m) (image m.assignment))
      (frame .target (received m history path)) .nominal
      ((data m).base.base.policy (history.getLastD .p0w0)) branch.1 := by
    refine ⟨(branch.2 : Rat)/4,?_,ScaledRows.positive 4 branch.2 (by decide)
      ((POS04HistoricalAutonomy.phase2_target_facts m rid history path hphase ht).2.2.2 branch hb).1⟩
    rw [response_rows m hp rid history path ht]
    exact List.mem_map.mpr ⟨branch,hb,rfl⟩
  have he := HistoricalAcquisition.every_supported_branch_is_entry _ (raw m) _ (rawReady m hp) domain rid _
    (protocol_arrival m hp rid history path ht) _ (routes_read m hp)
    (.nominal,(data m).base.base.policy (history.getLastD .p0w0)) (response_computed m hp rid history path)
    (by change LaneDisturbance.nominal ∈ [LaneDisturbance.nominal]; decide)
    (by change (data m).base.base.policy (history.getLastD .p0w0) ∈ actions; cases (data m).base.base.policy (history.getLastD .p0w0) <;> decide)
    (response_normalized m hp rid history path ht) branch.1 hs
  rw [POS04HistoricalRuntime.update_eq _ _ (rawReady m hp)] at he
  exact he

theorem frame_injective : Function.Injective (frame Tag.target) := by
  intro x y h
  exact congrArg (fun r => (r ()).2) h

/-- Whole entry relation, not merely canonical examples: EVERY raw historical
entry and EVERY frozen phase-2 support branch agree under the raw protocol. -/
theorem raw_entries_iff (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema (raw m) (image m.assignment)
      (rawReady m hp) (frame .target r) ↔ POS04HistoricalAutonomy.HistoricalEntries m r := by
  constructor
  · rintro ⟨_,rid,arrived,rs,da,o,ha,hr,hresp,hd,hact,hn,hpos,hup⟩
    obtain ⟨history,path,ht⟩ := protocol_route_tuple m hp rid
    have harr := arrival_unique m hp rid history path ht arrived ha
    have hrs := Option.some.inj (hr.symm.trans (routes_read m hp))
    subst rs
    rw [harr] at hresp hpos hup
    change (raw m).response.eval _ _ (rid,rid) = some da at hresp
    have hda := Option.some.inj ((response_computed m hp rid history path).symm.trans hresp)
    subst da
    unfold StrategyGame.PositiveSupport at hpos
    rw [response_rows m hp rid history path ht] at hpos
    obtain ⟨w,hw,_⟩ := hpos
    obtain ⟨branch,hb,heq⟩ := List.mem_map.mp hw
    have heo : branch.1 = o := congrArg Prod.fst heq
    rw [POS04HistoricalRuntime.update_eq _ _ (rawReady m hp)] at hup
    have hrun := frame_injective hup
    have hphase := List.all_eq_true.mp hp.2.2.2.2 rid (by cases rid <;> decide)
    have hbentry := (POS04HistoricalAutonomy.target_response_all_support m rid history path hphase ht branch hb).1
    have hentry : (branch.2,r) ∈ POS04HistoricalAutonomy.phase2Execution m rid := by
      simpa only [← heo,hrun,received] using hbentry
    exact ⟨branch.2,List.mem_flatMap.mpr ⟨rid,(by cases rid <;> decide),hentry⟩⟩
  · rintro ⟨numerator,hm⟩
    obtain ⟨rid,_,hphaseentry⟩ := List.mem_flatMap.mp hm
    obtain ⟨history,path,ht⟩ := protocol_route_tuple m hp rid
    have hphase := List.all_eq_true.mp hp.2.2.2.2 rid (by cases rid <;> decide)
    rw [POS04HistoricalAutonomy.phase2Execution,
      POS04HistoricalAutonomy.arrival_computed m rid history path hphase ht] at hphaseentry
    obtain ⟨branch,hb,heq⟩ := List.mem_map.mp hphaseentry
    have hrun := congrArg Prod.snd heq
    dsimp only at hrun
    rw [← hrun]
    exact branch_entry m hp rid history path ht branch hb

theorem entries_iff (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6) :
    HistoricalPackageRuntime.Entries (model m) m.assignment (ready m hp) (frame .target r) ↔
      POS04OperationalGame.Entries m r := by
  simpa only [HistoricalPackageRuntime.Entries,POS04HistoricalRuntime.target_eq] using
    (raw_entries_iff m hp r).trans (POS04HistoricalAutonomy.entries_iff m hp r)

theorem entries_target (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m)
    (x : Registers Unit FrameValue)
    (he : HistoricalPackageRuntime.Entries (model m) m.assignment (ready m hp) x) :
    ∃ r, x = frame .target r ∧ POS04OperationalGame.Entries m r := by
  have heRaw : HistoricalAcquisition.Entry POS04ExecutionFrontier.schema (raw m) (image m.assignment)
      (rawReady m hp) x := by
    simpa only [HistoricalPackageRuntime.Entries,POS04HistoricalRuntime.target_eq] using he
  rcases heRaw with ⟨_,rid,arrived,rs,da,o,ha,hr,hresp,hd,hact,hn,hpos,hup⟩
  obtain ⟨history,path,ht⟩ := protocol_route_tuple m hp rid
  rw [arrival_unique m hp rid history path ht arrived ha,
    POS04HistoricalRuntime.update_eq _ _ (rawReady m hp)] at hup
  refine ⟨_,hup,(entries_iff m hp _).mp ?_⟩
  simpa only [hup] using he

/-- Entry equivalence is itself bound to the extracted instruction, not a
caller-provided protocol Boolean. It remains valid for arbitrary partial inputs. -/
theorem checked_entries_iff (m : RawLaneModel)
    (hc : (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) = some true)
    (r : Run6) :
    HistoricalPackageRuntime.Entries (model m) m.assignment
      (ready m ((POS04HistoricalRuntimeProtocol.check_iff m).mp hc)) (frame .target r) ↔
      POS04OperationalGame.Entries m r :=
  entries_iff m ((POS04HistoricalRuntimeProtocol.check_iff m).mp hc) r

theorem baseline_entries_iff (r : Run6) :
    HistoricalPackageRuntime.Entries (model baseline) baseline.assignment
      (ready baseline POS04ExactGames.positive_games.2.1) (frame .target r) ↔
      POS04OperationalGame.Entries baseline r := entries_iff baseline POS04ExactGames.positive_games.2.1 r

theorem duplicate_event_entries_iff (r : Run6) :
    HistoricalPackageRuntime.Entries (model POS04HistoricalDuplicateEvents.diagnostic)
      POS04HistoricalDuplicateEvents.diagnostic.assignment
      (ready _ (((POS04OperationalGame.game_iff_ao _).mpr POS04HistoricalDuplicateEvents.legacy_ao_accepts).1))
      (frame .target r) ↔ POS04OperationalGame.Entries POS04HistoricalDuplicateEvents.diagnostic r :=
  entries_iff _ (((POS04OperationalGame.game_iff_ao _).mpr POS04HistoricalDuplicateEvents.legacy_ao_accepts).1) r

theorem missing_past_ticks_entries_iff (r : Run6) :
    HistoricalPackageRuntime.Entries (model POS04RuntimeEquivalenceBoundary.missingPastTicks)
      POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment
      (ready _ POS04RuntimeEquivalenceBoundary.legacy_operational_game_accepts.1) (frame .target r) ↔
      POS04OperationalGame.Entries POS04RuntimeEquivalenceBoundary.missingPastTicks r :=
  entries_iff _ POS04RuntimeEquivalenceBoundary.legacy_operational_game_accepts.1 r

/-- Every declared dependency is read eagerly by the extracted protocol.
An absent primitive cannot be replaced by a decoder fallback. -/
theorem missing_protocol_cell_rejected (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) (hm : image m.assignment k = none) :
    (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) = none :=
  POS04HistoricalRuntimeProtocol.missing_rejected m k hk hm

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalEntryEquivalence
