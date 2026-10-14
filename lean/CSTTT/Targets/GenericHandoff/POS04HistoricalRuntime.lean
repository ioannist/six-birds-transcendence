import CSTTT.Targets.GenericHandoff.POS04HistoricalRuntimeProtocol
import CSTTT.Targets.GenericHandoff.POS04RawFiniteAutonomy
import CSTTT.Targets.GenericHandoff.HistoricalFiniteAutonomy

/-! POS-04 historical acquisition and multi-resource runtime on ONE staged
assignment. The source past is raw support, not funded source execution. The
receiver writes the actual terminal coordinates and raw provenance, resets
counters, and executes the target-only actual updater. No source ticks,
source funding or hazards enter this operational execution. Every ambient
branch is retained. This component does not yet claim whole-game AF/AO
equivalence or the final RawHandoff promotion. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalRuntime
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter RegisterInitialization
open POS04RouteExecution POS04ResourceRuntime
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- The actual target updater, including all counters/ledger updates. No
funded source transition is needed to validate a recorded source past. -/
def execution : ResourceRuntime.Execution Cell Value Unit FrameValue LaneDisturbance Action Ambient :=
  ⟨[.nominal],actions,ambientStates,lift (POS04RegisterFuture.enabledRow .target),
    fun _ => nextExpression .target⟩

def historical : HistoricalAcquisition.Bindings Cell Value Unit FrameValue
    LaneDisturbance Action KState KState CSTTT.POS04.Stage EventId RouteId RouteId where
  histories := POS04HistoricalAcquisition.raw.histories
  sourceRows := POS04HistoricalAcquisition.raw.sourceRows
  sourcePolicy := POS04HistoricalAcquisition.raw.sourcePolicy
  targetCoordinate := POS04HistoricalAcquisition.raw.targetCoordinate
  targetRows := POS04HistoricalAcquisition.raw.targetRows
  targetPolicy := POS04HistoricalAcquisition.raw.targetPolicy
  routes := POS04HistoricalAcquisition.raw.routes
  events := POS04HistoricalAcquisition.raw.events
  activationEvents := POS04HistoricalAcquisition.raw.activationEvents
  realized := POS04HistoricalAcquisition.raw.realized
  receiver := POS04HistoricalAcquisition.raw.receiver
  reset := fun _ => .map (fun (v : Receiver × HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) =>
      (Tag.target,⟨Ambient.inK v.2.1,0,0,(v.2.2.1,v.2.2.2.1),v.1.funded⟩))
    (.pair (.cell Cell.receiverInput) (.environment id))
  response := lift POS04ExecutionFrontier.acquisition.arrivalResponse

def model (p : Protocol) : HistoricalPackageRuntime.Raw Cell Cell Value Value Unit FrameValue
    LaneDisturbance Action Ambient KState KState KState Resource
    (List KState × List EventId) CSTTT.POS04.Stage EventId RouteId RouteId where
  package := POS04DispatchedStage.raw
  resourceSchema := RuntimeComponents.resourceSchema cfg
  acquisitionSchema := POS04ExecutionFrontier.schema
  execution := execution
  resource := bindings p
  historical := historical
  runCells := runCells p

theorem target_eq (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    HistoricalPackageRuntime.target (model p) a = image a :=
  POS04DispatchedStage.global_eq_image a

theorem package_readout_iff (m : RawLaneModel) :
    HistoricalPackageRuntime.IntegratedTargetRealization (model (protocol m)) m.assignment ↔ PackageLane m.assignment := by
  change PackageRuntime.IntegratedTargetRealization (POS04ResourceRuntime.model (protocol m)) m.assignment ↔ _
  exact POS04ResourceRuntime.package_readout_iff m

/-- All raw cells are retained, including missing values. Only the target
recharge availability follows the declared post-exit retention rule. -/
theorem run_assignment_eq (m : RawLaneModel) (r : Registers Unit FrameValue) :
    HistoricalPackageRuntime.runAssignment (model (protocol m)) m.assignment r = withdrawnAssignment m := by
  change (fun k => (runCells (protocol m) k).eval
    (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) r ()) = _
  rw [target_eq]
  have he := POS04ResourceRuntime.run_assignment_eq m r
  unfold PackageRuntime.runAssignment at he
  rw [POS04ResourceRuntime.target_eq] at he
  exact he

abbrev factorFrame := POS04RawFiniteAutonomy.factorFrame
abbrev Checked (m : RawLaneModel) := HistoricalFiniteAutonomy.Checked
  (model (protocol m)) (factorFrame (protocol m)) m.assignment

theorem finite_cells_eq (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (x : KState) (r : Registers Unit FrameValue) (k : Cell) :
    (POS04RawFiniteAutonomy.finiteCells p k).eval a (fun _ => ()) x = (runCells p k).eval a r () := by
  cases k with
  | resources t => cases t <;> rfl
  | _ => rfl

theorem primitive_lift (m : RawLaneModel) (h : Checked m) (r : Registers Unit FrameValue) :
    HistoricalFiniteAutonomy.factorAssignment (model (protocol m)) (factorFrame (protocol m)) m.assignment
      (HistoricalFiniteAutonomy.project _ _ _ h r) = HistoricalPackageRuntime.runAssignment (model (protocol m)) m.assignment r := by
  funext k
  exact finite_cells_eq _ _ _ _ k

theorem required_eq (m : RawLaneModel) (h : Checked m) (x : KState) :
    HistoricalFiniteAutonomy.required (model (protocol m)) (factorFrame (protocol m)) m.assignment h x = [.recharge] := by
  have he := HistoricalFiniteAutonomy.readEnv_eq (factorFrame (protocol m)).maintenance
    (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) h.maintenance x
  exact (Option.some.inj he).symm

theorem resource_lift (m : RawLaneModel) (h : Checked m) (r : Registers Unit FrameValue) :
    (HistoricalPackageRuntime.resources (model (protocol m))).required.eval
      (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) r () =
      some (HistoricalFiniteAutonomy.required _ _ _ h (HistoricalFiniteAutonomy.project _ _ _ h r)) := by
  rw [required_eq]
  rfl

theorem withdrawal_eq (m : RawLaneModel) (h : Checked m) :
    HistoricalFiniteAutonomy.withdrawalData (model (protocol m)) (factorFrame (protocol m)) m.assignment h =
      withdrawal (protocol m) := by
  have hl := h.ready.2.2 Cell.maintenance (by
    simp [model,HistoricalPackageRuntime.resources,
      execution,bindings,ResourceRuntime.Raw.readDependencies])
  rw [target_eq] at hl
  have hp := POS04RegisterDynamics.cell_value hl
  have he := (HistoricalFiniteAutonomy.withdrawal_fields _ _ _ h).1
  rw [target_eq] at he
  change (image m.assignment Cell.maintenance).map (fun _ => withdrawal (protocol m)) = _ at he
  rw [hp] at he
  exact (Option.some.inj he).symm

theorem retained_is_recharge (m : RawLaneModel) (h : Checked m) (res : Resource)
    (hr : res ∈ (HistoricalFiniteAutonomy.withdrawalData (model (protocol m)) (factorFrame (protocol m)) m.assignment h).retained) :
    res = .recharge := by
  rw [withdrawal_eq] at hr
  obtain ⟨r,_,he⟩ := List.mem_map.mp hr
  exact he.symm

theorem owner_read (m : RawLaneModel) (h : Checked m) (res : Resource)
    (r : ResourceData) (he : image m.assignment (.resources .target) = some r) :
    HistoricalFiniteAutonomy.readEnv (factorFrame (protocol m)).resourceOwner
      (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) h.resourceOwner res =
      match res with | .recharge => tagCarrierId r.owner | .removed _ => tagCarrierId .source := by
  have hx := HistoricalFiniteAutonomy.readEnv_eq (factorFrame (protocol m)).resourceOwner
    (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) h.resourceOwner res
  conv at hx => lhs; rw [target_eq]
  simp only [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.eval] at hx
  rw [he] at hx
  exact (Option.some.inj hx).symm

theorem action_owner_read (m : RawLaneModel) (h : Checked m) (act : Action)
    (r : ResourceData) (he : image m.assignment (.resources .target) = some r) :
    HistoricalFiniteAutonomy.readEnv (factorFrame (protocol m)).actionOwner
      (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) h.actionOwner act = tagCarrierId r.owner := by
  have hx := HistoricalFiniteAutonomy.readEnv_eq (factorFrame (protocol m)).actionOwner
    (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) h.actionOwner act
  conv at hx => lhs; rw [target_eq]
  simp only [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.eval] at hx
  rw [he] at hx
  exact (Option.some.inj hx).symm

/-- Actual accounts use exactly the same owner cell as the finite owner
instruction, even before any assumption that the owner is the target. -/
theorem account_owner_lift (m : RawLaneModel) (h : Checked m)
    (run : Registers Unit FrameValue) (ac : Resource → ResourceRuntime.Account)
    (he : (HistoricalPackageRuntime.resources (model (protocol m))).accounts.eval
      (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) run () = some ac)
    (res : Resource) (hr : res ∈ (HistoricalFiniteAutonomy.withdrawalData _ _ _ h).retained) :
    (ac res).owner = some (HistoricalFiniteAutonomy.readEnv (factorFrame (protocol m)).resourceOwner
      (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) h.resourceOwner res) := by
  have hres := h.resourceOwner (.resources .target) (by simp [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies])
  rw [target_eq] at hres
  have hval := POS04RegisterDynamics.cell_value hres
  have hm := h.ready.2.2 Cell.maintenance (by
    simp [model,HistoricalPackageRuntime.resources,
      execution,bindings,ResourceRuntime.Raw.readDependencies])
  rw [target_eq] at hm
  have hv := POS04RegisterDynamics.cell_value hm
  rw [target_eq] at he
  change (accounts (protocol m)).eval (image m.assignment) run () = some ac at he
  simp only [accounts,Expr.eval] at he
  rw [hval,hv] at he
  simp only [Option.map_some] at he
  have heq := Option.some.inj he
  rw [retained_is_recharge m h res hr,← heq,owner_read m h .recharge _ hval]

/-- The full lifting equations are proved for arbitrary partial assignments,
under the explicit checked ownership premise. This premise is derived from a
genuine game entry below, not a supplied ownership verdict. -/
theorem lift (m : RawLaneModel) (h : Checked m)
    (rdata : ResourceData) (he : image m.assignment (.resources .target) = some rdata)
    (ho : rdata.owner = .target) :
    HistoricalFiniteAutonomy.Lift (model (protocol m)) (factorFrame (protocol m)) m.assignment h := by
  constructor
  · intro r _; exact primitive_lift m h r
  · intro r _; exact resource_lift m h r
  · intro res hr
    rw [retained_is_recharge m h res hr,owner_read m h .recharge rdata he,ho]
    rfl
  · intro r ac _ hx res hr; exact account_owner_lift m h r ac hx res hr
  · intro run d act _ _
    rw [action_owner_read m h act rdata he,ho]
    rfl

theorem ownership_of_resource_closed (m : RawLaneModel) (h : Checked m)
    (run : Registers Unit FrameValue)
    (hr : ResourceRuntime.ResourceClosed (model (protocol m)).resourceSchema
      (HistoricalPackageRuntime.resources (model (protocol m)))
      (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) run) :
    ∃ rdata, image m.assignment (.resources .target) = some rdata ∧ rdata.owner = .target := by
  have hp := h.resourceOwner (.resources .target) (by simp [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies])
  rw [target_eq] at hp
  have hv := POS04RegisterDynamics.cell_value hp
  refine ⟨_,hv,?_⟩
  rcases hr with ⟨ac,req,w,ha,hreq,hw,_,_,_,hsub,hs,_⟩
  change some ([.recharge] : List Resource) = some req at hreq
  have heq := Option.some.inj hreq
  subst req
  have hret := hs .recharge (by simp)
  have hmem : Resource.recharge ∈ (HistoricalFiniteAutonomy.withdrawalData _ _ _ h).retained := by
    have hew := Option.some.inj (hw.symm.trans (HistoricalFiniteAutonomy.withdrawal_fields _ _ _ h).1)
    rw [← hew]
    exact hsub (by simp)
  have howner := account_owner_lift m h run ac ha .recharge hmem
  rw [owner_read m h .recharge _ hv] at howner
  have hc : tagCarrierId ((image m.assignment (.resources .target)).getD (canonicalValue _)).owner = tagCarrierId .target :=
    Option.some.inj (howner.symm.trans hret.1)
  cases hx : ((image m.assignment (.resources .target)).getD (canonicalValue _)).owner with
  | target => rfl
  | source =>
    rw [hx] at hc
    have bad := congrArg CarrierId.code hc
    change (0 : Nat) = 1 at bad
    contradiction

/-- Ownership is derived at a genuine activated game entry. -/
theorem lift_of_game (m : RawLaneModel) (h : Checked m)
    (ha : HistoricalPackageRuntime.AcquisitionReady (model (protocol m)) m.assignment)
    (hg : HistoricalPackageRuntime.FullGame (model (protocol m)) m.assignment ha h.ready) :
    HistoricalFiniteAutonomy.Lift (model (protocol m)) (factorFrame (protocol m)) m.assignment h := by
  obtain ⟨entry,he⟩ := hg.2.1
  obtain ⟨_,_,strategy,hs⟩ := hg
  have safe := (hs entry he entry [] StrategyGame.Play.initial).2.1
  obtain ⟨rdata,hr,ho⟩ := ownership_of_resource_closed m h entry safe
  exact lift m h rdata hr ho

theorem game_each_entry_exact (m : RawLaneModel) (h : Checked m)
    (ha : HistoricalPackageRuntime.AcquisitionReady (model (protocol m)) m.assignment)
    (hg : HistoricalPackageRuntime.FullGame (model (protocol m)) m.assignment ha h.ready) :
    ∃ cert : HistoricalPackageRuntime.FullCertificate (model (protocol m)) m.assignment ha h.ready,
      ∀ entry, HistoricalPackageRuntime.Entries (model (protocol m)) m.assignment ha entry →
        Nonempty (CSTTT.AutonomyTheory.ExactAutonomyCertificate (GameAutonomyTransport.projectedData
          (HistoricalFiniteAutonomy.factor (model (protocol m)) (factorFrame (protocol m)) m.assignment h)
          cert (HistoricalFiniteAutonomy.project _ _ _ h) entry)) :=
  HistoricalFiniteAutonomy.each_entry_exact _ _ _ h (lift_of_game m h ha hg) ha hg

theorem canonical_resource_ready : HistoricalPackageRuntime.ResourceReady (model (protocol baseline)) canonical := by
  change ResourceRuntime.Ready (HistoricalPackageRuntime.resources (model (protocol baseline)))
    (HistoricalPackageRuntime.target (model (protocol baseline)) canonical)
  rw [target_eq,image_canonical]
  exact ⟨fun _ _ => rfl,fun _ _ _ => rfl,fun _ _ => rfl⟩

theorem canonical_withdrawal : HistoricalPackageRuntime.Withdrawal (model (protocol baseline)) canonical := by
  change ResourceRuntime.DomainCheck ((model (protocol baseline)).resourceSchema) ((HistoricalPackageRuntime.resources (model (protocol baseline)))) ∧
    ResourceRuntime.WithdrawalCheck ((model (protocol baseline)).resourceSchema) ((HistoricalPackageRuntime.resources (model (protocol baseline))))
      (HistoricalPackageRuntime.target (model (protocol baseline)) canonical)
  rw [target_eq,image_canonical]
  constructor
  · refine ⟨by decide,by decide,by decide,?_,?_,?_,?_,?_⟩
    · intro d; cases d; decide
    · intro a; cases a <;> decide +revert
    · intro o; cases o with
      | inK s => cases s <;> decide +revert
      | p2w0 => decide
      | p5w1 => decide
    · intro s; cases s <;> decide +revert
    · intro res; cases res with
      | recharge => decide
      | removed role => cases role <;> decide +revert
  · refine ⟨withdrawal (protocol baseline),rfl,?_,?_,?_,?_,?_,?_⟩
    · intro r hr; exact hr
    · intro r hr; exact hr
    · intro r hr; cases r <;> decide +revert
    · intro res hr; cases res with
      | recharge => simp [withdrawal,protocol,baseline] at hr
      | removed r => cases r <;> decide +revert
    · intro res hr; cases res with
      | recharge => decide
      | removed r => simp [withdrawal,protocol,baseline] at hr
    · intro res hr hret
      cases res with
      | recharge => simp [withdrawal,protocol,baseline] at hr
      | removed r => simp [withdrawal,protocol,baseline] at hret

theorem canonical_checked : Checked baseline := by
  refine ⟨canonical_resource_ready,canonical_withdrawal,?_,?_,?_,?_,resourceCode_injective,(by change tagCarrierId .source ≠ tagCarrierId .target; decide),rfl,rfl⟩
  all_goals rw [target_eq]; simp only [baseline]; rw [image_canonical]; intro k _; rfl

/-- Nonempty positive lift instance; these equations are not conditional on
an impossible readiness premise or on an unconstructed game. -/
theorem positive_lift : HistoricalFiniteAutonomy.Lift (model (protocol baseline))
    (factorFrame (protocol baseline)) canonical canonical_checked :=
  lift baseline canonical_checked (⟨.target,true⟩ : ResourceData) (by change image canonical _ = _; rw [image_canonical]; rfl) rfl



abbrev acquisitionRaw (p : Protocol) := HistoricalPackageRuntime.acquisition (model p)

def scope (p : Protocol) : List Cell :=
  (acquisitionRaw p).dependencies ++ ((acquisitionRaw p).reset ()).dependencies ++
    (acquisitionRaw p).execution.row.dependencies ++ ((acquisitionRaw p).execution.program ()).dependencies

theorem scope_subset (p : Protocol) : scope p ⊆ phase2Dependencies := by
  intro k hk
  have eq : scope p = scope (protocol baseline) := rfl
  rw [eq] at hk
  exact (by decide : scope (protocol baseline) ⊆ phase2Dependencies) hk

theorem no_source_ticks (p : Protocol) : Cell.ticks .source ∉ scope p :=
  fun h => (by decide : Cell.ticks .source ∉ phase2Dependencies) (scope_subset p h)
theorem no_source_resources (p : Protocol) : Cell.resources .source ∉ scope p :=
  fun h => (by decide : Cell.resources .source ∉ phase2Dependencies) (scope_subset p h)
theorem no_hazards (p : Protocol) : Cell.hazards ∉ scope p :=
  fun h => (by decide : Cell.hazards ∉ phase2Dependencies) (scope_subset p h)

theorem acquisition_ready (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete (scope p) a) : HistoricalAcquisition.Ready (acquisitionRaw p) a := by
  refine ⟨fun k hk => hc k (by simp [scope,hk]),?_,?_,?_⟩
  · intro reg k hk; cases reg; exact hc k (by simp [scope,hk])
  · intro k hk; exact hc k (by simp [scope,hk])
  · intro reg k hk; cases reg; exact hc k (by simp [scope,hk])

theorem acquisition_ready_iff (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    HistoricalAcquisition.Ready (acquisitionRaw p) a ↔ Complete (scope p) a := by
  constructor
  · intro h k hk
    simp only [scope,List.mem_append] at hk
    rcases hk with ((hk | hk) | hk) | hk
    · exact h.1 k hk
    · exact h.2.1 () k hk
    · exact h.2.2.1 k hk
    · exact h.2.2.2 () k hk
  · exact acquisition_ready p a

theorem canonical_acquisition_ready (p : Protocol) : HistoricalAcquisition.Ready (acquisitionRaw p) canonical :=
  acquisition_ready p canonical (fun _ _ => rfl)

theorem reset_link (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready (acquisitionRaw p) a)
    (hreg : HistoricalAcquisition.Ready POS04HistoricalAcquisition.raw a)
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    HistoricalAcquisition.reset (acquisitionRaw p) a h input =
      frame .target (POS04RegisterDynamics.decodeRun
        (HistoricalAcquisition.reset POS04HistoricalAcquisition.raw a hreg input)) := by
  have present := h.2.1 () Cell.receiverInput (by change Cell.receiverInput ∈ [Cell.receiverInput]; simp)
  have hv := POS04RegisterDynamics.cell_value present
  rw [POS04HistoricalAcquisition.reset_computed a hreg input _ hv,
    POS04RegisterDynamics.decode_encode]
  funext reg; cases reg
  apply Option.some.inj
  have he := RegisterInitialization.initial_eq (acquisitionRaw p).reset a h.2.1 input ()
  change (Expr.map (fun (v : Receiver × HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) =>
    (Tag.target,(⟨Ambient.inK v.2.1,0,0,(v.2.2.1,v.2.2.2.1),v.1.funded⟩ : Run6)))
      (.pair (.cell Cell.receiverInput) (.environment id))).eval a noRegisters input =
      some (HistoricalAcquisition.reset (acquisitionRaw p) a h input ()) at he
  simp only [Expr.eval] at he
  rw [hv] at he
  exact he.symm

theorem rows_eq (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready (acquisitionRaw p) a) (x : Run6)
    (d : LaneDisturbance) (act : Action) :
    HistoricalAcquisition.rows (acquisitionRaw p) a (frame .target x) d act =
      actualRows6 (runInputs6 a .target) x act := by
  have hc := (acquisition_ready_iff p a).mp h
  have hr := POS04RegisterDynamics.cell_value (hc (.resources .target) (by change _ ∈ scope (protocol baseline); decide))
  have hl := POS04RegisterDynamics.cell_value (hc .maintenance (by change _ ∈ scope (protocol baseline); decide))
  have hrows : (a (.rows .target)).isSome = true := hc _ (by change _ ∈ scope (protocol baseline); decide)
  have he := POS04RegisterDynamics.row_eval a .target hrows x d act
  change ((POS04RouteExecution.lift (POS04RegisterFuture.enabledRow .target)).eval a (frame .target x) (d,act)).getD [] = _
  rw [POS04RouteExecution.lift,frame,RunFrame.evaluation]
  change ((POS04RegisterFuture.enabledRow .target).eval a (POS04RegisterDynamics.encode x) (d,act)).getD [] = _
  simp only [POS04RegisterFuture.enabledRow,Expr.eval]
  rw [hr,hl,he]
  rfl

theorem update_eq (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready (acquisitionRaw p) a) (x : Run6)
    (d : LaneDisturbance) (act : Action) (o : Ambient) :
    HistoricalAcquisition.update (acquisitionRaw p) a h (frame .target x) d act o =
      frame .target (actualUpdate6 (runInputs6 a .target) x act o) := by
  have hc := (acquisition_ready_iff p a).mp h
  have core : Complete (POS04RegisterDynamics.coreDependencies .target) a := by
    intro k hk
    apply hc k
    simp [POS04RegisterDynamics.coreDependencies] at hk
    rcases hk with hk | hk | hk <;> subst k <;> change _ ∈ scope (protocol baseline) <;> decide
  have he := POS04RegisterDynamics.program_actual a .target core x d act o
  have evals (r : POS04RegisterDynamics.Register) := congrFun he r
  funext reg; cases reg
  apply Option.some.inj
  have eq := checked_execute_eq (acquisitionRaw p).execution.program a h.2.2.2
    (frame .target x) (d,act,o) ()
  change (nextExpression .target).eval a (frame .target x) (d,act,o) =
    some (HistoricalAcquisition.update (acquisitionRaw p) a h (frame .target x) d act o ()) at eq
  have sub (r : POS04RegisterDynamics.Register) :
      (POS04RouteExecution.lift (POS04RegisterDynamics.program .target r)).eval a (frame .target x) (d,act,o) =
      some (POS04RegisterDynamics.encode (actualUpdate6 (runInputs6 a .target) x act o) r) := by
    rw [POS04RouteExecution.lift,frame,RunFrame.evaluation]
    exact evals r
  simp only [nextExpression,Expr.eval,sub] at eq
  simp only [frame,RunFrame.pack,Option.map_some,POS04RegisterDynamics.encode] at eq
  exact eq.symm


theorem arrival_from_registers (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready (acquisitionRaw p) a)
    (hreg : HistoricalAcquisition.Ready POS04HistoricalAcquisition.raw a)
    (rid : RouteId) (r : Registers POS04RegisterDynamics.Register POS04RegisterDynamics.RegisterValue)
    (ha : HistoricalAcquisition.Arrival POS04ExecutionFrontier.schema POS04HistoricalAcquisition.raw a hreg rid r) :
    HistoricalAcquisition.Arrival POS04ExecutionFrontier.schema (acquisitionRaw p) a h rid
      (frame .target (POS04RegisterDynamics.decodeRun r)) := by
  rcases ha with ⟨hs,sr,sp,coord,tr,tp,rs,ev,real,rec,first,rest,
    hh,hr,hsp,hcoord,htr,htp,hrs,hev,hreal,hrec,hrid,hhid,hlist,hss,hts,hpath,hact,hreset⟩
  refine ⟨hs,sr,sp,coord,tr,tp,rs,ev,real,rec,first,rest,
    hh,hr,hsp,hcoord,htr,htp,hrs,hev,hreal,hrec,hrid,hhid,hlist,hss,hts,hpath,hact,?_⟩
  rw [hreset,reset_link p a h hreg]

theorem canonical_arrival (p : Protocol) (rid : RouteId) :
    HistoricalAcquisition.Arrival POS04ExecutionFrontier.schema (acquisitionRaw p) canonical
      (canonical_acquisition_ready p) rid (frame .target (arrivalFor rid)) := by
  have h := arrival_from_registers p canonical (canonical_acquisition_ready p)
    POS04HistoricalAcquisition.canonical_ready rid _ (POS04HistoricalAcquisition.canonical_arrival rid)
  simpa only [POS04RegisterDynamics.decode_encode] using h

/-- Every consumed acquisition cell rejects before reception or execution. -/
theorem missing_acquisition_no_games (m : RawLaneModel) (k : Cell)
    (hk : k ∈ scope (protocol m)) (hm : image m.assignment k = none) :
    ¬ HistoricalPackageRuntime.PostWithdrawalFullAutonomy (model (protocol m)) m.assignment ∧
      ¬ HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy (model (protocol m)) m.assignment := by
  have bad : ¬ HistoricalPackageRuntime.AcquisitionReady (model (protocol m)) m.assignment := by
    intro h
    rw [show HistoricalPackageRuntime.AcquisitionReady (model (protocol m)) m.assignment ↔
      HistoricalAcquisition.Ready (acquisitionRaw (protocol m)) (image m.assignment) from by rw [HistoricalPackageRuntime.AcquisitionReady,target_eq]] at h
    have present := (acquisition_ready_iff _ _).mp h k hk
    rw [hm] at present
    contradiction
  exact ⟨fun ⟨h,_,_⟩ => bad h,fun ⟨h,_,_⟩ => bad h⟩


/-- Exact target-row identity on ALL run contexts, including exit states. -/
theorem rows_from_registers (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready (acquisitionRaw p) a)
    (hr : HistoricalAcquisition.Ready POS04HistoricalAcquisition.raw a)
    (r : Registers POS04RegisterDynamics.Register POS04RegisterDynamics.RegisterValue)
    (d : LaneDisturbance) (act : Action) :
    HistoricalAcquisition.rows (acquisitionRaw p) a (frame .target (POS04RegisterDynamics.decodeRun r)) d act =
      HistoricalAcquisition.rows POS04HistoricalAcquisition.raw a r d act := by
  rw [rows_eq p a h]
  have he := POS04HistoricalAcquisition.actual_row a hr (POS04RegisterDynamics.decodeRun r) d act
  simpa only [POS04RegisterDynamics.encode_decode] using he.symm

theorem update_from_registers (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready (acquisitionRaw p) a)
    (hr : HistoricalAcquisition.Ready POS04HistoricalAcquisition.raw a)
    (r : Registers POS04RegisterDynamics.Register POS04RegisterDynamics.RegisterValue)
    (d : LaneDisturbance) (act : Action) (o : Ambient) :
    HistoricalAcquisition.update (acquisitionRaw p) a h (frame .target (POS04RegisterDynamics.decodeRun r)) d act o =
      frame .target (POS04RegisterDynamics.decodeRun
        (HistoricalAcquisition.update POS04HistoricalAcquisition.raw a hr r d act o)) := by
  rw [update_eq]
  have he := POS04HistoricalAcquisition.updater_computed a hr (POS04RegisterDynamics.decodeRun r) d act o
  rw [POS04RegisterDynamics.encode_decode] at he
  rw [he,POS04RegisterDynamics.decode_encode]

/-- Every actual branch transfers; this is not a selected entry witness or
an inference from nominal protocol acceptance. -/
theorem entry_from_registers (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (h : HistoricalAcquisition.Ready (acquisitionRaw p) a)
    (hr : HistoricalAcquisition.Ready POS04HistoricalAcquisition.raw a)
    (r : Registers POS04RegisterDynamics.Register POS04RegisterDynamics.RegisterValue)
    (he : HistoricalAcquisition.Entry POS04ExecutionFrontier.schema POS04HistoricalAcquisition.raw a hr r) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema (acquisitionRaw p) a h
      (frame .target (POS04RegisterDynamics.decodeRun r)) := by
  rcases he with ⟨domain,rid,received,routes,da,o,ha,hroute,hresp,hd,hact,hn,hp,hup⟩
  refine ⟨domain,rid,frame .target (POS04RegisterDynamics.decodeRun received),routes,da,o,
    arrival_from_registers p a h hr rid received ha,hroute,?_,hd,hact,?_,?_,?_⟩
  · change (POS04RouteExecution.lift POS04ExecutionFrontier.acquisition.arrivalResponse).eval
      a (frame .target (POS04RegisterDynamics.decodeRun received)) ((routes rid).history,rid) = some da
    rw [POS04RouteExecution.lift,frame,RunFrame.evaluation]
    simpa only [decode,POS04RegisterDynamics.encode_decode] using hresp
  · simpa only [StrategyGame.Normalized,StrategyGame.PositiveSupport,rows_from_registers p a h hr] using hn
  · simpa only [StrategyGame.PositiveSupport,rows_from_registers p a h hr] using hp
  · rw [hup,update_from_registers]

theorem canonical_entry (p : Protocol) (rid : RouteId) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema (acquisitionRaw p) canonical
      (canonical_acquisition_ready p) (frame .target (resultFor rid)) := by
  have he := entry_from_registers p canonical (canonical_acquisition_ready p)
    POS04HistoricalAcquisition.canonical_ready _ (POS04HistoricalAcquisition.canonical_entry rid)
  simpa only [POS04RegisterDynamics.decode_encode] using he


/-- The exact extracted nominal protocol supplies presence on every target
resource instruction. No source updater dependency is introduced. -/
theorem resource_ready_of_protocol (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    HistoricalPackageRuntime.ResourceReady (model (protocol m)) m.assignment := by
  have hc : Complete phase2Dependencies (image m.assignment) := fun k hk =>
    POS04OperationalGame.protocol_complete m hp k (List.mem_append_right _ hk)
  change ResourceRuntime.Ready (HistoricalPackageRuntime.resources (model (protocol m)))
    (HistoricalPackageRuntime.target (model (protocol m)) m.assignment)
  rw [target_eq]
  refine ⟨?_,?_,?_⟩
  · intro k hk; apply hc k
    exact (by decide : execution.row.dependencies ⊆ phase2Dependencies) hk
  · intro reg k hk; cases reg; apply hc k
    exact (by decide : (execution.program ()).dependencies ⊆ phase2Dependencies) hk
  · intro k hk; apply hc k
    have hs : (HistoricalPackageRuntime.resources (model (protocol m))).readDependencies =
        (HistoricalPackageRuntime.resources (model (protocol baseline))).readDependencies := rfl
    rw [hs] at hk
    exact (by decide : (HistoricalPackageRuntime.resources (model (protocol baseline))).readDependencies ⊆ phase2Dependencies) hk

/-- Nonempty disturbance domain, all six role removals, and disjoint raw
resources are checked rather than inherited from a positive baseline. -/
theorem withdrawal_of_protocol (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    HistoricalPackageRuntime.Withdrawal (model (protocol m)) m.assignment := by
  have hc := POS04OperationalGame.protocol_complete m hp
  have hv := POS04RegisterDynamics.cell_value (hc .maintenance (by decide))
  have removed : ∀ role : ResourceRuntime.Role, role ∈ (m.removed.map roleImage) := by
    intro role
    have has : ∀ r ∈ removedRoles, r ∈ m.removed := by
      have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hp.2.1).1).1
      intro r hr
      simpa using (List.all_eq_true.mp hh r hr)
    cases role
    all_goals apply List.mem_map.mpr
    case source => exact ⟨.source,has _ (by decide),rfl⟩
    case migrationBridge => exact ⟨.migrationBridge,has _ (by decide),rfl⟩
    case migrationController => exact ⟨.migrationController,has _ (by decide),rfl⟩
    case externalDecoder => exact ⟨.externalDecoder,has _ (by decide),rfl⟩
    case externalScheduler => exact ⟨.externalScheduler,has _ (by decide),rfl⟩
    case undeclaredRepair => exact ⟨.undeclaredRepair,has _ (by decide),rfl⟩
  change ResourceRuntime.DomainCheck (model (protocol m)).resourceSchema
      (HistoricalPackageRuntime.resources (model (protocol m))) ∧
    ResourceRuntime.WithdrawalCheck (model (protocol m)).resourceSchema
      (HistoricalPackageRuntime.resources (model (protocol m)))
      (HistoricalPackageRuntime.target (model (protocol m)) m.assignment)
  rw [target_eq]
  constructor
  · exact canonical_withdrawal.1
  · refine ⟨withdrawal (protocol m),?_,?_,?_,?_,?_,?_,?_⟩
    · change (image m.assignment .maintenance).map (fun _ => withdrawal (protocol m)) = _
      rw [hv]
      rfl
    · intro role _; exact removed role
    · intro role _; cases role <;> decide
    · intro role _ res hr
      have eq := List.mem_singleton.mp hr
      subst res
      obtain ⟨r,hr,he⟩ := List.mem_map.mp (removed role)
      exact List.mem_map.mpr ⟨r,hr,congrArg Resource.removed he⟩
    · intro res hr
      obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
      cases r <;> change _ ∈ resources <;> decide
    · intro res hr
      obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
      change Resource.recharge ∈ resources
      decide
    · intro res hr hret
      obtain ⟨r,_,rfl⟩ := List.mem_map.mp hr
      obtain ⟨s,_,he⟩ := List.mem_map.mp hret
      contradiction

theorem checked_of_protocol (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) : Checked m := by
  have hc := POS04OperationalGame.protocol_complete m hp
  refine ⟨resource_ready_of_protocol m hp,withdrawal_of_protocol m hp,?_,?_,?_,?_,
    resourceCode_injective,(by change tagCarrierId .source ≠ tagCarrierId .target; decide),rfl,rfl⟩
  all_goals rw [target_eq]
  · intro k hk; simp [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies] at hk
  · intro k hk; simp [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies] at hk
  · intro k hk
    have eq : k = Cell.resources .target := by simpa [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies] using hk
    subst k; exact hc _ (by decide)
  · intro k hk
    have eq : k = Cell.resources .target := by simpa [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies] using hk
    subst k; exact hc _ (by decide)


/-- The public game supplies the remaining finite-frame checks. No ownership
or nominal baseline premise is supplied: ownership is subsequently derived at
its genuine entry by lift_of_game. -/
theorem checked_of_full_game (m : RawLaneModel)
    (ha : HistoricalPackageRuntime.AcquisitionReady (model (protocol m)) m.assignment)
    (hr : HistoricalPackageRuntime.ResourceReady (model (protocol m)) m.assignment)
    (hg : HistoricalPackageRuntime.FullGame (model (protocol m)) m.assignment ha hr) : Checked m := by
  refine ⟨hr,hg.1,?_,?_,?_,?_,resourceCode_injective,
    (by change tagCarrierId .source ≠ tagCarrierId .target; decide),rfl,rfl⟩
  · intro k hk; simp [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies] at hk
  · intro k hk; simp [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies] at hk
  · intro k hk
    have eq : k = Cell.resources .target := by simpa [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies] using hk
    subst k
    exact hr.2.2 _ (by change Cell.resources .target ∈
      (HistoricalPackageRuntime.resources (model (protocol baseline))).readDependencies; decide)
  · intro k hk
    have eq : k = Cell.resources .target := by simpa [factorFrame,POS04RawFiniteAutonomy.factorFrame,Expr.dependencies] using hk
    subst k
    exact hr.2.2 _ (by change Cell.resources .target ∈
      (HistoricalPackageRuntime.resources (model (protocol baseline))).readDependencies; decide)

/-- Exact finite-factor TTH-05 transport for every partial assignment whose
DEFINED historical full game holds. The Checks and Lift are derived here. -/
theorem full_readout_transport (m : RawLaneModel)
    (hg : HistoricalPackageRuntime.PostWithdrawalFullAutonomy (model (protocol m)) m.assignment) :
    ∃ h : Checked m, ∃ ha : HistoricalPackageRuntime.AcquisitionReady (model (protocol m)) m.assignment,
      ∃ cert : HistoricalPackageRuntime.FullCertificate (model (protocol m)) m.assignment ha h.ready,
        ∀ entry, HistoricalPackageRuntime.Entries (model (protocol m)) m.assignment ha entry →
          Nonempty (CSTTT.AutonomyTheory.ExactAutonomyCertificate (GameAutonomyTransport.projectedData
            (HistoricalFiniteAutonomy.factor (model (protocol m)) (factorFrame (protocol m)) m.assignment h)
            cert (HistoricalFiniteAutonomy.project _ _ _ h) entry)) := by
  obtain ⟨ha,hr,game⟩ := hg
  let h := checked_of_full_game m ha hr game
  exact ⟨h,ha,game_each_entry_exact m h ha game⟩


theorem acquisition_ready_of_protocol (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) :
    HistoricalPackageRuntime.AcquisitionReady (model (protocol m)) m.assignment := by
  change HistoricalAcquisition.Ready (acquisitionRaw (protocol m)) (HistoricalPackageRuntime.target (model (protocol m)) m.assignment)
  rw [target_eq]
  exact acquisition_ready _ _ (fun k hk => POS04OperationalGame.protocol_complete m hp k
    (List.mem_append_right _ (scope_subset _ hk)))

/-- Missing resources reject both public games BEFORE instruction totalization;
this guard quantifies every syntactically consumed resource field. -/
theorem missing_resource_no_games (m : RawLaneModel) (k : Cell)
    (hk : k ∈ (HistoricalPackageRuntime.resources (model (protocol m))).readDependencies)
    (hm : image m.assignment k = none) :
    ¬ HistoricalPackageRuntime.PostWithdrawalFullAutonomy (model (protocol m)) m.assignment ∧
      ¬ HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy (model (protocol m)) m.assignment := by
  apply HistoricalPackageRuntime.missing_resource_no_games _ _ k hk
  rw [target_eq]
  exact hm

/-- The removed source never becomes post-withdrawal support. This negative
comes from resource safety at a genuine entry, not failure of a constructor. -/
theorem withdrawal_no_games (m : RawLaneModel) (empty : m.retained = []) :
    ¬ HistoricalPackageRuntime.PostWithdrawalFullAutonomy (model (protocol m)) m.assignment ∧
      ¬ HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy (model (protocol m)) m.assignment := by
  have no_resource (r : Registers Unit FrameValue) : ¬ ResourceRuntime.ResourceClosed
      (model (protocol m)).resourceSchema (HistoricalPackageRuntime.resources (model (protocol m)))
      (HistoricalPackageRuntime.target (model (protocol m)) m.assignment) r := by
    change ¬ ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema cfg)
      (resourceRaw (protocol m)) (PackageRuntime.target (POS04ResourceRuntime.model (protocol m)) m.assignment) r
    rintro ⟨ac,req,w,ha,hreq,hw,_,_,_,hsub,_⟩
    change some ([Resource.recharge] : List Resource) = some req at hreq
    have heq := Option.some.inj hreq
    subst req
    rw [POS04ResourceRuntime.target_eq] at hw
    change (image m.assignment .maintenance).map (fun _ => withdrawal (protocol m)) = some w at hw
    cases hv : image m.assignment .maintenance with
    | none => simp [hv] at hw
    | some v =>
      rw [hv] at hw
      have hwe := Option.some.inj hw
      subst w
      have impossible := hsub (by simp : Resource.recharge ∈ [Resource.recharge])
      simp [withdrawal,protocol,empty] at impossible
  constructor
  · rintro ⟨ha,hr,hw,⟨entry,he⟩,strategy,hs⟩
    exact no_resource entry (hs entry he entry [] StrategyGame.Play.initial).2.1
  · rintro ⟨ha,hr,hw,⟨entry,he⟩,strategy,hs⟩
    exact no_resource entry (hs entry he entry [] StrategyGame.Play.initial).2.1

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalRuntime





