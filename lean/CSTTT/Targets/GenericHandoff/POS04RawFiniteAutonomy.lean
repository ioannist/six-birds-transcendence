import CSTTT.Targets.GenericHandoff.POS04ResourceRuntime

/-! Exact POS-04 lifting equations for RawFiniteAutonomy. Primitive programs
are compared as assignments, including missing values. Required resources and
actual account owners are compared on EVERY relevant run, with unbounded
counter, ledger-enabling and route-register contexts retained. No predictive
representative replaces an actual supported outcome.

The finite state views are the declared shared POS-04 primitives; this does not
assert that an arbitrary generic recipe factors. Full-game nonemptiness is constructed in POS04MultiResourceGames; exact
arbitrary-partial F/O equivalence remains a later runtime adapter obligation. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RawFiniteAutonomy
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RouteExecution POS04ResourceRuntime
set_option maxRecDepth 8192

abbrev FiniteExpr (Env X : Type) := Expr Cell Value Unit (fun _ => Unit) Env X

def finiteCells (p : Protocol) (k : Cell) : FiniteExpr KState (Value k) :=
  match k with
  | .resources Tag.target => .map (fun (r : ResourceData) =>
      (⟨r.owner,r.rechargeAvailable && p.retained.contains .targetRecharge⟩ : ResourceData))
      (.cell (Cell.resources .target))
  | other => .cell other

def factorFrame (p : Protocol) : RawFiniteAutonomy.Frame Cell Value Unit FrameValue
    KState LaneDisturbance Action Resource where
  states := ⟨kernel,fun s => by cases s <;> decide⟩
  disturbances := ⟨[.nominal],fun d => by cases d; decide⟩
  actions := ⟨actions,fun a => by cases a <;> decide⟩
  projection := .map (fun x : Frame => match x.2.factor with
    | .inK s => s | _ => .p0w0) (.register ())
  cells := finiteCells p
  maintenance := .literal [.recharge]
  actionOwner := .map (fun r : ResourceData => tagCarrierId r.owner) (.cell (Cell.resources .target))
  resourceOwner := .map (fun v : ResourceData × Resource => match v.2 with
    | .recharge => tagCarrierId v.1.owner | .removed _ => tagCarrierId .source)
    (.pair (.cell (Cell.resources .target)) (.environment id))
  resourceId := resourceCode

abbrev Checked (m : RawLaneModel) :=
  RawFiniteAutonomy.Checked (model (protocol m)) (factorFrame (protocol m)) m.assignment

theorem finite_cells_eq (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (x : KState) (r : Registers Unit FrameValue) (k : Cell) :
    (finiteCells p k).eval a (fun _ => ()) x = (runCells p k).eval a r () := by
  cases k with
  | resources t => cases t <;> rfl
  | _ => rfl

theorem primitive_lift (m : RawLaneModel) (h : Checked m) (r : Registers Unit FrameValue) :
    RawFiniteAutonomy.factorAssignment (model (protocol m)) (factorFrame (protocol m)) m.assignment
      (RawFiniteAutonomy.project _ _ _ h r) = PackageRuntime.runAssignment (model (protocol m)) m.assignment r := by
  funext k
  exact finite_cells_eq _ _ _ _ k

theorem required_eq (m : RawLaneModel) (h : Checked m) (x : KState) :
    RawFiniteAutonomy.required (model (protocol m)) (factorFrame (protocol m)) m.assignment h x = [.recharge] := by
  have he := RawFiniteAutonomy.readEnv_eq (factorFrame (protocol m)).maintenance
    (PackageRuntime.target (model (protocol m)) m.assignment) h.maintenance x
  exact (Option.some.inj he).symm

theorem resource_lift (m : RawLaneModel) (h : Checked m) (r : Registers Unit FrameValue) :
    (RuntimeComponents.resources (model (protocol m)).runtime).required.eval
      (PackageRuntime.target (model (protocol m)) m.assignment) r () =
      some (RawFiniteAutonomy.required _ _ _ h (RawFiniteAutonomy.project _ _ _ h r)) := by
  rw [required_eq]
  rfl

theorem withdrawal_eq (m : RawLaneModel) (h : Checked m) :
    RawFiniteAutonomy.withdrawalData (model (protocol m)) (factorFrame (protocol m)) m.assignment h =
      withdrawal (protocol m) := by
  have hl := h.ready.2.2 Cell.maintenance (by
    simp [model,POS04DispatchedStage.bind,RuntimeComponents.resources,
      runtime,bindings,ResourceRuntime.Raw.readDependencies])
  rw [target_eq] at hl
  have hp := POS04RegisterDynamics.cell_value hl
  have he := (RawFiniteAutonomy.withdrawal_fields _ _ _ h).1
  rw [target_eq] at he
  change (image m.assignment Cell.maintenance).map (fun _ => withdrawal (protocol m)) = _ at he
  rw [hp] at he
  exact (Option.some.inj he).symm

theorem retained_is_recharge (m : RawLaneModel) (h : Checked m) (res : Resource)
    (hr : res ∈ (RawFiniteAutonomy.withdrawalData (model (protocol m)) (factorFrame (protocol m)) m.assignment h).retained) :
    res = .recharge := by
  rw [withdrawal_eq] at hr
  obtain ⟨r,_,he⟩ := List.mem_map.mp hr
  exact he.symm

theorem owner_read (m : RawLaneModel) (h : Checked m) (res : Resource)
    (r : ResourceData) (he : image m.assignment (.resources .target) = some r) :
    RawFiniteAutonomy.readEnv (factorFrame (protocol m)).resourceOwner
      (PackageRuntime.target (model (protocol m)) m.assignment) h.resourceOwner res =
      match res with | .recharge => tagCarrierId r.owner | .removed _ => tagCarrierId .source := by
  have hx := RawFiniteAutonomy.readEnv_eq (factorFrame (protocol m)).resourceOwner
    (PackageRuntime.target (model (protocol m)) m.assignment) h.resourceOwner res
  conv at hx => lhs; rw [target_eq]
  simp only [factorFrame,Expr.eval] at hx
  rw [he] at hx
  exact (Option.some.inj hx).symm

theorem action_owner_read (m : RawLaneModel) (h : Checked m) (act : Action)
    (r : ResourceData) (he : image m.assignment (.resources .target) = some r) :
    RawFiniteAutonomy.readEnv (factorFrame (protocol m)).actionOwner
      (PackageRuntime.target (model (protocol m)) m.assignment) h.actionOwner act = tagCarrierId r.owner := by
  have hx := RawFiniteAutonomy.readEnv_eq (factorFrame (protocol m)).actionOwner
    (PackageRuntime.target (model (protocol m)) m.assignment) h.actionOwner act
  conv at hx => lhs; rw [target_eq]
  simp only [factorFrame,Expr.eval] at hx
  rw [he] at hx
  exact (Option.some.inj hx).symm

/-- Actual accounts use exactly the same owner cell as the finite owner
instruction, even before any assumption that the owner is the target. -/
theorem account_owner_lift (m : RawLaneModel) (h : Checked m)
    (run : Registers Unit FrameValue) (ac : Resource → ResourceRuntime.Account)
    (he : (RuntimeComponents.resources (model (protocol m)).runtime).accounts.eval
      (PackageRuntime.target (model (protocol m)) m.assignment) run () = some ac)
    (res : Resource) (hr : res ∈ (RawFiniteAutonomy.withdrawalData _ _ _ h).retained) :
    (ac res).owner = some (RawFiniteAutonomy.readEnv (factorFrame (protocol m)).resourceOwner
      (PackageRuntime.target (model (protocol m)) m.assignment) h.resourceOwner res) := by
  have hres := h.resourceOwner (.resources .target) (by simp [factorFrame,Expr.dependencies])
  rw [target_eq] at hres
  have hval := POS04RegisterDynamics.cell_value hres
  have hm := h.ready.2.2 Cell.maintenance (by
    simp [model,POS04DispatchedStage.bind,RuntimeComponents.resources,
      runtime,bindings,ResourceRuntime.Raw.readDependencies])
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
    RawFiniteAutonomy.Lift (model (protocol m)) (factorFrame (protocol m)) m.assignment h := by
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
    (hr : ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema (model (protocol m)).runtimeSchema)
      (RuntimeComponents.resources (model (protocol m)).runtime)
      (PackageRuntime.target (model (protocol m)) m.assignment) run) :
    ∃ rdata, image m.assignment (.resources .target) = some rdata ∧ rdata.owner = .target := by
  have hp := h.resourceOwner (.resources .target) (by simp [factorFrame,Expr.dependencies])
  rw [target_eq] at hp
  have hv := POS04RegisterDynamics.cell_value hp
  refine ⟨_,hv,?_⟩
  rcases hr with ⟨ac,req,w,ha,hreq,hw,_,_,_,hsub,hs,_⟩
  change some ([.recharge] : List Resource) = some req at hreq
  have heq := Option.some.inj hreq
  subst req
  have hret := hs .recharge (by simp)
  have hmem : Resource.recharge ∈ (RawFiniteAutonomy.withdrawalData _ _ _ h).retained := by
    have hew := Option.some.inj (hw.symm.trans (RawFiniteAutonomy.withdrawal_fields _ _ _ h).1)
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
    (ha : PackageRuntime.AcquisitionReady (model (protocol m)) m.assignment)
    (hg : PackageRuntime.FullGame (model (protocol m)) m.assignment ha h.ready) :
    RawFiniteAutonomy.Lift (model (protocol m)) (factorFrame (protocol m)) m.assignment h := by
  obtain ⟨entry,he⟩ := hg.2.1
  obtain ⟨_,_,strategy,hs⟩ := hg
  have safe := (hs entry he entry [] StrategyGame.Play.initial).2.1
  obtain ⟨rdata,hr,ho⟩ := ownership_of_resource_closed m h entry safe
  exact lift m h rdata hr ho

theorem game_each_entry_exact (m : RawLaneModel) (h : Checked m)
    (ha : PackageRuntime.AcquisitionReady (model (protocol m)) m.assignment)
    (hg : PackageRuntime.FullGame (model (protocol m)) m.assignment ha h.ready) :
    ∃ cert : PackageRuntime.FullCertificate (model (protocol m)) m.assignment ha h.ready,
      ∀ entry, PackageRuntime.Entries (model (protocol m)) m.assignment ha entry →
        Nonempty (CSTTT.AutonomyTheory.ExactAutonomyCertificate (GameAutonomyTransport.projectedData
          (RawFiniteAutonomy.factor (model (protocol m)) (factorFrame (protocol m)) m.assignment h)
          cert (RawFiniteAutonomy.project _ _ _ h) entry)) :=
  RawFiniteAutonomy.each_entry_exact _ _ _ h (lift_of_game m h ha hg) ha hg

theorem canonical_resource_ready : PackageRuntime.ResourceReady (model (protocol baseline)) canonical := by
  change ResourceRuntime.Ready (resourceRaw (protocol baseline)) (PackageRuntime.target (model (protocol baseline)) canonical)
  rw [target_eq,image_canonical]
  refine ⟨?_,?_,?_⟩
  · intro k _; rfl
  · exact (POS04RouteExecution.ready canonical (canonical_complete _)).2.2.2.1
  · intro k _; rfl

theorem canonical_withdrawal : PackageRuntime.Withdrawal (model (protocol baseline)) canonical := by
  change ResourceRuntime.DomainCheck (RuntimeComponents.resourceSchema cfg) (resourceRaw (protocol baseline)) ∧
    ResourceRuntime.WithdrawalCheck (RuntimeComponents.resourceSchema cfg) (resourceRaw (protocol baseline))
      (PackageRuntime.target (model (protocol baseline)) canonical)
  rw [target_eq,image_canonical]
  constructor
  · refine ⟨by decide,by decide,by decide,?_,?_,?_,?_,?_⟩
    · intro d; cases d; decide
    · intro a; cases a <;> decide
    · intro o; cases o with
      | inK s => cases s <;> decide
      | p2w0 => decide
      | p5w1 => decide
    · intro s; cases s <;> decide
    · intro res; cases res with
      | recharge => decide
      | removed role => cases role <;> decide
  · refine ⟨withdrawal (protocol baseline),rfl,?_,?_,?_,?_,?_,?_⟩
    · intro r hr; exact hr
    · intro r hr; exact hr
    · intro r hr; cases r <;> decide
    · intro res hr; cases res with
      | recharge => simp [withdrawal,protocol,baseline] at hr
      | removed r => cases r <;> decide
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
theorem positive_lift : RawFiniteAutonomy.Lift (model (protocol baseline))
    (factorFrame (protocol baseline)) canonical canonical_checked :=
  lift baseline canonical_checked (⟨.target,true⟩ : ResourceData) (by change image canonical _ = _; rw [image_canonical]; rfl) rfl

end CSTTT.TargetTheory.GenericHandoff.POS04RawFiniteAutonomy
