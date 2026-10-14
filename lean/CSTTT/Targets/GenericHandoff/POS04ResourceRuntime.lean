import CSTTT.Targets.GenericHandoff.POS04DispatchedStage
import CSTTT.Targets.GenericHandoff.POS04RouteExecution
import CSTTT.Targets.GenericHandoff.RawFiniteAutonomy

/-! Concrete multi-resource POS-04 runtime, G6 specification §§3–5.
The six removed roles and the target recharge are distinct resource accounts.
Their identifiers use the existing G6 serialization; this introduces no prices
or dynamics. Withdrawal metadata are RAW protocol data, not autonomy verdicts.
Acquisition uses source rows, reception switches carrier, and the same execution
object then uses target rows. Resource and package instructions read the same
staged assignment. Missing primitive reads propagate through Option.

This is the runtime/factor seam, not an assembled RawHandoff or a claim of
arbitrary-partial F/O game equivalence. Full lineage and game equivalence remain
separate completion gates. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ResourceRuntime
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RouteExecution
abbrev StepEnv := POS04RegisterDynamics.StepEnv

inductive Resource where
  | removed (role : ResourceRuntime.Role)
  | recharge
  deriving DecidableEq

def resources : List Resource := ResourceRuntime.roles.map Resource.removed ++ [.recharge]

def roleImage : RemovedRole → ResourceRuntime.Role
  | .source => .source | .migrationBridge => .migrationBridge
  | .migrationController => .migrationController | .externalDecoder => .externalDecoder
  | .externalScheduler => .externalScheduler | .undeclaredRepair => .undeclaredRepair

/-- Only the three raw withdrawal fields; no assignment or derived set. -/
structure Protocol where
  retained : List RetainedResource
  removed : List RemovedRole
  sourcePresent : Bool

def protocol (m : RawLaneModel) : Protocol :=
  ⟨m.retained,m.removed,m.sourcePresentAfterWithdrawal⟩

def withdrawal (p : Protocol) : ResourceRuntime.Withdrawal Resource :=
  ⟨p.removed.map roleImage,fun role => [.removed role],
    p.removed.map (fun role => .removed (roleImage role)),
    p.retained.map (fun _ => .recharge)⟩

def resourceCode : Resource → ResourceId
  | .removed role => ⟨ResourceRuntime.roles.idxOf role⟩
  | .recharge => rechargeResourceCode

theorem resourceCode_injective : Function.Injective resourceCode := by
  intro x y h
  cases x with
  | recharge => cases y with
    | recharge => rfl
    | removed r => cases r <;> contradiction
  | removed r => cases y with
    | recharge => cases r <;> contradiction
    | removed s => cases r <;> cases s <;> first | rfl | contradiction

theorem removed_code_existing (r : RemovedRole) :
    resourceCode (.removed (roleImage r)) = removedResourceCode r := by
  cases r <;> decide

theorem recharge_code_existing : resourceCode .recharge = rechargeResourceCode := rfl

/-- Nominal maintenance requires the declared target recharge, not any of the
removed acquisition supports. Its balance follows the defined funded register.
No acquisition history appears as a post-withdrawal resource. -/
def accounts (p : Protocol) : E Unit (Resource → ResourceRuntime.Account) :=
  .map (fun (v : ResourceData × Ledger × Bool) => fun res => match res with
    | .removed _ => ⟨none,false,0⟩
    | .recharge => ⟨some (tagCarrierId v.1.owner),
        v.1.rechargeAvailable && p.retained.contains .targetRecharge,
        if v.2.2 then v.2.1.initialBudget else 0⟩)
    (.pair (.cell (Cell.resources .target)) (.pair (.cell Cell.maintenance)
      (.map (fun x : Frame => x.2.funded) (.register ()))))

def charge (p : Protocol) : E (LaneDisturbance × Action) (ResourceRuntime.Charge Resource) :=
  .map (fun (v : ResourceData × Ledger × Frame) =>
    ⟨tagCarrierId v.1.owner,(if v.2.2.1 = .target then [.recharge] else []),
      (fun res => match res with | .recharge => v.2.1.actionCost | _ => 0),
      (fun res => match res with
        | .recharge => if v.1.rechargeAvailable && p.retained.contains .targetRecharge
            then v.2.1.rechargePerAction else 0
        | _ => 0)⟩)
    (.pair (.cell (Cell.resources .target)) (.pair (.cell Cell.maintenance) (.register ())))

def advances : E StepEnv ResourceRuntime.Advances :=
  .map (fun (v : (KState → Action → Nat) × Frame × StepEnv) =>
    ⟨1,(match v.2.1.2.factor with | .inK s => v.1 s v.2.2.2.1 | _ => 0),1,1⟩)
    (.pair (.cell (Cell.ticks .target)) (.pair (.register ()) (.environment id)))

def bindings (p : Protocol) : ResourceRuntime.Bindings Cell Value Unit FrameValue
    LaneDisturbance Action Ambient KState Resource (List KState × List EventId) where
  accounts := accounts p
  required := .literal [.recharge]
  charge := charge p
  advances := advances
  factor := .map (fun x : Frame => match x.2.factor with | .inK s => some s | _ => none) (.register ())
  order := .map (fun x : Frame => x.2.counter) (.register ())
  ticks := .map (fun x : Frame => x.2.ticks) (.register ())
  progress := .map (fun x : Frame => x.2.counter) (.register ())
  record := lift (POS04RegisterDynamics.recordExpression .target)
  writer := lift (POS04RegisterDynamics.writerExpression .target)
  residue := .map (fun x : Frame => x.2.residue) (.register ())
  sourcePresent := .literal p.sourcePresent
  -- The ledger cell is required before interpreting the raw withdrawal rule;
  -- no missing ledger can be replaced by a default withdrawal view.
  withdrawal := ⟨.maintenance,fun _ => withdrawal p⟩

def resourceRaw (p : Protocol) : ResourceRuntime.Raw Cell Value Unit FrameValue
    LaneDisturbance Action Ambient KState Resource (List KState × List EventId) :=
  {bindings p with execution := acquisition.execution}

def cfg : RuntimeComponents.Schema KState Resource CSTTT.POS04.Stage EventId RouteId RouteId :=
  ⟨tagCarrierId .source,tagCarrierId .target,kernel,resources,stages,eventIds,
    routeIds,routeIds,.sourceLive,.targetExit,2,stages.idxOf⟩

/-- Source/target mode selection is a raw run coordinate. -/
def predictive : E Unit CSTTT.POS04.PredictiveNow :=
  .choose (.map (fun x : Frame => x.1 == Tag.target) (.register ()))
    (lift (POS04RegisterDynamics.predictiveExpression .target))
    (lift (POS04RegisterDynamics.predictiveExpression .source))

/-- These raw update recipes expose the declared counter increment and retained
register. They are not an accepted readout-law verdict. The enclosing temporal
gate still checks every recipe against the shared updater on the closure. -/
def recipes (p : Protocol) : RegisterFuture.StepRecipes Cell Value Unit FrameValue
    LaneDisturbance Action Ambient CSTTT.POS04.PredictiveNow
    (List KState × List EventId) (List ResourceRuntime.Account)
  | .predictive => .choose (.map (fun x : Frame => x.1 == Tag.target) (.register ()))
      (lift (POS04RegisterReadoutLaws.nextPredictive .target))
      (lift (POS04RegisterReadoutLaws.nextPredictive .source))
  | .order | .progress => .map (fun x : Frame => x.2.counter + 1) (.register ())
  | .ticks => .choose (.map (fun x : Frame => x.1 == Tag.target) (.register ()))
      (lift (POS04RegisterDynamics.program .target .ticks))
      (lift (POS04RegisterDynamics.program .source .ticks))
  | .writer => (bindings p).writer.reenv (fun _ => ())
  | .record => lift (POS04RegisterReadoutLaws.nextRecord .target)
  | .residue => (bindings p).residue.reenv (fun _ => ())
  | .maintenance => .map (fun v : ResourceData × Ledger × Bool =>
      resources.map fun res => match res with
      | .removed _ => ⟨none,false,0⟩
      | .recharge => ⟨some (tagCarrierId v.1.owner),
          v.1.rechargeAvailable && p.retained.contains .targetRecharge,
          if v.2.2 then v.2.1.initialBudget else 0⟩)
      (.pair (.cell (Cell.resources .target)) (.pair (.cell Cell.maintenance)
        (lift (POS04RegisterDynamics.program .target .funded))))
  | .owner => .map (fun r : ResourceData => tagCarrierId r.owner) (.cell (Cell.resources .target))

def runtime (p : Protocol) : RuntimeComponents.Raw Cell Value Unit FrameValue
    LaneDisturbance Action Ambient CSTTT.POS04.PredictiveNow KState Resource
    (List KState × List EventId) CSTTT.POS04.Stage EventId RouteId RouteId :=
  ⟨acquisition.execution,bindings p,acquisition.toBindings,predictive,recipes p⟩

/-- The declared POS-04 state views share the same primitives at every K state.
Only the target recharge availability is transformed by the raw retention rule.
All other cells are unchanged, including absent ones. -/
def runCells (p : Protocol) (k : Cell) : E Unit (Value k) :=
  match k with
  | .resources Tag.target => .map (fun (r : ResourceData) => (⟨r.owner,r.rechargeAvailable && p.retained.contains .targetRecharge⟩ : ResourceData)) (.cell (Cell.resources .target))
  | other => .cell other

def model (p : Protocol) := POS04DispatchedStage.bind cfg (runtime p) (runCells p)

theorem target_eq (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    PackageRuntime.target (model p) a = image a :=
  POS04DispatchedStage.target_eq_image _ _ _ a

theorem resources_eq (p : Protocol) : RuntimeComponents.resources (runtime p) = resourceRaw p := rfl
theorem acquisition_eq (p : Protocol) : RuntimeComponents.acquisition (runtime p) = acquisition := rfl

theorem run_assignment_eq (m : RawLaneModel) (r : Registers Unit FrameValue) :
    PackageRuntime.runAssignment (model (protocol m)) m.assignment r = withdrawnAssignment m := by
  funext k
  rw [show PackageRuntime.runAssignment (model (protocol m)) m.assignment r k =
    (runCells (protocol m) k).eval (image m.assignment) r () from by change (runCells (protocol m) k).eval (PackageRuntime.target (model (protocol m)) m.assignment) r () = _; rw [target_eq]]
  by_cases he : k = Cell.resources .target
  · subst k
    simp [runCells,Expr.eval,withdrawnAssignment,mapCell,protocol]
    rfl
  · have ho := mapCell_other_cell (image m.assignment) (.resources .target) k
      (fun v => {v with rechargeAvailable := v.rechargeAvailable && m.retained.contains .targetRecharge}) he
    rw [withdrawnAssignment,ho]
    cases k with
    | resources t =>
      cases t with
      | source => rfl
      | target => exact (he rfl).elim
    | _ => rfl

theorem package_readout_iff (m : RawLaneModel) :
    PackageRuntime.IntegratedTargetRealization (model (protocol m)) m.assignment ↔ PackageLane m.assignment :=
  POS04DispatchedStage.realization_iff _ _ _ _

theorem missing_resource_guard (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (k : Cell) (hk : k ∈ (resourceRaw p).readDependencies) (hm : image a k = none) :
    ¬ PackageRuntime.ResourceReady (model p) a := by
  change ¬ ResourceRuntime.Ready (resourceRaw p) (PackageRuntime.target (model p) a)
  rw [target_eq]
  exact ResourceRuntime.missing_read_rejected _ _ k hk hm

/-- Source-history execution is acquisition, not a target-owned maintenance
response. This prevents source-mode rows from entering the exact finite image
relation through a legal post-withdrawal action. -/
theorem legal_target_mode (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (r : Registers Unit FrameValue) (d : LaneDisturbance) (act : Action)
    (h : ResourceRuntime.Legal (RuntimeComponents.resourceSchema cfg) (resourceRaw p) a r d act) :
    (r ()).1 = .target := by
  rcases h with ⟨_,_,ac,needed,ch,w,_,_,hc,_,_,hn,_⟩
  change (charge p).eval a r (d,act) = some ch at hc
  cases he : a (.resources .target) with
  | none => simp [charge,Expr.eval,he] at hc
  | some data =>
    cases hl : a .maintenance with
    | none => simp [charge,Expr.eval,he,hl] at hc
    | some ledger =>
      simp only [charge,Expr.eval] at hc
      rw [he,hl] at hc
      have hch := Option.some.inj hc
      subst ch
      cases hm : (r ()).1 with
      | target => rfl
      | source => simp [hm] at hn

theorem source_mode_not_legal (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (x : Run6) (d : LaneDisturbance) (act : Action) :
    ¬ ResourceRuntime.Legal (RuntimeComponents.resourceSchema cfg) (resourceRaw p) a
      (frame .source x) d act := by
  intro h
  have hm := legal_target_mode p a _ d act h
  contradiction

end CSTTT.TargetTheory.GenericHandoff.POS04ResourceRuntime
