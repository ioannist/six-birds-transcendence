import CSTTT.Targets.GenericHandoff.AcquisitionExecution
import CSTTT.Targets.GenericHandoff.RegisterReadoutLaws

/-! Raw component binding: one execution object, one assigned cell namespace.
The temporal, acquisition and resource projections below are DEFINED; no
candidate row/updater/observer/entry predicate is an argument. Arbitrary finite
factor, action, disturbance, event and route domains remain type parameters.
All unbounded run contexts remain expressible by RegisterInterpreter recipes.
This is not the finished RawHandoff: package rule aggregation and same-cell
G4/G1c projections, exact family adapters and final soundness remain gates.
-/
namespace CSTTT.TargetTheory.GenericHandoff.RuntimeComponents
open RegisterInterpreter

structure Schema (Factor Resource Stage Id History RouteId : Type) where
  source : CarrierId
  target : CarrierId
  factors : List Factor
  resources : List Resource
  stages : List Stage
  eventIds : List Id
  histories : List History
  routes : List RouteId
  entryStage : Stage
  exitStage : Stage
  tickPeriod : Nat
  clock : Stage → Nat

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O P Factor Resource Residue Stage Id History RouteId : Type) where
  execution : ResourceRuntime.Execution Cell Value R RV D A O
  resource : ResourceRuntime.Bindings Cell Value R RV D A O Factor Resource Residue
  acquisition : AcquisitionExecution.Bindings Cell Value R RV D A O Stage Id History RouteId
  predictive : Expr Cell Value R RV Unit P
  readoutRecipes : RegisterFuture.StepRecipes Cell Value R RV D A O P Residue
    (List ResourceRuntime.Account)

variable {Cell R D A O P Factor Resource Residue Stage Id History RouteId : Type}
    {Value : Cell → Type} {RV : R → Type}

/-- Distinct carrier identifiers are an enclosing handoff obligation, not a
prerequisite of a target's resource game or acquisition helper alone. -/
def CarrierCheck (cfg : Schema Factor Resource Stage Id History RouteId) : Prop :=
  cfg.source ≠ cfg.target

def resourceSchema (cfg : Schema Factor Resource Stage Id History RouteId) :
    ResourceRuntime.Schema Factor Resource := ⟨cfg.factors,cfg.resources,cfg.source,cfg.target⟩

def acquisitionSchema (cfg : Schema Factor Resource Stage Id History RouteId) :
    AcquisitionExecution.Schema Stage Id History RouteId :=
  ⟨cfg.stages,cfg.eventIds,cfg.histories,cfg.routes,cfg.entryStage,cfg.exitStage,cfg.source,cfg.target,cfg.clock⟩

def resources (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId) :
    ResourceRuntime.Raw Cell Value R RV D A O Factor Resource Residue :=
  {raw.resource with execution := raw.execution}

def acquisition (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId) :
    AcquisitionExecution.Raw Cell Value R RV D A O Stage Id History RouteId :=
  {raw.acquisition with execution := raw.execution}

/-- Maintenance exposes the actual declared accounts, not a supplied health
label. Ownership is read from the first required account. The pure helper's
fallback denotes an invalid account and cannot pass ResourceClosed. -/
def temporal (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId) :
    RegisterFuture.Raw Cell Value R RV D A O P Residue (List ResourceRuntime.Account) where
  outcomes := raw.execution.outcomes
  actions := raw.execution.actions
  disturbances := raw.execution.disturbances
  tickPeriod := cfg.tickPeriod
  row := raw.execution.row
  program := raw.execution.program
  readouts := {
    predictive := raw.predictive
    order := raw.resource.order
    ticks := raw.resource.ticks
    progress := raw.resource.progress
    writer := raw.resource.writer
    record := raw.resource.record
    residue := raw.resource.residue
    maintenance := .map (fun accounts => cfg.resources.map accounts) raw.resource.accounts
    owner := .map (fun p : (Resource → ResourceRuntime.Account) × List Resource =>
      match p.2 with
      | [] => cfg.source
      | res::_ => (p.1 res).owner.getD cfg.source)
      (.pair raw.resource.accounts raw.resource.required) }

/-- Entries are an interpreted relation, with ALL positive branches included.
No caller-provided set is exposed at this raw component boundary. -/
def Entries [DecidableEq Stage] (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (h : AcquisitionExecution.Ready (acquisition raw) a) :
    Registers R RV → Prop :=
  AcquisitionExecution.Entry (acquisitionSchema cfg) (acquisition raw) a h

theorem rows_shared (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (r : Registers R RV) (d : D) (act : A) :
    ResourceRuntime.rows (resources raw) a r d act =
      AcquisitionExecution.rows (acquisition raw) a r d act := rfl

theorem update_shared (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (hr : ResourceRuntime.Ready (resources raw) a)
    (ha : AcquisitionExecution.Ready (acquisition raw) a)
    (r : Registers R RV) (d : D) (act : A) (o : O) :
    ResourceRuntime.update (resources raw) a hr r d act o =
      AcquisitionExecution.update (acquisition raw) a ha r d act o := rfl

theorem temporal_rows_shared (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (ht : RegisterFuture.RawReady (temporal cfg raw) a)
    (r : Registers R RV) (d : D) (act : A) :
    RegisterFuture.row (temporal cfg raw) a ht r (d,act) =
      ResourceRuntime.rows (resources raw) a r d act := by
  unfold ResourceRuntime.rows
  change _ = (raw.execution.row.eval a r (d,act)).getD []
  have he := RegisterFuture.row_eq (temporal cfg raw) a ht r (d,act)
  change raw.execution.row.eval a r (d,act) = _ at he
  rw [he]
  rfl

theorem temporal_update_shared (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (ht : RegisterFuture.RawReady (temporal cfg raw) a)
    (hr : ResourceRuntime.Ready (resources raw) a)
    (r : Registers R RV) (d : D) (act : A) (o : O) :
    RegisterFuture.next (temporal cfg raw) a ht r (d,act) o =
      ResourceRuntime.update (resources raw) a hr r d act o := rfl

/-- Raw account ownership determines the temporal owner at EVERY safe run;
this is not merely a snapshot equation. -/
theorem resource_owner_link (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (r : Registers R RV)
    (h : ResourceRuntime.ResourceClosed (resourceSchema cfg) (resources raw) a r) :
    (temporal cfg raw).readouts.owner.eval a r () = some cfg.target := by
  rcases h with ⟨accounts,required,w,ha,hr,_,_,_,hn,_,hs,_⟩
  change raw.resource.accounts.eval a r () = some accounts at ha
  change raw.resource.required.eval a r () = some required at hr
  cases required with
  | nil => exact (hn rfl).elim
  | cons res rest =>
    have ho := (hs res (by simp)).1
    change (accounts res).owner = some cfg.target at ho
    simp [temporal,Expr.eval,ha,hr,ho]

/-- The auxiliary invariant uses DEFINED entries and the computed resource
semantics. It is not the generic TTH-06 result or its F package interpreter. -/
abbrev OperationalCertificate [DecidableEq Stage] (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (ha : AcquisitionExecution.Ready (acquisition raw) a)
    (hr : ResourceRuntime.Ready (resources raw) a) :=
  ResourceRuntime.Certificate (resourceSchema cfg) (resources raw) a hr (Entries cfg raw a ha)

def OperationalReadout [DecidableEq Stage] (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (ha : AcquisitionExecution.Ready (acquisition raw) a)
    (hr : ResourceRuntime.Ready (resources raw) a) : Prop :=
  ResourceRuntime.OperationalReadout (resourceSchema cfg) (resources raw) a hr (Entries cfg raw a ha)

theorem operational_soundness [DecidableEq Stage] (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (ha : AcquisitionExecution.Ready (acquisition raw) a)
    (hr : ResourceRuntime.Ready (resources raw) a)
    (cert : OperationalCertificate cfg raw a ha hr) : OperationalReadout cfg raw a ha hr :=
  ResourceRuntime.soundness _ _ _ _ _ cert

theorem source_absent_no_operational_readout [DecidableEq Stage]
    (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (a : Assignment Cell Value) (ha : AcquisitionExecution.Ready (acquisition raw) a)
    (hr : ResourceRuntime.Ready (resources raw) a)
    (receiver : AcquisitionExecution.Receiver)
    (he : (acquisition raw).receiver.read a = some receiver)
    (absent : receiver.sourcePresent = false) : ¬ OperationalReadout cfg raw a ha hr :=
  StrategyGame.no_entries_no_game (fun r =>
    AcquisitionExecution.source_absent_no_entry _ _ _ _ receiver he absent r)

end CSTTT.TargetTheory.GenericHandoff.RuntimeComponents
