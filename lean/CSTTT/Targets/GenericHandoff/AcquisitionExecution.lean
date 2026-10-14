import CSTTT.Targets.GenericHandoff.ResourceRuntime
import CSTTT.Targets.GenericHandoff.RegisterInitialization
import CSTTT.Targets.GenericHandoff.StaticView

/-! Generic acquisition/phase-2 execution component (G6d design §§1.4–1.5).
Histories and routes are raw finite selectors for lists. Every run is computed
by initialization, supported history execution, raw receiver instructions,
and an actual positive-support post-exit step. No endpoint class, entry set,
activation verdict or run snapshot is a raw field. Source and arrival rows
are interpreted from the SAME execution object used by the resource game.
Missing acquisition inputs reject before helper rows can be read.

This is the entry interpreter seam. The enclosing stage/cover package,
G4/G1c adapters and POS-04 exact equivalence are separate remaining work.
-/
namespace CSTTT.TargetTheory.GenericHandoff.AcquisitionExecution
open RegisterInterpreter

structure Event (Stage : Type) where
  fromStage : Stage
  toStage : Stage
  sourceSupport : Bool
  targetSupport : Bool
  strictStep : Bool
  atomic : Bool
  orderAdvance : Nat

structure Receiver where
  sourcePresent : Bool
  targetFunded : Bool
  funded : Bool
  mixedRequired : Bool

structure Route (History Id : Type) where
  history : History
  path : List Id

structure Schema (Stage Id History RouteId : Type) where
  stages : List Stage
  eventIds : List Id
  histories : List History
  routes : List RouteId
  entryStage : Stage
  exitStage : Stage
  source : CarrierId
  target : CarrierId
  clock : Stage → Nat

structure Bindings (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O Stage Id History RouteId : Type) where
  initializer : RegisterInitialization.InitialProgram Cell Value R RV History
  histories : StaticView Cell Value (History → List (D × A × O))
  routes : CellView Cell Value (RouteId → Route History Id)
  events : CellView Cell Value (Id → Event Stage)
  realized : CellView Cell Value (List Stage)
  receiver : CellView Cell Value Receiver
  receive : Program Cell Value R RV (History × RouteId)
  arrivalResponse : Expr Cell Value R RV (History × RouteId) (D × A)

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O Stage Id History RouteId : Type)
    extends Bindings Cell Value R RV D A O Stage Id History RouteId where
  execution : ResourceRuntime.Execution Cell Value R RV D A O

variable {Cell R D A O Stage Id History RouteId : Type}
    {Value : Cell → Type} {RV : R → Type}

def Raw.dependencies (raw : Raw Cell Value R RV D A O Stage Id History RouteId) : List Cell :=
  raw.histories.dependencies ++
  [raw.routes.cell,raw.events.cell,raw.realized.cell,raw.receiver.cell] ++ raw.arrivalResponse.dependencies

def Ready (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  Complete raw.dependencies a ∧ RegisterInitialization.Ready raw.initializer a ∧
  Complete raw.execution.row.dependencies a ∧ ProgramReady raw.execution.program a ∧
  ProgramReady raw.receive a

noncomputable def initial (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (hist : History) : Registers R RV :=
  RegisterInitialization.initial raw.initializer a h.2.1 hist

noncomputable def update (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a)
    (r : Registers R RV) (d : D) (act : A) (o : O) : Registers R RV :=
  checkedExecute raw.execution.program a h.2.2.2.1 r (d,act,o)

noncomputable def receive (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a)
    (source : Registers R RV) (hist : History) (route : RouteId) : Registers R RV :=
  checkedExecute raw.receive a h.2.2.2.2 source (hist,route)

def rows (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (r : Registers R RV) (d : D) (act : A) :=
  (raw.execution.row.eval a r (d,act)).getD []

/-- Only raw instructions and their actual supported outcomes determine the
terminal state. Every action is admitted; no route-endpoint label is read. -/
inductive HistoryExecution (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) :
    Registers R RV → List (D × A × O) → Registers R RV → Prop where
  | nil (r : Registers R RV) : HistoryExecution raw a h r [] r
  | step {r final : Registers R RV} {d : D} {act : A} {o : O} {rest : List (D × A × O)}
      (disturbance : d ∈ raw.execution.disturbances)
      (action : act ∈ raw.execution.actions)
      (supported : StrategyGame.PositiveSupport (rows raw a) r d act o)
      (tail : HistoryExecution raw a h (update raw a h r d act o) rest final) :
      HistoryExecution raw a h r ((d,act,o)::rest) final

/-- Pure instruction fold. Checks are separate equations on this computed
execution; a caller cannot substitute a candidate terminal snapshot. -/
noncomputable def foldHistory (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) :
    Registers R RV → List (D × A × O) → Registers R RV
  | r, [] => r
  | r, (d,act,o)::rest => foldHistory raw a h (update raw a h r d act o) rest

theorem history_terminal_defined (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) {start final : Registers R RV}
    {word : List (D × A × O)} (he : HistoryExecution raw a h start word final) :
    final = foldHistory raw a h start word := by
  induction he with
  | nil => rfl
  | step _ _ _ _ ih => exact ih

/-- Check legal actions and the actual selected branch while
executing the word. These checks do not mention an intended endpoint. -/
noncomputable def HistoryCheck (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) :
    Registers R RV → List (D × A × O) → Prop
  | _, [] => True
  | r, (d,act,o)::rest => d ∈ raw.execution.disturbances ∧ act ∈ raw.execution.actions ∧
    StrategyGame.PositiveSupport (rows raw a) r d act o ∧
    HistoryCheck raw a h (update raw a h r d act o) rest

theorem history_check_executes (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (start : Registers R RV)
    (word : List (D × A × O)) (hc : HistoryCheck raw a h start word) :
    HistoryExecution raw a h start word (foldHistory raw a h start word) := by
  induction word generalizing start with
  | nil => exact HistoryExecution.nil _
  | cons step rest ih =>
    rcases step with ⟨d,act,o⟩
    exact HistoryExecution.step hc.1 hc.2.1 hc.2.2.1 (ih _ hc.2.2.2)

theorem history_execution_checked (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) {start final : Registers R RV}
    {word : List (D × A × O)} (he : HistoryExecution raw a h start word final) :
    HistoryCheck raw a h start word := by
  induction he with
  | nil => trivial
  | step hd ha hp _ ih => exact ⟨hd,ha,hp,ih⟩

variable [DecidableEq Stage]

/-- Path references, contiguity and realization are checked independently of
corridor acceptance. Entry execution does not manufacture strict lineage. -/
def PathCheck (cfg : Schema Stage Id History RouteId) (events : Id → Event Stage)
    (realized : List Stage) (path : List Id) : Prop :=
  ∃ first rest, path = first :: rest ∧
    (events first).fromStage = cfg.entryStage ∧
    (∀ id ∈ path, (events id).fromStage ∈ realized ∧ (events id).toStage ∈ realized ∧
      id ∈ cfg.eventIds ∧ (events id).fromStage ∈ cfg.stages ∧ (events id).toStage ∈ cfg.stages ∧
      (events id).atomic = true ∧ (events id).strictStep = true ∧ (events id).orderAdvance > 0 ∧
      cfg.clock (events id).toStage = cfg.clock (events id).fromStage + (events id).orderAdvance) ∧
    ((path.zip (path.drop 1)).all (fun pair =>
      decide ((events pair.1).toStage = (events pair.2).fromStage))) = true ∧
    ∃ last, path.getLast? = some last ∧ (events last).toStage = cfg.exitStage ∧
      (events last).sourceSupport = false ∧ (events last).targetSupport = true

def Mixed (events : Id → Event Stage) (realized : List Stage) (path : List Id) : Prop :=
  ∃ id ∈ path, (events id).fromStage ∈ realized ∧ (events id).toStage ∈ realized ∧
    (events id).sourceSupport = true ∧ (events id).targetSupport = true ∧ (events id).atomic = true

def Activated (input : Receiver) (events : Id → Event Stage)
    (realized : List Stage) (path : List Id) : Prop :=
  input.sourcePresent = true ∧ input.targetFunded = true ∧ input.funded = true ∧
    (input.mixedRequired = true → Mixed events realized path)

def DomainCheck (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId) : Prop :=
  cfg.routes ≠ [] ∧ cfg.histories ≠ [] ∧
  (∀ route, route ∈ cfg.routes) ∧ (∀ hist, hist ∈ cfg.histories) ∧
  (∀ id, id ∈ cfg.eventIds) ∧ (∀ stage, stage ∈ cfg.stages) ∧
  raw.execution.disturbances ≠ [] ∧ (∀ d, d ∈ raw.execution.disturbances)

/-- The acquired state is the receiver's raw instruction result, after a
supported source history. Activation and availability are checked here, not
borrowed from a sibling corridor check. -/
def Arrival (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : RouteId)
    (arrived : Registers R RV) : Prop :=
  ∃ histories routes events realized receiver,
    raw.histories.read a = some histories ∧ raw.routes.read a = some routes ∧
    raw.events.read a = some events ∧ raw.realized.read a = some realized ∧
    raw.receiver.read a = some receiver ∧ rid ∈ cfg.routes ∧
    (routes rid).history ∈ cfg.histories ∧ PathCheck cfg events realized (routes rid).path ∧ Activated receiver events realized (routes rid).path ∧
    ∃ source, HistoryExecution raw a h (initial raw a h (routes rid).history)
      (histories (routes rid).history) source ∧
      arrived = receive raw a h source (routes rid).history rid

/-- The receiver input and result are a fixed expression of the assigned
history and instructions. This excludes a supplied endpoint-class conclusion. -/
theorem arrival_terminal_defined (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : RouteId) (arrived : Registers R RV)
    (ha : Arrival cfg raw a h rid arrived) :
    ∃ histories routes, raw.histories.read a = some histories ∧ raw.routes.read a = some routes ∧
      arrived = receive raw a h
        (foldHistory raw a h (initial raw a h (routes rid).history) (histories (routes rid).history))
        (routes rid).history rid := by
  rcases ha with ⟨histories,routes,_,_,_,hh,hr,_,_,_,_,_,_,_,source,exec,he⟩
  exact ⟨histories,routes,hh,hr,he.trans (by rw [history_terminal_defined raw a h exec])⟩

/-- ALL positive-support arrival branches are entries, including a bad branch
if one exists. Autonomy must prove safety of each; entry formation cannot filter
an exit, resource failure or package failure out of the raw support. -/
def Entry (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (entry : Registers R RV) : Prop :=
  DomainCheck cfg raw ∧ ∃ rid arrived routes da outcome,
    Arrival cfg raw a h rid arrived ∧ raw.routes.read a = some routes ∧
    raw.arrivalResponse.eval a arrived ((routes rid).history,rid) = some da ∧
    da.1 ∈ raw.execution.disturbances ∧ da.2 ∈ raw.execution.actions ∧
    StrategyGame.Normalized (rows raw a) arrived da.1 da.2 ∧
    StrategyGame.PositiveSupport (rows raw a) arrived da.1 da.2 outcome ∧
    entry = update raw a h arrived da.1 da.2 outcome

omit [DecidableEq Stage] in
theorem missing_dependency_rejected (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.dependencies) (hm : a k = none) : ¬ Ready raw a := by
  intro h
  have hp := h.1 k hk
  rw [hm] at hp
  contradiction

omit [DecidableEq Stage] in
theorem missing_source_row_rejected (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.execution.row.dependencies) (hm : a k = none) : ¬ Ready raw a := by
  intro h
  have hp := h.2.2.1 k hk
  rw [hm] at hp
  contradiction

omit [DecidableEq Stage] in
theorem missing_initializer_rejected (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (r : R) (k : Cell) (hk : k ∈ (raw.initializer r).dependencies)
    (hm : a k = none) : ¬ Ready raw a :=
  fun h => RegisterInitialization.missing_rejected raw.initializer a r k hk hm h.2.1

omit [DecidableEq Stage] in
theorem missing_receiver_program_rejected (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (r : R) (k : Cell) (hk : k ∈ (raw.receive r).dependencies)
    (hm : a k = none) : ¬ Ready raw a :=
  fun h => missing_program_rejected raw.receive a r k hk hm h.2.2.2.2

omit [DecidableEq Stage] in
theorem missing_update_rejected (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (r : R) (k : Cell) (hk : k ∈ (raw.execution.program r).dependencies)
    (hm : a k = none) : ¬ Ready raw a :=
  fun h => missing_program_rejected raw.execution.program a r k hk hm h.2.2.2.1

/-- Applies to EACH consumed static view, not only the receiver input. -/
theorem missing_entry_view (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (entry : Registers R RV)
    (hm : raw.histories.read a = none ∨ raw.routes.read a = none ∨
      raw.events.read a = none ∨ raw.realized.read a = none ∨ raw.receiver.read a = none) :
    ¬ ∃ h : Ready raw a, Entry cfg raw a h entry := by
  rintro ⟨h,_,rid,arrived,routes,da,o,ha,_⟩
  rcases ha with ⟨histories,routes,events,realized,receiver,hh,hr,he,hs,hrec,_⟩
  rcases hm with hm | hm | hm | hm | hm <;> simp_all

theorem source_absent_no_entry (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (receiver : Receiver)
    (he : raw.receiver.read a = some receiver) (hs : receiver.sourcePresent = false)
    (entry : Registers R RV) : ¬ Entry cfg raw a h entry := by
  rintro ⟨_,rid,arrived,routes,da,o,ha,_⟩
  rcases ha with ⟨histories,routes,events,realized,rec,_,_,_,_,hr,_,_,_,hac,_⟩
  have heq : rec = receiver := Option.some.inj (hr.symm.trans he)
  subst rec
  simp [Activated,hs] at hac

inductive ActivationField where | source | targetFunding | receiverFunding
  deriving DecidableEq

def activationField (r : Receiver) : ActivationField → Bool
  | .source => r.sourcePresent
  | .targetFunding => r.targetFunded
  | .receiverFunding => r.funded

omit [DecidableEq Stage] in
theorem activated_fields (receiver : Receiver) (events : Id → Event Stage)
    (realized : List Stage) (path : List Id) (ha : Activated receiver events realized path)
    (field : ActivationField) : activationField receiver field = true := by
  cases field with
  | source => exact ha.1
  | targetFunding => exact ha.2.1
  | receiverFunding => exact ha.2.2.1

/-- Uniform gate for EACH availability input, at this lane itself. -/
theorem unavailable_receiver_field_no_arrival (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (receiver : Receiver)
    (he : raw.receiver.read a = some receiver) (field : ActivationField)
    (bad : activationField receiver field = false) (rid : RouteId) (arrived : Registers R RV) :
    ¬ Arrival cfg raw a h rid arrived := by
  rintro ⟨_,_,events,realized,rec,_,_,_,_,hr,_,_,_,ha,_⟩
  have heq := Option.some.inj (hr.symm.trans he)
  subst rec
  have hg := activated_fields receiver events realized _ ha field
  rw [bad] at hg
  contradiction

/-- Un-realizing any stage used by the declared route rejects THAT route's
arrival. No fixed baseline route readout or stage number is part of the gate. -/
theorem unrealized_path_no_arrival (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : RouteId)
    (routes : RouteId → Route History Id) (events : Id → Event Stage) (realized : List Stage)
    (hr : raw.routes.read a = some routes) (he : raw.events.read a = some events)
    (hs : raw.realized.read a = some realized)
    (id : Id) (hi : id ∈ (routes rid).path) (bad : (events id).toStage ∉ realized)
    (arrived : Registers R RV) : ¬ Arrival cfg raw a h rid arrived := by
  rintro ⟨_,rs,es,ss,_,_,hrs,hes,hss,_,_,_,hp,_⟩
  have hreq := Option.some.inj (hrs.symm.trans hr)
  have heeq := Option.some.inj (hes.symm.trans he)
  have hseq := Option.some.inj (hss.symm.trans hs)
  subst rs; subst es; subst ss
  rcases hp with ⟨_,_,_,_,hall,_⟩
  exact bad (hall id hi).2.1

/-- The path's independent raw increment equation DERIVES strictness. -/
theorem path_step_strict (cfg : Schema Stage Id History RouteId) (events : Id → Event Stage)
    (realized : List Stage) (path : List Id) (hp : PathCheck cfg events realized path)
    (id : Id) (hi : id ∈ path) : cfg.clock (events id).fromStage < cfg.clock (events id).toStage := by
  rcases hp with ⟨_,_,_,_,hall,_⟩
  have hg := hall id hi
  have positive := hg.2.2.2.2.2.2.2.1
  have law := hg.2.2.2.2.2.2.2.2
  omega

theorem capped_event_clock_rejected (cfg : Schema Stage Id History RouteId) (events : Id → Event Stage)
    (realized : List Stage) (path : List Id) (id : Id) (hi : id ∈ path)
    (bad : cfg.clock (events id).toStage ≤ cfg.clock (events id).fromStage) :
    ¬ PathCheck cfg events realized path := fun h => Nat.not_lt_of_ge bad (path_step_strict cfg events realized path h id hi)

theorem nonstrict_event_rejected (cfg : Schema Stage Id History RouteId) (events : Id → Event Stage)
    (realized : List Stage) (path : List Id) (id : Id) (hi : id ∈ path)
    (bad : (events id).strictStep = false) : ¬ PathCheck cfg events realized path := by
  rintro ⟨_,_,_,_,hall,_⟩
  have he := (hall id hi).2.2.2.2.2.2.1
  rw [bad] at he
  contradiction

/-- Retention is universal over ACTUAL support, never over a chosen class
representative or a filtered row. -/
theorem every_supported_branch_is_entry (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a)
    (domain : DomainCheck cfg raw) (rid : RouteId) (arrived : Registers R RV)
    (arrival : Arrival cfg raw a h rid arrived) (routes : RouteId → Route History Id)
    (hr : raw.routes.read a = some routes) (da : D × A)
    (hrsp : raw.arrivalResponse.eval a arrived ((routes rid).history,rid) = some da)
    (hd : da.1 ∈ raw.execution.disturbances) (ha : da.2 ∈ raw.execution.actions)
    (hn : StrategyGame.Normalized (rows raw a) arrived da.1 da.2)
    (outcome : O) (hp : StrategyGame.PositiveSupport (rows raw a) arrived da.1 da.2 outcome) :
    Entry cfg raw a h (update raw a h arrived da.1 da.2 outcome) :=
  ⟨domain,rid,arrived,routes,da,outcome,arrival,hr,hrsp,hd,ha,hn,hp,rfl⟩

theorem normalized_arrival_has_entry (cfg : Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a)
    (domain : DomainCheck cfg raw) (rid : RouteId) (arrived : Registers R RV)
    (arrival : Arrival cfg raw a h rid arrived) (routes : RouteId → Route History Id)
    (hr : raw.routes.read a = some routes) (da : D × A)
    (hrsp : raw.arrivalResponse.eval a arrived ((routes rid).history,rid) = some da)
    (hd : da.1 ∈ raw.execution.disturbances) (ha : da.2 ∈ raw.execution.actions)
    (hn : StrategyGame.Normalized (rows raw a) arrived da.1 da.2) :
    ∃ entry, Entry cfg raw a h entry := by
  obtain ⟨o,ho⟩ := hn.2.2
  exact ⟨_,every_supported_branch_is_entry cfg raw a h domain rid arrived arrival routes hr da hrsp hd ha hn o ho⟩

end CSTTT.TargetTheory.GenericHandoff.AcquisitionExecution
