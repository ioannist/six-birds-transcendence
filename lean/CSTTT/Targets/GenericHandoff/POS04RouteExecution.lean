import CSTTT.Targets.GenericHandoff.RunFrame
import CSTTT.Targets.GenericHandoff.POS04ExecutionFrontier
import CSTTT.Targets.GenericHandoff.RouteComponent

/-! POS-04 acquisition and executed-route specialization (G6 spec §§3–4).
One run frame records the actual carrier mode. Supported acquisition history
uses SOURCE rows; the receiver changes mode, and its funded response uses TARGET
rows and target tick updates. These equations hold for arbitrary partial
assignments, with each consumed primitive checked before interpretation.

The receive instruction copies raw coordinates, as declared; it does not read a
class or a desired endpoint. Its probe-local counter/ticks start at zero so the
actual response produces the G6 phase-2 counter one. The provenance probe is
the declared designed first-phase readout, not independent physical evidence.
This module defines the FULL `Indexed`/`Retained` route check, not merely
`ExecutedMemory`. Its enclosing named-lineage equivalence is separate work.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RouteExecution
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter RegisterInitialization
open POS04RegisterDynamics
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

abbrev Frame := Tag × Run6
abbrev FrameValue := RunFrame.Values Frame
abbrev E (Env X : Type) := Expr Cell Value Unit FrameValue Env X
def frame (t : Tag) (x : Run6) := RunFrame.pack (t,x)
def decode (x : Frame) := encode x.2
def lift {Env X : Type} (e : POS04RegisterDynamics.E Env X) : E Env X := RunFrame.embed decode e

def nextExpression (t : Tag) : E StepEnv Frame :=
  .map (fun p => (p.1,⟨p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2⟩))
    (.pair (.map Prod.fst (.register ()))
      (.pair (lift (program t .factor)) (.pair (lift (program t .counter))
        (.pair (lift (program t .ticks)) (.pair (lift (program t .residue))
          (lift (program t .funded)))))))

def updateProgram : Program Cell Value Unit FrameValue StepEnv := fun _ =>
  .choose (.map (fun x : Frame => x.1 == Tag.target) (.register ()))
    (nextExpression .target) (nextExpression .source)

def row : E (LaneDisturbance × Action) (List (Ambient × Rat)) :=
  .choose (.map (fun x : Frame => x.1 == Tag.target) (.register ()))
    (lift (POS04RegisterFuture.enabledRow .target))
    (lift (POS04RegisterFuture.enabledRow .source))

def initializer : InitialProgram Cell Value Unit FrameValue RouteId := fun _ =>
  .map (fun p => (Tag.source,⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩))
    (.pair (POS04ExecutionFrontier.initializer .factor)
      (.pair (POS04ExecutionFrontier.initializer .counter)
        (.pair (POS04ExecutionFrontier.initializer .ticks)
          (.pair (POS04ExecutionFrontier.initializer .residue)
            (POS04ExecutionFrontier.initializer .funded)))))

/-- Raw coordinate reception; no endpoint class participates. -/
def receiveProgram : Program Cell Value Unit FrameValue (RouteId × RouteId) := fun _ =>
  .map (fun (p : Receiver × Frame) =>
    match p.1.contentRule,p.1.registerRule with
    | .copyTerminalPositionPhase,.copyRawRouteTuple =>
      (Tag.target,⟨p.2.2.factor,0,0,p.2.2.residue,p.1.funded⟩))
    (.pair (.cell Cell.receiverInput) (.register ()))

def acquisition : AcquisitionExecution.Raw Cell Value Unit FrameValue
    LaneDisturbance Action Ambient CSTTT.POS04.Stage EventId RouteId RouteId where
  initializer := initializer
  histories := POS04ExecutionFrontier.wordExpr
  routes := POS04ExecutionFrontier.routeView
  events := POS04ExecutionFrontier.eventView
  realized := ⟨.realized,id⟩
  receiver := POS04ExecutionFrontier.receiverView
  receive := receiveProgram
  arrivalResponse := lift POS04ExecutionFrontier.acquisition.arrivalResponse
  execution := ⟨[.nominal],actions,ambientStates,row,updateProgram⟩

/-- Exactly the acquisition/route execution inputs; no interface declaration,
hazard, predictive-coordinate, or writer table is read by this component. -/
def dependencies : List Cell :=
  [.rows .source,.rows .target,.ticks .source,.ticks .target,.resources .source,.resources .target,
   .maintenance,.policy,.histories,.routeTable,.receiverInput,.eventTable,.realized]

theorem ready (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    AcquisitionExecution.Ready acquisition a := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k hk
    apply hc k
    simp only [acquisition,
      AcquisitionExecution.Raw.dependencies,
      POS04ExecutionFrontier.wordExpr,
      POS04ExecutionFrontier.pathExpr,
      POS04ExecutionFrontier.routeView,
      POS04ExecutionFrontier.eventView,
      POS04ExecutionFrontier.receiverView,
      POS04ExecutionFrontier.acquisition,
      StaticView.dependencies,
      row,
      POS04RegisterFuture.enabledRow,
      rowExpression,
      Expr.dependencies,
      lift,
      RunFrame.dependencies,
      dependencies,
      List.mem_append,
      List.mem_cons,
      List.not_mem_nil,
      or_false] at hk ⊢
    grind
  · intro r k hk
    apply hc k
    simp only [acquisition,
      POS04ExecutionFrontier.wordExpr,
      POS04ExecutionFrontier.pathExpr,
      POS04ExecutionFrontier.routeView,
      POS04ExecutionFrontier.eventView,
      POS04ExecutionFrontier.receiverView,
      POS04ExecutionFrontier.acquisition,
      initializer,
      POS04ExecutionFrontier.initializer,
      POS04ExecutionFrontier.residueExpr,
      row,
      POS04RegisterFuture.enabledRow,
      rowExpression,
      Expr.dependencies,
      Expr.reenv_dependencies,
      lift,
      dependencies,
      List.mem_append,
      List.mem_cons,
      List.not_mem_nil,
      or_false] at hk ⊢
    grind
  · intro k hk
    apply hc k
    simp only [acquisition,
      POS04ExecutionFrontier.wordExpr,
      POS04ExecutionFrontier.pathExpr,
      POS04ExecutionFrontier.routeView,
      POS04ExecutionFrontier.eventView,
      POS04ExecutionFrontier.receiverView,
      POS04ExecutionFrontier.acquisition,
      row,
      POS04RegisterFuture.enabledRow,
      rowExpression,
      Expr.dependencies,
      lift,
      RunFrame.dependencies,
      dependencies,
      List.mem_append,
      List.mem_cons,
      List.not_mem_nil,
      or_false] at hk ⊢
    grind
  · intro r k hk
    apply hc k
    simp only [acquisition,
      POS04ExecutionFrontier.wordExpr,
      POS04ExecutionFrontier.pathExpr,
      POS04ExecutionFrontier.routeView,
      POS04ExecutionFrontier.eventView,
      POS04ExecutionFrontier.receiverView,
      POS04ExecutionFrontier.acquisition,
      row,
      POS04RegisterFuture.enabledRow,
      rowExpression,
      updateProgram,
      nextExpression,
      program,
      Expr.dependencies,
      lift,
      RunFrame.dependencies,
      dependencies,
      List.mem_append,
      List.mem_cons,
      List.not_mem_nil,
      or_false] at hk ⊢
    grind
  · intro r k hk
    apply hc k
    simp only [acquisition,
      POS04ExecutionFrontier.wordExpr,
      POS04ExecutionFrontier.pathExpr,
      POS04ExecutionFrontier.routeView,
      POS04ExecutionFrontier.eventView,
      POS04ExecutionFrontier.receiverView,
      POS04ExecutionFrontier.acquisition,
      row,
      POS04RegisterFuture.enabledRow,
      rowExpression,
      receiveProgram,
      Expr.dependencies,
      lift,
      dependencies,
      List.mem_append,
      List.mem_cons,
      List.not_mem_nil,
      or_false] at hk ⊢
    grind

theorem next_eval (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (mode t : Tag) (x : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    (nextExpression t).eval a (frame mode x) (d,act,o) =
      some (mode,actualUpdate6 (runInputs6 a t) x act o) := by
  have hcore : Complete (coreDependencies t) a := by
    intro k hk
    apply hc k
    cases t <;> simp_all [coreDependencies,dependencies] <;> grind
  have hp := program_actual a t hcore x d act o
  simp only [nextExpression,Expr.eval,lift,RunFrame.evaluation,frame,RunFrame.pack,decode]
  have hfactor := congrFun hp Register.factor
  have hcounter := congrFun hp Register.counter
  have hticks := congrFun hp Register.ticks
  have hresidue := congrFun hp Register.residue
  have hfunded := congrFun hp Register.funded
  simp only [execute] at hfactor hcounter hticks hresidue hfunded
  rw [hfactor,hcounter,hticks,hresidue,hfunded]
  rfl

theorem update_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (t : Tag) (x : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    AcquisitionExecution.update acquisition a (ready a hc) (frame t x) d act o =
      frame t (actualUpdate6 (runInputs6 a t) x act o) := by
  funext r
  apply Option.some.inj
  unfold AcquisitionExecution.update
  rw [← checked_execute_eq]
  change (updateProgram r).eval a (frame t x) (d,act,o) = _
  have hs := next_eval a hc t .source x d act o
  have ht := next_eval a hc t .target x d act o
  simp only [updateProgram,Expr.eval]
  rw [ht,hs]
  cases t <;> rfl

theorem rows_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (t : Tag) (x : Run6) (d : LaneDisturbance) (act : Action) :
    AcquisitionExecution.rows acquisition a (frame t x) d act = actualRows6 (runInputs6 a t) x act := by
  have hs := row_eval a .source (hc (.rows .source) (by simp [dependencies])) x d act
  have ht := row_eval a .target (hc (.rows .target) (by simp [dependencies])) x d act
  have hrs := cell_value (hc (.resources .source) (by simp [dependencies]))
  have hrt := cell_value (hc (.resources .target) (by simp [dependencies]))
  have hl := cell_value (hc .maintenance (by simp [dependencies]))
  simp only [AcquisitionExecution.rows,acquisition,row,Expr.eval,lift,RunFrame.evaluation,
    frame,RunFrame.pack,decode,POS04RegisterFuture.enabledRow]
  rw [hs,ht]
  simp only [encode]
  rw [hrs,hrt,hl]
  cases t <;> rfl

theorem receive_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (t : Tag) (x : Run6) (hist r : RouteId) :
    AcquisitionExecution.receive acquisition a (ready a hc) (frame t x) hist r =
      frame .target ⟨x.factor,0,0,x.residue,((a .receiverInput).getD (canonicalValue .receiverInput)).funded⟩ := by
  funext k
  apply Option.some.inj
  unfold AcquisitionExecution.receive
  rw [← checked_execute_eq]
  change (receiveProgram k).eval a (frame t x) (hist,r) = _
  simp only [receiveProgram,Expr.eval]
  rw [cell_value (hc .receiverInput (by simp [dependencies]))]
  rfl

theorem initial_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (r : RouteId) :
    AcquisitionExecution.initial acquisition a (ready a hc) r =
      frame .source (acquisitionInitialRun a .source r) := by
  have hh := cell_value (hc .histories (by simp [dependencies]))
  have hr := cell_value (hc .routeTable (by simp [dependencies]))
  have hm := cell_value (hc .receiverInput (by simp [dependencies]))
  funext k
  apply Option.some.inj
  unfold AcquisitionExecution.initial
  rw [← RegisterInitialization.initial_eq]
  simp only [RegisterInitialization.evaluate,acquisition,initializer,Expr.eval,
    POS04ExecutionFrontier.initializer,POS04ExecutionFrontier.pathExpr,
    POS04ExecutionFrontier.residueExpr,Expr.reenv_eval]
  rw [hh,hr,hm]
  change some (Tag.source,⟨_,0,0,_,_⟩) = some (Tag.source,acquisitionInitialRun a .source r)
  unfold acquisitionInitialRun
  simp only [routeTuple,POS04ExecutionFrontier.source_routes,
    POS04ExecutionFrontier.source_histories]
  rw [POS04ExecutionFrontier.source_path]
  rfl

def actualFold (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    Run6 → List StepEnv → Run6
  | x, [] => x
  | x, (_,act,o)::rest => actualFold a t (actualUpdate6 (runInputs6 a t) x act o) rest

theorem fold_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (t : Tag) (x : Run6) (word : List StepEnv) :
    AcquisitionExecution.foldHistory acquisition a (ready a hc) (frame t x) word =
      frame t (actualFold a t x word) := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [AcquisitionExecution.foldHistory,actualFold,update_eq a hc,ih]

theorem fold_preserves_register (a : CSTTT.POS04.Assigned.Assignment)
    (t : Tag) (x : Run6) (word : List StepEnv) :
    (actualFold a t x word).residue = x.residue := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    exact ih (actualUpdate6 (runInputs6 a t) x act o)

theorem frame_eta (x : Registers Unit FrameValue) : RunFrame.pack (x ()) = x := by
  funext k; cases k; rfl

/-- Actual source execution followed by the declared receiver. This is an
equation for every arrival, not a supplied snapshot or a baseline endpoint. -/
theorem arrival_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (r : RouteId) (arrived : Registers Unit FrameValue)
    (ha : AcquisitionExecution.Arrival POS04ExecutionFrontier.schema acquisition a (ready a hc) r arrived) :
    ∃ histories routes,
      acquisition.histories.read a = some histories ∧ acquisition.routes.read a = some routes ∧
      let x := actualFold a .source (acquisitionInitialRun a .source (routes r).history)
        (histories (routes r).history)
      arrived = frame .target ⟨x.factor,0,0,x.residue,
        ((a .receiverInput).getD (canonicalValue .receiverInput)).funded⟩ := by
  obtain ⟨histories,routes,hh,hr,he⟩ := AcquisitionExecution.arrival_terminal_defined
    POS04ExecutionFrontier.schema acquisition a (ready a hc) r arrived ha
  refine ⟨histories,routes,hh,hr,?_⟩
  rw [he,initial_eq a hc,fold_eq a hc,receive_eq a hc]

/-- The declared raw path tuple is the provenance; route IDs only select it. -/
def provenance : StaticView Cell Value
    (RouteId → List (LaneDisturbance × Action × Ambient) → List EventId → List KState × List EventId) :=
  ⟨.map (fun (p : (HistoryId → List KState) × List Route) => fun r _word path =>
    (POS04ExecutionFrontier.historyPath p.1 p.2 r,path))
    (.pair (.cell Cell.histories) (.cell Cell.routeTable))⟩

def routeRaw : RouteComponent.Raw Cell Value Unit FrameValue LaneDisturbance Action Ambient
    CSTTT.POS04.Stage EventId RouteId RouteId (List KState × List EventId) (Tag × Ambient) where
  acquisition := acquisition
  provenance := provenance
  register := .map (fun x : Frame => x.2.residue) (.register ())
  readout := .map (fun (p : RouteReadout × Frame) => match p.1 with
    | .firstSourcePhaseAfterFundedStep => p.2.2.residue.1.head?.map (fun s => ambientPhase (.inK s)))
    (.pair (.literal routeReadout) (.register ()))
  owner := .map (fun r : ResourceData => tagCarrierId r.owner) (.cell (Cell.resources .target))
  endpoint := .map (fun x : Frame => (x.1,x.2.factor)) (.register ())

/-- All actual branches after reception use the target's rows and update,
even when the partial assignment's two transition tables differ. -/
theorem result_target_step (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (r : RouteId) (entry : Registers Unit FrameValue)
    (he : RouteComponent.Result POS04ExecutionFrontier.schema routeRaw a (ready a hc) r entry) :
    ∃ (x : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient),
      StrategyGame.PositiveSupport (fun y (_ : LaneDisturbance) action => actualRows6 (runInputs6 a .target) y action)
        x d act o ∧ entry = frame .target (actualUpdate6 (runInputs6 a .target) x act o) := by
  obtain ⟨arrived,d,act,o,ha,hp,hu⟩ := RouteComponent.result_actual_update _ routeRaw a (ready a hc) r entry he
  obtain ⟨_,_,_,_,hx⟩ := arrival_eq a hc r arrived ha
  dsimp only at hx
  subst arrived
  unfold StrategyGame.PositiveSupport at hp
  change (∃ p, (o,p) ∈ AcquisitionExecution.rows acquisition a (frame .target _) d act ∧ 0 < p) at hp
  rw [rows_eq a hc] at hp
  exact ⟨_,d,act,o,hp,hu.trans (update_eq a hc .target _ d act o)⟩

/-- Full comparison: actual distinct paths, shared endpoint, and retention on
EVERY branch. It is never replaced by the weaker `ExecutedMemory` readout. -/
def RoutePass (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  RouteComponent.Pass POS04ExecutionFrontier.schema routeRaw a

theorem ready_route (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    RouteComponent.Ready routeRaw a := by
  refine ⟨ready a hc,?_⟩
  intro k hk
  simp [RouteComponent.scope,routeRaw,provenance,StaticView.dependencies,Expr.dependencies] at hk
  rcases hk with hk | hk | hk <;> subst k
  · exact hc _ (by simp [dependencies])
  · exact hc _ (by simp [dependencies])
  · exact hc _ (by simp [dependencies])

/-- Exact decoder domain, for arbitrary PARTIAL assignments. None of the
unconsumed C6 interface/hazard/writer fields is silently filled to prove this. -/
theorem ready_route_iff (a : CSTTT.POS04.Assigned.Assignment) :
    RouteComponent.Ready routeRaw a ↔ Complete dependencies a := by
  constructor
  · intro h k hk
    simp only [dependencies,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals subst k
    all_goals solve
      | (apply h.1.1; simp [routeRaw,acquisition,AcquisitionExecution.Raw.dependencies,
          POS04ExecutionFrontier.wordExpr,POS04ExecutionFrontier.pathExpr,
          POS04ExecutionFrontier.routeView,POS04ExecutionFrontier.eventView,
          POS04ExecutionFrontier.receiverView,POS04ExecutionFrontier.acquisition,
          StaticView.dependencies,Expr.dependencies,lift,RunFrame.dependencies])
      | (apply h.1.2.2.1; simp [routeRaw,acquisition,row,POS04RegisterFuture.enabledRow,
          rowExpression,Expr.dependencies,lift,RunFrame.dependencies])
      | (apply h.1.2.2.2.1 (); simp [routeRaw,acquisition,updateProgram,nextExpression,
          program,Expr.dependencies,lift,RunFrame.dependencies])
  · exact ready_route a

theorem result_uses_actual_support (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (r : RouteId) (entry : Registers Unit FrameValue)
    (he : RouteComponent.Result POS04ExecutionFrontier.schema routeRaw a (ready a hc) r entry) :
    ∃ arrived d act o,
      AcquisitionExecution.Arrival POS04ExecutionFrontier.schema acquisition a (ready a hc) r arrived ∧
      StrategyGame.PositiveSupport (AcquisitionExecution.rows acquisition a) arrived d act o ∧
      entry = AcquisitionExecution.update acquisition a (ready a hc) arrived d act o :=
  RouteComponent.result_actual_update _ routeRaw a (ready a hc) r entry he

theorem status_preserves_full_comparison (a : CSTTT.POS04.Assigned.Assignment) :
    RouteComponent.statusOf POS04ExecutionFrontier.schema routeRaw a = .routeIndexed ↔ RoutePass a :=
  RouteComponent.status_indexed_iff _ routeRaw a

theorem missing_atomic_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ RoutePass (put a .eventTable none) := by
  apply RouteComponent.missing_acquisition_rejected _ routeRaw _ .eventTable
  · simp [routeRaw,acquisition,AcquisitionExecution.Raw.dependencies,POS04ExecutionFrontier.eventView]
  · simp

theorem missing_source_rows_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ RoutePass (put a (.rows .source) none) := by
  rintro ⟨h,_⟩
  apply AcquisitionExecution.missing_source_row_rejected acquisition _ (.rows .source) _ (put_same _ _ _) h.1
  simp [acquisition,row,Expr.dependencies,lift,RunFrame.dependencies,POS04RegisterFuture.enabledRow,rowExpression]

theorem missing_target_rows_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ RoutePass (put a (.rows .target) none) := by
  rintro ⟨h,_⟩
  apply AcquisitionExecution.missing_source_row_rejected acquisition _ (.rows .target) _ (put_same _ _ _) h.1
  simp [acquisition,row,Expr.dependencies,lift,RunFrame.dependencies,POS04RegisterFuture.enabledRow,rowExpression]

def wordFor (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId) : List StepEnv :=
  let path := acquisitionHistory a .source r
  (path.zip (path.drop 1)).map (fun e => (.nominal,(runInputs6 a .source).base.base.policy e.1,.inK e.2))

theorem words_read (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    acquisition.histories.read a = some (wordFor a) := by
  simp only [acquisition,POS04ExecutionFrontier.wordExpr,POS04ExecutionFrontier.pathExpr,
    StaticView.read,Expr.eval]
  rw [cell_value (hc .histories (by simp [dependencies])),
    cell_value (hc .routeTable (by simp [dependencies])),
    cell_value (hc .policy (by simp [dependencies]))]
  apply congrArg some
  funext r
  dsimp only [wordFor]
  rw [POS04ExecutionFrontier.source_path,POS04ExecutionFrontier.source_policy]

def pathsFor (a : CSTTT.POS04.Assigned.Assignment) :
    RouteId → AcquisitionExecution.Route RouteId EventId :=
  fun r => ⟨r,((((a .routeTable).getD (canonicalValue .routeTable)).find?
    (fun v => v.id == r)).map Route.eventPath).getD []⟩

def eventsFor (a : CSTTT.POS04.Assigned.Assignment) : EventId → AcquisitionExecution.Event CSTTT.POS04.Stage :=
  fun id => match ((a .eventTable).getD (canonicalValue .eventTable)).find? (fun e => e.id == id) with
    | none => ⟨.sourceLive,.sourceLive,false,false,false,false,0⟩
    | some e => ⟨e.fromStage,e.toStage,e.sourceSupport,e.targetSupport,e.strictStep,e.atomic,
        stages.idxOf e.toStage - stages.idxOf e.fromStage⟩

def receiverFor (a : CSTTT.POS04.Assigned.Assignment) : AcquisitionExecution.Receiver :=
  let r := (a .receiverInput).getD (canonicalValue .receiverInput)
  ⟨r.sourcePresent,r.targetReceiverFunded,r.funded,r.mixedEventRequired⟩

theorem routes_read (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    acquisition.routes.read a = some (pathsFor a) := by
  simp only [acquisition,POS04ExecutionFrontier.routeView,CellView.read]
  rw [cell_value (hc .routeTable (by simp [dependencies]))]
  rfl

theorem events_read (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    acquisition.events.read a = some (eventsFor a) := by
  simp only [acquisition,POS04ExecutionFrontier.eventView,CellView.read]
  rw [cell_value (hc .eventTable (by simp [dependencies]))]
  rfl

theorem realized_read (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    acquisition.realized.read a = some ((a .realized).getD (canonicalValue .realized)) := by
  simp only [acquisition,CellView.read]
  rw [cell_value (hc .realized (by simp [dependencies]))]
  rfl

theorem receiver_read (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    acquisition.receiver.read a = some (receiverFor a) := by
  simp only [acquisition,POS04ExecutionFrontier.receiverView,CellView.read]
  rw [cell_value (hc .receiverInput (by simp [dependencies]))]
  rfl

theorem canonical_routes_read : acquisition.routes.read canonical =
    some (fun r => ⟨r,[.mix1,.mix2,.exit]⟩) := by
  apply congrArg some
  funext r
  cases r <;> rfl

def supportedWord (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) : Run6 → List StepEnv → Bool
  | _, [] => true
  | x, (d,act,o)::rest => decide (d ∈ acquisition.execution.disturbances ∧ act ∈ acquisition.execution.actions) &&
    (actualRows6 (runInputs6 a t) x act).any (fun e => decide (e.1 = o ∧ 0 < e.2)) &&
    supportedWord a t (actualUpdate6 (runInputs6 a t) x act o) rest

theorem supported_word_iff (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (t : Tag) (x : Run6) (word : List StepEnv) :
    AcquisitionExecution.HistoryCheck acquisition a (ready a hc) (frame t x) word ↔
      supportedWord a t x word = true := by
  induction word generalizing x with
  | nil => simp [AcquisitionExecution.HistoryCheck,supportedWord]
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [AcquisitionExecution.HistoryCheck,supportedWord,Bool.and_eq_true,decide_eq_true_eq]
    rw [update_eq a hc,ih]
    unfold StrategyGame.PositiveSupport
    rw [rows_eq a hc,POS04ExecutionFrontier.support_any]
    simp only [and_assoc]

def arrivalRun (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId) : Run6 :=
  let x := actualFold a .source (acquisitionInitialRun a .source r) (wordFor a r)
  ⟨x.factor,0,0,x.residue,((a .receiverInput).getD (canonicalValue .receiverInput)).funded⟩

/-- Independent semantic arrival: raw realized path, activation, actual
supported history, and its coordinate receiver result. No C6 interface-list
declaration or unrelated package bookkeeping is added to this readout. -/
def ArrivalReadout (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId)
    (arrived : Registers Unit FrameValue) : Prop :=
  r ∈ routeIds ∧
  AcquisitionExecution.PathCheck POS04ExecutionFrontier.schema (eventsFor a)
    ((a .realized).getD (canonicalValue .realized)) (pathsFor a r).path ∧
  AcquisitionExecution.Activated (receiverFor a) (eventsFor a)
    ((a .realized).getD (canonicalValue .realized)) (pathsFor a r).path ∧
  supportedWord a .source (acquisitionInitialRun a .source r) (wordFor a r) = true ∧
  arrived = frame .target (arrivalRun a r)

theorem arrival_readout_iff (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (r : RouteId) (arrived : Registers Unit FrameValue) :
    AcquisitionExecution.Arrival POS04ExecutionFrontier.schema acquisition a (ready a hc) r arrived ↔
      ArrivalReadout a r arrived := by
  constructor
  · intro ha
    obtain ⟨histories,routes,events,realized,input,hh,hr,he,hs,hi,hd,_hhist,hpath,hactive,
      source,hsource,hreceive⟩ := ha
    have eqhist := Option.some.inj (hh.symm.trans (words_read a hc))
    have eqroutes := Option.some.inj (hr.symm.trans (routes_read a hc))
    have eqevents := Option.some.inj (he.symm.trans (events_read a hc))
    have eqrealized := Option.some.inj (hs.symm.trans (realized_read a hc))
    have eqinput := Option.some.inj (hi.symm.trans (receiver_read a hc))
    subst histories; subst routes; subst events; subst realized; subst input
    have hcheck := AcquisitionExecution.history_execution_checked acquisition a (ready a hc) hsource
    have hterminal := AcquisitionExecution.history_terminal_defined acquisition a (ready a hc) hsource
    simp only [pathsFor] at hcheck hterminal hreceive
    rw [initial_eq a hc,supported_word_iff a hc] at hcheck
    refine ⟨hd,hpath,hactive,hcheck,?_⟩
    rw [hreceive,hterminal,initial_eq a hc,fold_eq a hc,receive_eq a hc]
    rfl
  · rintro ⟨hd,hpath,hactive,hword,harrived⟩
    refine ⟨wordFor a,pathsFor a,eventsFor a,(a .realized).getD (canonicalValue .realized),receiverFor a,
      words_read a hc,routes_read a hc,events_read a hc,realized_read a hc,receiver_read a hc,
      hd,hd,hpath,hactive,?_,?_,?_⟩
    · exact AcquisitionExecution.foldHistory acquisition a (ready a hc)
        (AcquisitionExecution.initial acquisition a (ready a hc) r) (wordFor a r)
    · apply AcquisitionExecution.history_check_executes
      rw [initial_eq a hc,supported_word_iff a hc]
      exact hword
    · rw [initial_eq a hc,fold_eq a hc,receive_eq a hc]
      exact harrived

def responseAction (a : CSTTT.POS04.Assigned.Assignment) (x : Run6) : Action :=
  ((a .policy).getD (canonicalValue .policy))
    (match x.factor with | .inK s => s | _ => .p0w0)

theorem response_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (t : Tag) (x : Run6) (hist r : RouteId) :
    acquisition.arrivalResponse.eval a (frame t x) (hist,r) = some (.nominal,responseAction a x) := by
  simp only [acquisition,lift,RunFrame.evaluation,frame,decode,POS04ExecutionFrontier.acquisition,Expr.eval,encode]
  rw [cell_value (hc .policy (by simp [dependencies]))]
  rfl

/-- Independent all-support phase-2 semantics, executing the target row on
the raw reception result. The endpoint is not reset after the response. -/
def ResultReadout (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId)
    (entry : Registers Unit FrameValue) : Prop :=
  ArrivalReadout a r (frame .target (arrivalRun a r)) ∧
  let x := arrivalRun a r
  let act := responseAction a x
  StrategyGame.Normalized (fun y (_ : LaneDisturbance) action => actualRows6 (runInputs6 a .target) y action)
    x .nominal act ∧
  ∃ o, StrategyGame.PositiveSupport (fun y (_ : LaneDisturbance) action => actualRows6 (runInputs6 a .target) y action)
    x .nominal act o ∧ entry = frame .target (actualUpdate6 (runInputs6 a .target) x act o)

theorem result_readout_iff (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (r : RouteId) (entry : Registers Unit FrameValue) :
    RouteComponent.Result POS04ExecutionFrontier.schema routeRaw a (ready a hc) r entry ↔
      ResultReadout a r entry := by
  constructor
  · rintro ⟨_,arrived,routes,da,o,ha,hr,hrsp,hd,hact,hn,hp,hu⟩
    have har := (arrival_readout_iff a hc r arrived).mp ha
    rw [har.2.2.2.2] at ha hrsp hn hp hu
    rw [har.2.2.2.2] at har
    have he := Option.some.inj (hrsp.symm.trans (response_eq a hc .target (arrivalRun a r) _ r))
    subst da
    refine ⟨har,?_,o,?_,?_⟩
    · simpa only [StrategyGame.Normalized,StrategyGame.PositiveSupport,routeRaw,rows_eq a hc] using hn
    · simpa only [StrategyGame.PositiveSupport,routeRaw,rows_eq a hc] using hp
    · exact hu.trans (update_eq a hc .target _ .nominal _ o)
  · rintro ⟨har,hn,o,hp,hu⟩
    have hact : responseAction a (arrivalRun a r) ∈ actions := by
      cases responseAction a (arrivalRun a r) <;> decide
    refine ⟨POS04ExecutionFrontier.canonical_domain.1,frame .target (arrivalRun a r),pathsFor a,
      (.nominal,responseAction a (arrivalRun a r)),o,
      (arrival_readout_iff a hc r _).mpr har,routes_read a hc,
      response_eq a hc .target _ _ r,(show LaneDisturbance.nominal ∈ [.nominal] from by decide),hact,?_,?_,?_⟩
    · simpa only [StrategyGame.Normalized,StrategyGame.PositiveSupport,routeRaw,rows_eq a hc] using hn
    · simpa only [StrategyGame.PositiveSupport,routeRaw,rows_eq a hc] using hp
    · dsimp only [routeRaw]
      rw [update_eq a hc]
      exact hu

def arrivalFor (r : RouteId) : Run6 := ⟨.inK .p1w0,0,0,routeRegister r,true⟩

theorem canonical_source_terminal (r : RouteId) :
    actualFold canonical .source (acquisitionInitialRun canonical .source r) (wordFor canonical r) =
      ⟨.inK .p1w0,2,2,routeRegister r,true⟩ := by
  cases r <;> decide +kernel

theorem canonical_arrival_unique (r : RouteId) (arrived : Registers Unit FrameValue)
    (ha : AcquisitionExecution.Arrival POS04ExecutionFrontier.schema acquisition canonical
      (ready canonical (canonical_complete _)) r arrived) : arrived = frame .target (arrivalFor r) := by
  obtain ⟨histories,routes,hh,hr,he⟩ := arrival_eq canonical (canonical_complete _) r arrived ha
  have hw := words_read canonical (canonical_complete _)
  have hhist := Option.some.inj (hh.symm.trans hw)
  have hroute := Option.some.inj (hr.symm.trans canonical_routes_read)
  subst histories; subst routes
  dsimp only at he
  rw [canonical_source_terminal] at he
  exact he

theorem canonical_arrival (r : RouteId) :
    AcquisitionExecution.Arrival POS04ExecutionFrontier.schema acquisition canonical
      (ready canonical (canonical_complete _)) r (frame .target (arrivalFor r)) := by
  let ev := (POS04ExecutionFrontier.eventView.read canonical).getD
    (fun _ => ⟨.sourceLive,.sourceLive,false,false,false,false,0⟩)
  let input := (POS04ExecutionFrontier.receiverView.read canonical).getD ⟨false,false,false,false⟩
  refine ⟨wordFor canonical,(fun r => ⟨r,[.mix1,.mix2,.exit]⟩),ev,realizedStages,input,
    words_read canonical (canonical_complete _),canonical_routes_read,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · cases r <;> decide
  · cases r <;> decide
  · dsimp only
    refine ⟨.mix1,[.mix2,.exit],rfl,rfl,?_,by decide,.exit,rfl,rfl,rfl,rfl⟩
    intro id hid; cases id <;> decide
  · dsimp only
    exact ⟨rfl,rfl,rfl,fun _ => ⟨.mix1,by decide,by decide,by decide,rfl,rfl,rfl⟩⟩
  · exact AcquisitionExecution.foldHistory acquisition canonical (ready canonical (canonical_complete _))
      (AcquisitionExecution.initial acquisition canonical (ready canonical (canonical_complete _)) r)
      (wordFor canonical r)
  · apply AcquisitionExecution.history_check_executes
    rw [initial_eq canonical (canonical_complete _),supported_word_iff canonical (canonical_complete _)]
    cases r <;> decide +kernel
  · rw [initial_eq canonical (canonical_complete _),fold_eq canonical (canonical_complete _),canonical_source_terminal,receive_eq canonical (canonical_complete _)]
    rfl

theorem canonical_domain : AcquisitionExecution.DomainCheck POS04ExecutionFrontier.schema acquisition :=
  POS04ExecutionFrontier.canonical_domain.1

def resultFor (r : RouteId) : Run6 := ⟨.inK .p2w1,1,1,routeRegister r,true⟩

theorem canonical_result (r : RouteId) :
    RouteComponent.Result POS04ExecutionFrontier.schema routeRaw canonical
      (ready canonical (canonical_complete _)) r (frame .target (resultFor r)) := by
  refine ⟨canonical_domain,frame .target (arrivalFor r),(fun r => ⟨r,[.mix1,.mix2,.exit]⟩),
    (.nominal,.cw),.inK .p2w1,canonical_arrival r,canonical_routes_read,?_,by decide,by decide,?_,?_,?_⟩
  · simp only [routeRaw,acquisition,lift,RunFrame.evaluation,frame,decode]
    rfl
  · simp only [StrategyGame.Normalized,StrategyGame.PositiveSupport,routeRaw,rows_eq canonical (canonical_complete _)]
    refine ⟨?_,?_,.inK .p2w1,1,?_,by decide⟩
    · cases r <;> decide +kernel
    · cases r <;> decide +kernel
    · cases r <;> decide +kernel
  · unfold StrategyGame.PositiveSupport
    dsimp only [routeRaw]
    rw [rows_eq canonical (canonical_complete _)]
    exact ⟨1,by cases r <;> decide +kernel,by decide⟩
  · dsimp only [routeRaw]
    rw [update_eq canonical (canonical_complete _)]
    rfl

theorem canonical_retained (r : RouteId) :
    RouteComponent.Retained POS04ExecutionFrontier.schema routeRaw canonical
      (ready canonical (canonical_complete _)) r (routeRegister r)
      (ambientPhase (.inK ((routeRegister r).1.getD 0 .p0w0))) (.target,.inK .p1w0) := by
  refine ⟨?_,⟨_,canonical_result r⟩,?_,?_⟩
  · unfold RouteComponent.expected
    dsimp only [routeRaw]
    rw [words_read canonical (canonical_complete _),
      canonical_routes_read]
    apply congrArg some
    cases r <;> rfl
  · intro arrived ha
    rw [canonical_arrival_unique r arrived ha]
    rfl
  · intro entry he
    obtain ⟨arrived,d,act,o,ha,hp,hu⟩ := RouteComponent.result_actual_update _ routeRaw canonical
      (ready canonical (canonical_complete _)) r entry he
    rw [canonical_arrival_unique r arrived ha] at hu
    dsimp only [routeRaw] at hu
    rw [update_eq canonical (canonical_complete _)] at hu
    subst entry
    refine ⟨rfl,?_,rfl⟩
    cases r <;> rfl

theorem positive : RoutePass canonical := by
  refine ⟨ready_route canonical (canonical_complete _),.a,.b,by decide,by decide,by decide,?_,
    routeRegister .a,routeRegister .b,0,1,(.target,.inK .p1w0),by decide,by decide,?_,?_⟩
  · unfold RouteComponent.pathIdentity
    dsimp only [routeRaw]
    rw [words_read canonical (canonical_complete _),
      canonical_routes_read]
    decide +kernel
  · exact canonical_retained .a
  · exact canonical_retained .b

theorem positive_route_status :
    RouteComponent.statusOf POS04ExecutionFrontier.schema routeRaw canonical = .routeIndexed :=
  (status_preserves_full_comparison canonical).mpr positive

theorem source_absent_rejected (a : CSTTT.POS04.Assigned.Assignment)
    (input : Receiver) (hi : a .receiverInput = some input) (absent : input.sourcePresent = false) :
    ¬ RoutePass a := by
  apply RouteComponent.source_absent_rejected _ routeRaw a
    ⟨input.sourcePresent,input.targetReceiverFunded,input.funded,input.mixedEventRequired⟩ _ absent
  simp [routeRaw,acquisition,POS04ExecutionFrontier.receiverView,CellView.read,hi]

theorem missing_owner_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ RoutePass (put a (.resources .target) none) := by
  apply RouteComponent.missing_readout_rejected _ routeRaw _ (.resources .target)
  · simp [RouteComponent.scope,routeRaw,Expr.dependencies]
  · simp

theorem wrong_owner_rejected (a : CSTTT.POS04.Assigned.Assignment)
    (resource : ResourceData) (hi : a (.resources .target) = some resource)
    (bad : resource.owner = .source) : ¬ RoutePass a := by
  apply RouteComponent.owner_mismatch_rejected _ routeRaw a (tagCarrierId .source) (by decide)
  intro entry
  simp [routeRaw,Expr.eval,hi,bad]

/-- A missing post-exit branch cannot be replaced by a source branch, or by
the canonical positive row. This applies to arbitrary assigned empty rows. -/
theorem empty_target_support_rejected (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a)
    (empty : ∀ x act, actualRows6 (runInputs6 a .target) x act = []) : ¬ RoutePass a := by
  apply RouteComponent.no_result_rejected _ routeRaw a
  intro h r entry he
  obtain ⟨x,d,act,o,hp,_⟩ := result_target_step a hc r entry he
  simp [StrategyGame.PositiveSupport,empty] at hp

def erasedTargetRows : CSTTT.POS04.Assigned.Assignment :=
  put canonical (.rows .target) (some (fun _ _ => []))

theorem erased_target_complete : Complete dependencies erasedTargetRows := by
  intro k hk
  cases k with
  | rows tag => cases tag <;> rfl
  | _ => rfl

theorem erased_target_row (x : Run6) (act : Action) :
    actualRows6 (runInputs6 erasedTargetRows .target) x act = [] := by
  cases hf : x.factor <;> simp [actualRows6,row6,hf,runInputs6,extraInputs,inputs,Assigned.decode,
    clauseScope,commonScope,erasedTargetRows]

theorem erased_target_rejected : ¬ RoutePass erasedTargetRows :=
  empty_target_support_rejected erasedTargetRows erased_target_complete erased_target_row

/-- The SAME perturbation leaves source history execution supported. Thus
the target-row guard tests the real mode switch, not loss of acquisition. -/
theorem erased_target_source_history_still_supported (r : RouteId) :
    AcquisitionExecution.HistoryCheck acquisition erasedTargetRows (ready _ erased_target_complete)
      (frame .source (acquisitionInitialRun erasedTargetRows .source r))
      (wordFor erasedTargetRows r) := by
  rw [supported_word_iff _ erased_target_complete]
  cases r <;> decide +kernel

theorem constant_register_readout_rejected :
    ¬ RouteComponent.Pass POS04ExecutionFrontier.schema
      {routeRaw with register := .literal ([],[])} canonical :=
  RouteComponent.constant_register_rejected _ _ _ ([],[]) (fun _ => rfl)

theorem constant_register_no_named_memory :
    ¬ RouteComponent.ExecutedMemory POS04ExecutionFrontier.schema
      {routeRaw with register := .literal ([],[])} canonical :=
  RouteComponent.constant_register_no_memory _ _ _ ([],[]) (fun _ => rfl)

theorem constant_probe_rejected :
    ¬ RouteComponent.Pass POS04ExecutionFrontier.schema
      {routeRaw with readout := .literal (some 0)} canonical :=
  RouteComponent.constant_probe_rejected _ _ _ 0 (fun _ => rfl)

/-- The post-step register equation is independent of the selected actual
outcome. This quantifies over ALL actual response branches. -/
theorem every_result_retains_provenance (r : RouteId) (entry : Registers Unit FrameValue)
    (he : RouteComponent.Result POS04ExecutionFrontier.schema routeRaw canonical
      (ready canonical (canonical_complete _)) r entry) :
    routeRaw.register.eval canonical entry () = some (routeRegister r) ∧
    routeRaw.readout.eval canonical entry () =
      some (some (ambientPhase (.inK ((routeRegister r).1.getD 0 .p0w0)))) ∧
    routeRaw.owner.eval canonical entry () = some (tagCarrierId .target) :=
  (canonical_retained r).2.2.2 entry he

end CSTTT.TargetTheory.GenericHandoff.POS04RouteExecution
