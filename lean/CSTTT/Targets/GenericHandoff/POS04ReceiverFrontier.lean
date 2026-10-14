import CSTTT.Targets.GenericHandoff.POS04BridgeExecution
import CSTTT.Targets.GenericHandoff.ExecutionBridge

/-! Target/receiver execution specialization. The receiver operates on raw
history states and activation primitives from the shared assignment; neither
endpoint classes nor a successful receiver label are supplied. Target history
words, initial registers, dynamics, observations and audit snapshots are all
constructed. The coordinate-copy operation remains the declared near-automatic
POS-04 operation, not independent physical evidence of transport.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ReceiverFrontier
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TransportTheory
open RegisterInterpreter RegisterInitialization POS04RegisterDynamics
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
abbrev Static (X : Type) := Expr Cell Value Empty NoValue Unit X

/-- Exactly active7's declared raw rule, including realization of the mix. -/
def activated (receiver : Receiver) (events : List CSTTT.POS04.Event)
    (realized : List CSTTT.POS04.Stage) : Bool :=
  receiver.sourcePresent && receiver.targetReceiverFunded && receiver.funded &&
    (!receiver.mixedEventRequired || events.any (fun e => e.id != .exit && e.atomic &&
      e.sourceSupport && e.targetSupport && decide (e.fromStage ∈ realized) && decide (e.toStage ∈ realized)))

def targetPath (histories : HistoryId → List KState) (routes : List Route)
    (receiver : Receiver) (events : List CSTTT.POS04.Event) (realized : List CSTTT.POS04.Stage)
    (r : RouteId) : List KState :=
  match routes.find? (fun v => v.id == r) with
  | none => []
  | some route =>
    if activated receiver events realized then
      match receiver.contentRule with
      | .copyTerminalPositionPhase => match (histories route.sourceHistory).getLast? with
        | none => []
        | some s => (histories route.sourceHistory).dropLast ++ [s]
    else []

def pathExpr : Static (RouteId → List KState) :=
  .map (fun p => targetPath p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (.pair (.cell Cell.histories) (.pair (.cell Cell.routeTable) (.pair (.cell Cell.receiverInput)
      (.pair (.cell Cell.eventTable) (.cell Cell.realized)))))

def wordExpr : StaticView Cell Value (RouteId → List (LaneDisturbance × Action × Ambient)) :=
  ⟨.map (fun (p : (RouteId → List KState) × (KState → Action)) => fun r =>
    ((p.1 r).zip ((p.1 r).drop 1)).map (fun e => (.nominal,p.2 e.1,.inK e.2)))
      (.pair pathExpr (.cell Cell.policy))⟩

def initializer : InitialProgram Cell Value Register RegisterValue RouteId
  | .factor => .map (fun (p : (RouteId → List KState) × RouteId) => Ambient.inK ((p.1 p.2).getD 0 .p0w0))
      (.pair (pathExpr.reenv (fun _ => ())) (.environment id))
  | .counter | .ticks => .literal (0 : Nat)
  | .residue => POS04ExecutionFrontier.initializer .residue
  | .funded => .map Receiver.funded (.cell Cell.receiverInput)

def acquisition : AcquisitionExecution.Raw Cell Value Register RegisterValue
    LaneDisturbance Action Ambient CSTTT.POS04.Stage EventId RouteId RouteId :=
  {POS04ExecutionFrontier.acquisition with
    initializer := initializer
    histories := wordExpr
    execution := {
      disturbances := [.nominal]
      actions := actions
      outcomes := ambientStates
      row := POS04RegisterFuture.enabledRow .target
      program := program .target}}

def raw : ExecutionFrontier.Raw Cell Value Register RegisterValue LaneDisturbance Action Ambient
    CSTTT.POS04.PredictiveNow (List KState × List EventId) Bool CSTTT.POS04.Stage EventId RouteId RouteId :=
  ⟨acquisition,readouts .target,POS04RegisterReadoutLaws.recipes .target,2,
    POS04ExecutionFrontier.audit,POS04ExecutionFrontier.schema,Prod.fst⟩

def dependencies : List Cell := temporalDependencies .target ++
  [.policy,.receiverInput,.histories,.routeTable,.eventTable,.realized]

theorem temporal_eq : ExecutionFrontier.temporal raw = POS04RegisterFuture.raw .target := rfl

theorem ready (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) : ExecutionFrontier.Ready raw a := by
  refine ⟨⟨?_,?_,?_,?_,?_⟩,POS04RegisterFuture.ready a .target (fun k hk => hc k (List.mem_append_left _ hk))⟩
  · intro k hk
    apply hc k
    simp [raw,acquisition,AcquisitionExecution.Raw.dependencies,StaticView.dependencies,
      wordExpr,pathExpr,POS04ExecutionFrontier.acquisition,POS04ExecutionFrontier.routeView,
      POS04ExecutionFrontier.eventView,POS04ExecutionFrontier.receiverView,Expr.dependencies] at hk
    rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
    all_goals subst k; simp [dependencies,temporalDependencies,coreDependencies]
  · intro r k hk
    apply hc k
    cases r <;> simp_all [raw,acquisition,initializer,pathExpr,POS04ExecutionFrontier.initializer,
      POS04ExecutionFrontier.residueExpr,Expr.dependencies,Expr.reenv_dependencies,
      dependencies,temporalDependencies,coreDependencies]
    all_goals grind
  · exact (POS04RegisterFuture.ready a .target (fun k hk => hc k (List.mem_append_left _ hk))).1
  · exact (POS04RegisterFuture.ready a .target (fun k hk => hc k (List.mem_append_left _ hk))).2.1
  · intro r k hk; simp [raw,acquisition,POS04ExecutionFrontier.acquisition,Expr.dependencies] at hk

theorem path_equation (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId) :
    targetPath ((a .histories).getD (canonicalValue .histories))
      ((a .routeTable).getD (canonicalValue .routeTable))
      ((a .receiverInput).getD (canonicalValue .receiverInput))
      ((a .eventTable).getD (canonicalValue .eventTable))
      ((a .realized).getD (canonicalValue .realized)) r = acquisitionHistory a .target r := by
  simp only [targetPath,acquisitionHistory,acquisitionTargetHistory,acquisitionReceiver,
    activated,active7,mixed7,runInputs6,extraInputs,clauseScope,commonScope]
  simp only [Assigned.decode,List.mem_append,List.mem_cons,or_true,true_or,if_true]
  cases he : ((a .routeTable).getD (canonicalValue .routeTable)).find? (fun v => v.id == r) with
  | none => rfl
  | some v =>
    by_cases ha : activated ((a .receiverInput).getD (canonicalValue .receiverInput))
      ((a .eventTable).getD (canonicalValue .eventTable)) ((a .realized).getD (canonicalValue .realized)) = true
    all_goals simp_all only [activated,if_pos] <;> rfl

theorem path_read (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    pathExpr.eval a noRegisters () = some (fun r => acquisitionHistory a .target r) := by
  have hh := cell_value (hc .histories (by simp [dependencies]))
  have hr := cell_value (hc .routeTable (by simp [dependencies]))
  have hm := cell_value (hc .receiverInput (by simp [dependencies]))
  have he := cell_value (hc .eventTable (by simp [dependencies]))
  have hs := cell_value (hc .realized (by simp [dependencies]))
  simp only [pathExpr,Expr.eval]
  rw [hh,hr,hm,he,hs]
  try simp only [Option.bind_some,Option.map_some]
  exact congrArg some (funext (path_equation a))

theorem word_equation (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    acquisition.histories.read a = some (fun r =>
      let path := acquisitionHistory a .target r
      (path.zip (path.drop 1)).map (fun e => (LaneDisturbance.nominal,
        (runInputs6 a .target).base.base.policy e.1, Ambient.inK e.2))) := by
  have hp := cell_value (hc Cell.policy (by simp [dependencies]))
  simp only [acquisition,wordExpr,StaticView.read,Expr.eval]
  rw [path_read a hc,hp]
  rfl

/-- The target initializer reads the same raw route register as the source.
Activation/history availability are checked before any initialized default can
become a certified snapshot. -/
theorem initial_equation (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) (r : RouteId) :
    ExecutionFrontier.initial raw a (ready a hc) r = encode (acquisitionInitialRun a .target r) := by
  funext k
  have he := RegisterInitialization.initial_eq initializer a (ready a hc).1.2.1 r k
  apply Option.some.inj
  change some (RegisterInitialization.initial initializer a (ready a hc).1.2.1 r k) = _
  rw [← he]
  cases k
  all_goals simp only [RegisterInitialization.evaluate,initializer,Expr.eval,Expr.reenv_eval,encode,
    acquisitionInitialRun]
  case factor => rw [path_read a hc]; rfl
  case residue =>
    have hh := cell_value (hc .histories (by simp [dependencies]))
    have hr := cell_value (hc .routeTable (by simp [dependencies]))
    simp only [POS04ExecutionFrontier.initializer,POS04ExecutionFrontier.residueExpr,Expr.eval,Expr.reenv_eval]
    rw [hh,hr]
    unfold routeTuple
    rfl
  case funded => rw [cell_value (hc .receiverInput (by simp [dependencies]))]; rfl

theorem actual_update (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (x : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    AcquisitionExecution.update acquisition a (ready a hc).1 (encode x) d act o =
      encode (actualUpdate6 (runInputs6 a .target) x act o) :=
  checked_actual a .target (fun k hk => hc k (by
    simp [coreDependencies] at hk
    rcases hk with hk | hk | hk <;> subst k <;> simp [dependencies,temporalDependencies,coreDependencies])) x d act o

def actualFold (a : CSTTT.POS04.Assigned.Assignment) : Run6 → List (LaneDisturbance × Action × Ambient) → Run6
  | x, [] => x
  | x, (_,act,o)::rest => actualFold a (actualUpdate6 (runInputs6 a .target) x act o) rest

theorem fold_equation (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (x : Run6) (word : List (LaneDisturbance × Action × Ambient)) :
    AcquisitionExecution.foldHistory acquisition a (ready a hc).1 (encode x) word = encode (actualFold a x word) := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [AcquisitionExecution.foldHistory,actualFold,actual_update a hc,ih]

def observed (a : CSTTT.POS04.Assigned.Assignment) (i : RouteId × Nat) :=
  c6ObservationToBridge (observation6 (runInputs6 a .target) .target
    (actualFold a (acquisitionInitialRun a .target i.1) (ExecutionFrontier.historyPrefix raw a i)))

theorem snapshot_equation (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) (i : RouteId × Nat) :
    ExecutionFrontier.observation raw a (ready a hc) i = observed a i := by
  unfold ExecutionFrontier.observation ExecutionFrontier.snapshot
  rw [initial_equation a hc]
  change RegisterFuture.observation (ExecutionFrontier.temporal raw) a _
    (AcquisitionExecution.foldHistory acquisition a _ _ _) = _
  rw [fold_equation a hc]
  exact POS04RegisterFuture.observation_eq a .target
    (fun k hk => hc k (List.mem_append_left _ hk)) _

/-- All target future weights and successors are the actual assigned rows
and ledger/tick updates, on every run, not merely terminal snapshots. -/
theorem future_word_equation (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (x : Run6) (word : List (LaneDisturbance × Action)) (trace : List C6Observation) :
    fullFuture (RegisterFuture.future (ExecutionFrontier.temporal raw) a (ready a hc).2)
      (encode x) word (trace.map c6ObservationToBridge) =
      fullFuture (actualFuture6 a .target) x (word.map Prod.snd) trace :=
  POS04RegisterFuture.word_law a .target (fun k hk => hc k (List.mem_append_left _ hk)) x word trace

theorem actual_rows (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (x : Run6) (d : LaneDisturbance) (act : Action) :
    AcquisitionExecution.rows acquisition a (encode x) d act = actualRows6 (runInputs6 a .target) x act := by
  change AcquisitionExecution.rows raw.acquisition a (encode x) d act = _
  rw [← ExecutionFrontier.rows_shared raw a (ready a hc) (encode x) d act]
  exact POS04RegisterFuture.row_eq a .target (fun k hk => hc k (List.mem_append_left _ hk)) x d act

def actualPrefixCheck (a : CSTTT.POS04.Assigned.Assignment) : Run6 → List (LaneDisturbance × Action × Ambient) → Prop
  | _, [] => True
  | x, (_d,act,o)::rest =>
    (actualRows6 (runInputs6 a .target) x act).any (fun e => decide (e.1 = o ∧ 0 < e.2)) = true ∧
    actualWeight6 (runInputs6 a .target) x act o > 0 ∧
    actualPrefixCheck a (actualUpdate6 (runInputs6 a .target) x act o) rest

def prefixDecision (a : CSTTT.POS04.Assigned.Assignment) (x : Run6) :
    (word : List (LaneDisturbance × Action × Ambient)) → Decidable (actualPrefixCheck a x word)
  | [] => isTrue trivial
  | (_d,act,o)::rest =>
    letI := prefixDecision a (actualUpdate6 (runInputs6 a .target) x act o) rest
    inferInstanceAs (Decidable (_ ∧ _ ∧ actualPrefixCheck a (actualUpdate6 (runInputs6 a .target) x act o) rest))
instance (a : CSTTT.POS04.Assigned.Assignment) (x : Run6) (word : List (LaneDisturbance × Action × Ambient)) :
    Decidable (actualPrefixCheck a x word) := prefixDecision a x word

theorem prefix_check_iff (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (x : Run6) (word : List (LaneDisturbance × Action × Ambient)) :
    ExecutionFrontier.PrefixCheck raw a (ready a hc) (encode x) word ↔ actualPrefixCheck a x word := by
  induction word generalizing x with
  | nil => exact Iff.rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    have hd : d ∈ acquisition.execution.disturbances := by cases d; decide
    have ha : act ∈ acquisition.execution.actions := by cases act <;> decide
    have ho : o ∈ acquisition.execution.outcomes := by cases o with
      | inK s => cases s <;> decide
      | p2w0 => decide
      | p5w1 => decide
    simp only [ExecutionFrontier.PrefixCheck,show raw.acquisition = acquisition from rfl,hd,ha,ho,true_and,actualPrefixCheck]
    have hn : AcquisitionExecution.update raw.acquisition a (ready a hc).1 (encode x) d act o =
        encode (actualUpdate6 (runInputs6 a .target) x act o) := actual_update a hc x d act o
    rw [hn,ih]
    change (_ ∧ RegisterFuture.weight (POS04RegisterFuture.raw .target) a _ (encode x) (d,act) o > 0 ∧ _) ↔ _
    rw [POS04RegisterFuture.weight_eq a .target (fun k hk => hc k (List.mem_append_left _ hk)) x d act o]
    unfold StrategyGame.PositiveSupport
    rw [actual_rows a hc]
    exact and_congr (POS04ExecutionFrontier.support_any _ _) Iff.rfl

theorem canonical_ready : ExecutionFrontier.Ready raw canonical := ready canonical (canonical_complete _)

theorem canonical_audit : ExecutionFrontier.AuditCheck raw canonical canonical_ready := by
  refine ⟨by decide,?_,?_,?_,?_⟩
  · exact fun r =>
      let path := acquisitionHistory canonical .target r
      (path.zip (path.drop 1)).map (fun e => (LaneDisturbance.nominal,
        (runInputs6 canonical .target).base.base.policy e.1, Ambient.inK e.2))
  · exact word_equation canonical (canonical_complete _)
  · rintro ⟨r,n⟩ hi
    have hn : n = 1 ∨ n = 2 := by cases r <;> simpa [raw,POS04ExecutionFrontier.audit,
      acquisitionSnapshotIndices,routeIds,snapshotPositions,snapshotOccurrence] using hi
    rcases hn with rfl | rfl
    all_goals refine ⟨by omega,?_,?_⟩
    all_goals try (cases r <;> decide)
    all_goals
      rw [initial_equation canonical (canonical_complete _),prefix_check_iff canonical (canonical_complete _)]
      simp only [ExecutionFrontier.historyPrefix]
      cases r <;> decide +kernel
  · intro hist hh
    exact ⟨(hist,2),by cases hist <;> decide,rfl,by cases hist <;> decide⟩

theorem canonical_paths : ExecutionFrontier.PathsAvailable raw canonical :=
  POS04ExecutionFrontier.canonical_paths

theorem canonical_domain : AcquisitionExecution.DomainCheck raw.schema acquisition ∧ ExecutionFrontier.ExecutionDomain raw :=
  POS04ExecutionFrontier.canonical_domain

theorem canonical_roots_subset (x : Registers Register RegisterValue)
    (hx : x ∈ ExecutionFrontier.roots raw canonical canonical_ready) :
    x ∈ POS04RegisterReadoutLaws.roots canonical .target := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hx
  subst x
  rw [initial_equation canonical (canonical_complete _)]
  apply List.mem_map.mpr
  refine ⟨acquisitionInitialRun canonical .target i.1,?_,rfl⟩
  rcases i with ⟨r,n⟩
  cases r
  all_goals dsimp only [Prod.fst]; decide +kernel

theorem canonical_readout_laws :
    RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal raw) raw.recipes canonical canonical_ready.2
      (ExecutionFrontier.roots raw canonical canonical_ready) := by
  apply RegisterFuture.restrict_readout_gate (POS04RegisterFuture.raw .target)
    (POS04RegisterReadoutLaws.recipes .target) canonical canonical_ready.2
    (POS04RegisterReadoutLaws.roots canonical .target) _
    (POS04RegisterReadoutLaws.readout_gate (canonical_accept6 .target))
  · intro hn
    have ht := congrArg List.length hn
    change (raw.audit.map _).length = 0 at ht
    simp only [List.length_map] at ht
    have hp : raw.audit.length = 4 := by decide
    omega
  · intro r hr; exact FutureClosure.root _ (canonical_roots_subset r hr)

theorem canonical_row_laws : ExecutionFrontier.RowLawGate raw canonical canonical_ready := by
  intro x hx d hd act ha
  rw [show AcquisitionExecution.rows raw.acquisition canonical x d act =
      actualRows6 (runInputs6 canonical .target) (decodeRun x) act from by
      simpa only [encode_decode] using actual_rows canonical (canonical_complete _) (decodeRun x) d act]
  have he : actualRows6 (runInputs6 canonical .target) (decodeRun x) act =
      actualRows6 (runInputs6 canonical .source) (decodeRun x) act := rfl
  rw [he]
  exact POS04ExecutionFrontier.canonical_rows (decodeRun x) act

theorem positive : ExecutionFrontier.Valid raw canonical :=
  ⟨canonical_ready,canonical_audit,canonical_domain.1,canonical_domain.2,canonical_paths,
    POS04RegisterFuture.one_step canonical .target (canonical_complete _) (canonical_finite_bisim6 .target),
    canonical_readout_laws,canonical_row_laws⟩

/-- Direct rejection of the executed target frame when the shared atomic
witness or any receiver-history input is missing. -/
theorem missing_atomic_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ ExecutionFrontier.Valid raw (Assigned.put a .eventTable none) := by
  apply ExecutionFrontier.missing_atomic_view
  simp [raw,acquisition,POS04ExecutionFrontier.acquisition,POS04ExecutionFrontier.eventView,CellView.read]

theorem missing_history_input (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ wordExpr.dependencies) : ¬ ExecutionFrontier.Valid raw (Assigned.put a k none) := by
  apply ExecutionFrontier.missing_consumed_input raw _ k
  · exact List.mem_append_left _ (List.mem_append_left _ hk)
  · simp

theorem source_absent_rejected (a : CSTTT.POS04.Assigned.Assignment) (r : Receiver)
    (hr : a .receiverInput = some r) (absent : r.sourcePresent = false) : ¬ ExecutionFrontier.Valid raw a := by
  apply ExecutionFrontier.inactive_receiver_rejected raw a
    ⟨r.sourcePresent,r.targetReceiverFunded,r.funded,r.mixedEventRequired⟩ _ .source absent
  simp [raw,acquisition,POS04ExecutionFrontier.acquisition,POS04ExecutionFrontier.receiverView,CellView.read,hr]

end CSTTT.TargetTheory.GenericHandoff.POS04ReceiverFrontier
