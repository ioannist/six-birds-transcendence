import CSTTT.Targets.GenericHandoff.ExecutionFrontier
import CSTTT.Targets.GenericHandoff.POS04RegisterLumping
import CSTTT.Targets.GenericHandoff.POS04RegisterReadoutLaws
import CSTTT.Targets.GenericHandoff.ReadoutFrontierRestriction

/-! Source-frontier instantiation on POS-04's shared partial assignment.
Raw histories are converted to disturbance/action/outcome words using the
ASSIGNED policy, not a canonical policy default. Initializers have no run
argument. This is the source execution boundary, not the finished two-sided
G4/G1c lineage adapter or a new POS-04 model. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ExecutionFrontier
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory RegisterInterpreter RegisterInitialization POS04RegisterDynamics
set_option maxRecDepth 8192

abbrev Static (X : Type) := Expr Cell Value Empty NoValue Unit X

def historyPath (histories : HistoryId → List KState) (routes : List Route) (r : RouteId) :=
  ((routes.find? (fun v => v.id == r)).map (fun v => histories v.sourceHistory)).getD []

def pathExpr : Static (RouteId → List KState) :=
  .map (fun (p : (HistoryId → List KState) × List Route) => historyPath p.1 p.2)
    (.pair (.cell Cell.histories) (.cell Cell.routeTable))

def wordExpr : StaticView Cell Value (RouteId → List (ComputedFIACH.LaneDisturbance × Action × Ambient)) :=
  ⟨.map (fun (p : (RouteId → List KState) × (KState → Action)) => fun r =>
      ((p.1 r).zip ((p.1 r).drop 1)).map (fun e => (.nominal,p.2 e.1,.inK e.2)))
    (.pair pathExpr (.cell Cell.policy))⟩

def residueExpr : Static (RouteId → List KState × List EventId) :=
  .map (fun (p : (HistoryId → List KState) × List Route) => fun r =>
      ((p.2.find? (fun v => v.id == r)).map (fun v => (p.1 v.sourceHistory,v.eventPath))).getD ([],[]))
    (.pair (.cell Cell.histories) (.cell Cell.routeTable))

def initializer : InitialProgram Cell Value Register RegisterValue RouteId
  | .factor => .map (fun (p : (RouteId → List KState) × RouteId) => Ambient.inK ((p.1 p.2).getD 0 .p0w0))
      (.pair (pathExpr.reenv (fun _ => ())) (.environment id))
  | .counter | .ticks => .literal (0 : Nat)
  | .residue => .map (fun p => p.1 p.2) (.pair (residueExpr.reenv (fun _ => ())) (.environment id))
  | .funded => .map Receiver.funded (.cell Cell.receiverInput)

def routeView : CellView Cell Value (RouteId → AcquisitionExecution.Route RouteId EventId) :=
  ⟨.routeTable,fun routes r => ⟨r,((routes.find? (fun v => v.id == r)).map Route.eventPath).getD []⟩⟩
def eventView : CellView Cell Value (EventId → AcquisitionExecution.Event CSTTT.POS04.Stage) :=
  ⟨.eventTable,fun events id =>
    match events.find? (fun e => e.id == id) with
    | none => ⟨.sourceLive,.sourceLive,false,false,false,false,0⟩
    | some e => ⟨e.fromStage,e.toStage,e.sourceSupport,e.targetSupport,e.strictStep,e.atomic,
        stages.idxOf e.toStage - stages.idxOf e.fromStage⟩⟩
def receiverView : CellView Cell Value AcquisitionExecution.Receiver :=
  ⟨.receiverInput,fun r => ⟨r.sourcePresent,r.targetReceiverFunded,r.funded,r.mixedEventRequired⟩⟩

def acquisition : AcquisitionExecution.Raw Cell Value Register RegisterValue
    ComputedFIACH.LaneDisturbance Action Ambient CSTTT.POS04.Stage EventId RouteId RouteId where
  initializer := initializer
  histories := wordExpr
  routes := routeView
  events := eventView
  realized := ⟨.realized,id⟩
  receiver := receiverView
  -- Source-frame coordinates are already in their source namespace. Receiver
  -- transfer is deliberately NOT certified by this execution-only instance.
  receive := fun r => .register r
  arrivalResponse := .map (fun p => (ComputedFIACH.LaneDisturbance.nominal, p.1 p.2))
    (.pair (.cell Cell.policy)
      (.map (fun o => match o with | Ambient.inK s => s | _ => .p0w0) (.register Register.factor)))
  execution := {
    disturbances := [.nominal]
    actions := actions
    outcomes := ambientStates
    row := POS04RegisterFuture.enabledRow .source
    program := program .source }

def schema : AcquisitionExecution.Schema CSTTT.POS04.Stage EventId RouteId RouteId :=
  ⟨stages,eventIds,routeIds,routeIds,.sourceLive,.targetExit,tagCarrierId .source,tagCarrierId .target,stages.idxOf⟩

def audit : List (RouteId × Nat) := ComputedFIACH.acquisitionSnapshotIndices.map (fun i => (i.1,snapshotOccurrence i.2))

def raw : ExecutionFrontier.Raw Cell Value Register RegisterValue
    ComputedFIACH.LaneDisturbance Action Ambient CSTTT.POS04.PredictiveNow
      (List KState × List EventId) Bool CSTTT.POS04.Stage EventId RouteId RouteId :=
  ⟨acquisition,readouts .source,POS04RegisterReadoutLaws.recipes .source,2,audit,schema,Prod.fst⟩

def dependencies : List Cell := temporalDependencies .source ++
  [.policy,.receiverInput,.histories,.routeTable,.eventTable,.realized]

theorem temporal_eq : ExecutionFrontier.temporal raw = POS04RegisterFuture.raw .source := rfl

theorem ready (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) : ExecutionFrontier.Ready raw a := by
  refine ⟨⟨?_,?_,?_,?_,?_⟩,POS04RegisterFuture.ready a .source (fun k hk => hc k (List.mem_append_left _ hk))⟩
  · intro k hk
    simp [raw,acquisition,AcquisitionExecution.Raw.dependencies,StaticView.dependencies,
      wordExpr,pathExpr,routeView,eventView,receiverView,Expr.dependencies] at hk
    rcases hk with hk | hk | hk | hk | hk | hk | hk | hk
    all_goals subst k; exact hc _ (by simp [dependencies,temporalDependencies,coreDependencies])
  · intro r k hk
    apply hc k
    cases r <;> simp_all [raw,acquisition,initializer,pathExpr,residueExpr,Expr.dependencies,Expr.reenv_dependencies,dependencies,temporalDependencies,coreDependencies]
    all_goals grind
  · exact (POS04RegisterFuture.ready a .source (fun k hk => hc k (List.mem_append_left _ hk))).1
  · exact (POS04RegisterFuture.ready a .source (fun k hk => hc k (List.mem_append_left _ hk))).2.1
  · intro r k hk; simp [raw,acquisition,Expr.dependencies] at hk

theorem source_routes (a : CSTTT.POS04.Assigned.Assignment) :
    (runInputs6 a .source).base.routes = (a .routeTable).getD (canonicalValue .routeTable) := by
  simp [runInputs6,extraInputs,Assigned.decode,clauseScope,commonScope]
theorem source_histories (a : CSTTT.POS04.Assigned.Assignment) :
    (runInputs6 a .source).base.histories = (a .histories).getD (canonicalValue .histories) := by
  simp [runInputs6,extraInputs,Assigned.decode,clauseScope,commonScope]
theorem source_policy (a : CSTTT.POS04.Assigned.Assignment) :
    (runInputs6 a .source).base.base.policy = (a .policy).getD (canonicalValue .policy) := by
  simp [runInputs6,extraInputs,inputs,Assigned.decode,clauseScope,commonScope]
theorem source_path (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId) :
    historyPath ((a .histories).getD (canonicalValue .histories))
      ((a .routeTable).getD (canonicalValue .routeTable)) r = ComputedFIACH.acquisitionHistory a .source r := by
  unfold historyPath ComputedFIACH.acquisitionHistory
  simp only [source_routes,source_histories]
  cases ((a .routeTable).getD (canonicalValue .routeTable)).find? (fun v => v.id == r) <;> rfl

theorem word_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    acquisition.histories.read a = some (fun r =>
      let path := ComputedFIACH.acquisitionHistory a .source r
      (path.zip (path.drop 1)).map (fun e => (ComputedFIACH.LaneDisturbance.nominal,
        (runInputs6 a .source).base.base.policy e.1, Ambient.inK e.2))) := by
  have hh := cell_value (hc .histories (by simp [dependencies]))
  have hr := cell_value (hc .routeTable (by simp [dependencies]))
  have hp := cell_value (hc Cell.policy (by simp [dependencies]))
  simp only [acquisition,wordExpr,StaticView.read,pathExpr,Expr.eval]
  rw [hh,hr,hp]
  try simp only [Option.map_some,Option.bind_some]
  apply congrArg some
  funext r
  dsimp only
  rw [source_path,source_policy]

theorem initial_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) (r : RouteId) :
    ExecutionFrontier.initial raw a (ready a hc) r = encode (ComputedFIACH.acquisitionInitialRun a .source r) := by
  funext k
  have he := RegisterInitialization.initial_eq initializer a (ready a hc).1.2.1 r k
  apply Option.some.inj
  change some (RegisterInitialization.initial initializer a (ready a hc).1.2.1 r k) = _
  rw [← he]
  cases k
  all_goals simp only [RegisterInitialization.evaluate,initializer,Expr.eval,Expr.reenv_eval,encode,
    ComputedFIACH.acquisitionInitialRun]
  all_goals try rfl
  case factor =>
    have hh := cell_value (hc .histories (by simp [dependencies]))
    have hr := cell_value (hc .routeTable (by simp [dependencies]))
    simp only [pathExpr,Expr.eval]
    rw [hh,hr]
    change some (Ambient.inK ((historyPath ((a .histories).getD (canonicalValue .histories))
      ((a .routeTable).getD (canonicalValue .routeTable)) r).getD 0 .p0w0)) = _
    rw [source_path]
  case residue =>
    have hh := cell_value (hc .histories (by simp [dependencies]))
    have hr := cell_value (hc .routeTable (by simp [dependencies]))
    simp only [residueExpr,Expr.eval]
    rw [hh,hr]
    unfold routeTuple
    simp only [source_routes,source_histories]
    rfl
  case funded =>
    have hm := cell_value (hc .receiverInput (by simp [dependencies]))
    rw [hm]
    rfl

theorem canonical_ready : ExecutionFrontier.Ready raw canonical := ready canonical (canonical_complete _)
theorem canonical_one_step : FutureLumping.OneStep (RegisterFuture.future (ExecutionFrontier.temporal raw) canonical canonical_ready.2) :=
  POS04RegisterFuture.one_step canonical .source (canonical_complete _) (canonical_finite_bisim6 .source)

theorem actual_update (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (x : Run6) (d : ComputedFIACH.LaneDisturbance) (act : Action) (o : Ambient) :
    AcquisitionExecution.update acquisition a (ready a hc).1 (encode x) d act o =
      encode (actualUpdate6 (runInputs6 a .source) x act o) :=
  checked_actual a .source (fun k hk => hc k (by
    simp [coreDependencies] at hk
    rcases hk with hk | hk | hk <;> subst k <;> simp [dependencies,temporalDependencies,coreDependencies])) x d act o

theorem actual_rows (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (x : Run6) (d : ComputedFIACH.LaneDisturbance) (act : Action) :
    AcquisitionExecution.rows acquisition a (encode x) d act = actualRows6 (runInputs6 a .source) x act := by
  change AcquisitionExecution.rows raw.acquisition a (encode x) d act = _
  rw [← ExecutionFrontier.rows_shared raw a (ready a hc) (encode x) d act]
  exact POS04RegisterFuture.row_eq a .source (fun k hk => hc k (List.mem_append_left _ hk)) x d act

theorem support_any (xs : List (Ambient × Rat)) (o : Ambient) :
    (∃ p, (o,p) ∈ xs ∧ 0 < p) ↔ (xs.any fun e => decide (e.1 = o ∧ 0 < e.2)) = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨p,hp,hn⟩; exact ⟨(o,p),hp,by simpa using hn⟩
  · rintro ⟨⟨dest,p⟩,hm,hb⟩
    obtain ⟨he,hn⟩ := of_decide_eq_true hb
    change dest = o at he
    subst dest
    exact ⟨p,hm,hn⟩

/-- Closed finite prefix checker; its equivalence below is for arbitrary
partial assignments once the consumed primitives are present. -/
def actualPrefixCheck (a : CSTTT.POS04.Assigned.Assignment) : Run6 →
    List (ComputedFIACH.LaneDisturbance × Action × Ambient) → Prop
  | _, [] => True
  | x, (_d,act,o)::rest =>
    (actualRows6 (runInputs6 a .source) x act).any (fun e => decide (e.1 = o ∧ 0 < e.2)) = true ∧
    actualWeight6 (runInputs6 a .source) x act o > 0 ∧
    actualPrefixCheck a (actualUpdate6 (runInputs6 a .source) x act o) rest

def actualPrefixDecision (a : CSTTT.POS04.Assigned.Assignment) (x : Run6) :
    (word : List (ComputedFIACH.LaneDisturbance × Action × Ambient)) → Decidable (actualPrefixCheck a x word)
  | [] => isTrue trivial
  | (_d,act,o)::rest =>
    letI := actualPrefixDecision a (actualUpdate6 (runInputs6 a .source) x act o) rest
    inferInstanceAs (Decidable (_ ∧ _ ∧ actualPrefixCheck a (actualUpdate6 (runInputs6 a .source) x act o) rest))
instance (a : CSTTT.POS04.Assigned.Assignment) (x : Run6)
    (word : List (ComputedFIACH.LaneDisturbance × Action × Ambient)) : Decidable (actualPrefixCheck a x word) :=
  actualPrefixDecision a x word

theorem prefix_check_iff (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (x : Run6) (word : List (ComputedFIACH.LaneDisturbance × Action × Ambient)) :
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
        encode (actualUpdate6 (runInputs6 a .source) x act o) := actual_update a hc x d act o
    rw [hn,ih]
    change (_ ∧ RegisterFuture.weight (POS04RegisterFuture.raw .source) a
      (POS04RegisterFuture.ready a .source (fun k hk => hc k (List.mem_append_left _ hk))) (encode x) (d,act) o > 0 ∧ _) ↔ _
    rw [POS04RegisterFuture.weight_eq a .source (fun k hk => hc k (List.mem_append_left _ hk)) x d act o]
    unfold StrategyGame.PositiveSupport
    rw [actual_rows a hc]
    exact and_congr (support_any _ _) Iff.rfl

theorem canonical_audit : ExecutionFrontier.AuditCheck raw canonical canonical_ready := by
  refine ⟨by decide,?_,?_,?_,?_⟩
  · exact fun r =>
      let path := ComputedFIACH.acquisitionHistory canonical .source r
      (path.zip (path.drop 1)).map (fun e => (ComputedFIACH.LaneDisturbance.nominal,
        (runInputs6 canonical .source).base.base.policy e.1, Ambient.inK e.2))
  · exact word_eq canonical (canonical_complete _)
  · rintro ⟨r,n⟩ hi
    have hn : n = 1 ∨ n = 2 := by cases r <;> simpa [raw,audit,ComputedFIACH.acquisitionSnapshotIndices,routeIds,snapshotPositions,snapshotOccurrence] using hi
    rcases hn with rfl | rfl
    all_goals refine ⟨by omega,?_,?_⟩
    all_goals try (cases r <;> decide)
    all_goals
      rw [initial_eq canonical (canonical_complete _),prefix_check_iff canonical (canonical_complete _)]
      simp only [ExecutionFrontier.historyPrefix]
      cases r <;> decide +kernel
  · intro hist hh
    exact ⟨(hist,2),by cases hist <;> decide,rfl,by cases hist <;> decide⟩

theorem canonical_paths : ExecutionFrontier.PathsAvailable raw canonical := by
  refine ⟨(routeView.read canonical).getD (fun r => ⟨r,[]⟩),
    (eventView.read canonical).getD (fun _ => ⟨.sourceLive,.sourceLive,false,false,false,false,0⟩),
    realizedStages,(receiverView.read canonical).getD ⟨false,false,false,false⟩,
    rfl,rfl,rfl,rfl,?_⟩
  rintro ⟨r,n⟩ hi
  dsimp only [raw]
  have hr : r ∈ routeIds := by cases r <;> decide
  refine ⟨hr,rfl,?_,?_⟩
  · cases r
    all_goals refine ⟨.mix1,[.mix2,.exit],rfl,rfl,?_,by decide,.exit,rfl,rfl,rfl,rfl⟩
    all_goals intro id hid; cases id <;> decide
  · cases r <;> refine ⟨rfl,rfl,rfl,?_⟩ <;> intro _
    all_goals exact ⟨.mix1,by decide,by decide,by decide,rfl,rfl,rfl⟩

theorem canonical_domain : AcquisitionExecution.DomainCheck schema acquisition ∧ ExecutionFrontier.ExecutionDomain raw := by
  constructor
  · refine ⟨by decide,by decide,?_,?_,?_,?_,by decide,?_⟩
    all_goals intro x; cases x <;> decide
  · refine ⟨by decide,?_,?_⟩
    · intro o; cases o with
      | inK s => cases s <;> decide
      | p2w0 => decide
      | p5w1 => decide
    · intro act; cases act <;> decide

theorem canonical_roots_subset (x : Registers Register RegisterValue)
    (hx : x ∈ ExecutionFrontier.roots raw canonical canonical_ready) :
    x ∈ POS04RegisterReadoutLaws.roots canonical .source := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hx
  subst x
  rw [initial_eq canonical (canonical_complete _)]
  apply List.mem_map.mpr
  refine ⟨ComputedFIACH.acquisitionInitialRun canonical .source i.1,?_,rfl⟩
  rcases i with ⟨r,n⟩
  cases r
  all_goals dsimp only [Prod.fst]; decide +kernel

theorem canonical_readout_laws :
    RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal raw) raw.recipes canonical canonical_ready.2
      (ExecutionFrontier.roots raw canonical canonical_ready) := by
  apply RegisterFuture.restrict_readout_gate (POS04RegisterFuture.raw .source)
    (POS04RegisterReadoutLaws.recipes .source) canonical canonical_ready.2
    (POS04RegisterReadoutLaws.roots canonical .source) _
    (POS04RegisterReadoutLaws.readout_gate (canonical_accept6 .source))
  · intro hn
    have ht := congrArg List.length hn
    change (raw.audit.map _).length = 0 at ht
    simp only [List.length_map] at ht
    have hp : raw.audit.length = 4 := by decide
    omega
  · intro r hr; exact FutureClosure.root _ (canonical_roots_subset r hr)

theorem canonical_rows (x : Run6) (act : Action) :
    (∀ e ∈ actualRows6 (runInputs6 canonical .source) x act, 0 ≤ e.2) ∧
    (((actualRows6 (runInputs6 canonical .source) x act).map Prod.snd).sum = 0 ∨
    ((actualRows6 (runInputs6 canonical .source) x act).map Prod.snd).sum = 1) := by
  have hr : actualRows6 (runInputs6 canonical .source) x act =
      actualRows6 (runInputs6 canonical .source) ⟨x.factor,0,0,([],[]),x.funded⟩ act := rfl
  rw [hr]
  cases hf : x.funded <;> cases ho : x.factor <;> cases act
  all_goals try (rename_i s; cases s)
  all_goals constructor
  all_goals first | decide +kernel | (intro e he; simp_all [actualRows6,enabled6])

theorem canonical_row_laws : ExecutionFrontier.RowLawGate raw canonical canonical_ready := by
  intro x hx d hd act ha
  rw [show AcquisitionExecution.rows raw.acquisition canonical x d act =
      actualRows6 (runInputs6 canonical .source) (decodeRun x) act from by
      simpa only [encode_decode] using actual_rows canonical (canonical_complete _) (decodeRun x) d act]
  exact canonical_rows (decodeRun x) act

theorem positive : ExecutionFrontier.Valid raw canonical :=
  ⟨canonical_ready,canonical_audit,canonical_domain.1,canonical_domain.2,canonical_paths,
    canonical_one_step,canonical_readout_laws,canonical_row_laws⟩

/-- A direct negative of the executed-frame readout. No failed Boolean sibling
is used to deny a snapshot witness; its own atomic input is absent. -/
theorem missing_atomic_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ ExecutionFrontier.Valid raw (Assigned.put a .eventTable none) := by
  apply ExecutionFrontier.missing_atomic_view
  simp [raw,acquisition,eventView,CellView.read]

theorem missing_policy_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ ExecutionFrontier.Valid raw (Assigned.put a .policy none) := by
  apply ExecutionFrontier.missing_consumed_input _ _ .policy
  · simp [raw,acquisition,AcquisitionExecution.Raw.dependencies,wordExpr,pathExpr,
      StaticView.dependencies,Expr.dependencies]
  · simp

theorem source_absent_rejected (a : CSTTT.POS04.Assigned.Assignment)
    (r : CSTTT.POS04.Receiver) (hr : a .receiverInput = some r) (absent : r.sourcePresent = false) :
    ¬ ExecutionFrontier.Valid raw a := by
  apply ExecutionFrontier.inactive_receiver_rejected raw a
    ⟨r.sourcePresent,r.targetReceiverFunded,r.funded,r.mixedEventRequired⟩ _ .source absent
  simp [raw,acquisition,receiverView,CellView.read,hr]

def cappedProgress := ExecutionFrontier.replaceReadout raw .progress (show E Unit Nat from .map (fun n : Nat => Nat.min n (2 : Nat)) (.register Register.counter))
theorem capped_ready : ExecutionFrontier.Ready cappedProgress canonical := canonical_ready

/-- The cap agrees at both audit occurrences 1 and 2, but the independent
progress recipe requires 3 on a future step from the executed endpoint. -/
theorem capped_progress_rejected : ¬ ExecutionFrontier.Valid cappedProgress canonical := by
  let i : RouteId × Nat := (.a,2)
  let x := ExecutionFrontier.snapshot raw canonical canonical_ready i
  have hi : i ∈ raw.audit := by decide
  have hx := (ExecutionFrontier.snapshot_execution raw canonical canonical_ready canonical_audit i hi).2
  apply ExecutionFrontier.readout_mismatch_rejected raw canonical canonical_ready x hx
    .nominal (by decide) .cw (by decide) (.inK .p2w1) (by decide)
    .progress (show E Unit Nat from .map (fun n : Nat => Nat.min n (2 : Nat)) (.register Register.counter)) capped_ready
  intro law
  have laws : RegisterFuture.FieldLaw (ExecutionFrontier.temporal raw) raw.recipes
      canonical canonical_ready.2 x (.nominal,.cw) (.inK .p2w1) .order :=
    (canonical_readout_laws.2.2.2.2.2.1 x hx .nominal (by decide) .cw (by decide)
      (.inK .p2w1) (by decide)).1 .order
  have hcounter : (x Register.counter : Nat) = (2 : Nat) := by
    unfold x ExecutionFrontier.snapshot
    rw [initial_eq canonical (canonical_complete _)]
    simp only [ExecutionFrontier.historyPrefix]
    change (AcquisitionExecution.foldHistory acquisition canonical canonical_ready.1
      (encode (ComputedFIACH.acquisitionInitialRun canonical .source .a))
      [(.nominal,.cw,.inK .p2w1),(.nominal,.stay,.inK .p1w0)]) Register.counter = (2 : Nat)
    change (AcquisitionExecution.update acquisition canonical canonical_ready.1
      (AcquisitionExecution.update acquisition canonical canonical_ready.1
        (encode (ComputedFIACH.acquisitionInitialRun canonical .source .a)) .nominal .cw (.inK .p2w1))
      .nominal .stay (.inK .p1w0)) Register.counter = (2 : Nat)
    rw [actual_update canonical (canonical_complete _),actual_update canonical (canonical_complete _)]
    rfl
  change (raw.readouts.order).eval canonical (RegisterFuture.next (ExecutionFrontier.temporal raw)
      canonical canonical_ready.2 x (.nominal,.cw) (.inK .p2w1)) () = _ at laws
  change some ((RegisterFuture.next (ExecutionFrontier.temporal raw)
      canonical canonical_ready.2 x (.nominal,.cw) (.inK .p2w1)) Register.counter) = some (Nat.add (x Register.counter) (1 : Nat)) at laws
  have hnext := Option.some.inj laws
  change some ((min : Nat → Nat → Nat) ((RegisterFuture.next (ExecutionFrontier.temporal cappedProgress)
      canonical capped_ready.2 x (.nominal,.cw) (.inK .p2w1)) Register.counter) 2) = some (Nat.add (x Register.counter) (1 : Nat)) at law
  have hnext' : (RegisterFuture.next (ExecutionFrontier.temporal cappedProgress)
      canonical capped_ready.2 x (.nominal,.cw) (.inK .p2w1)) Register.counter = Nat.add (x Register.counter) (1 : Nat) := hnext
  rw [hnext',hcounter] at law
  contradiction

end CSTTT.TargetTheory.GenericHandoff.POS04ExecutionFrontier
