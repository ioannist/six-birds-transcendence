import CSTTT.Targets.GenericHandoff.HistoricalSupport
import CSTTT.Targets.GenericHandoff.AcquisitionExecution
import CSTTT.Targets.GenericHandoff.StaticView

/-! TTH-06 historical-support acquisition, G6d manager interpretation.
The source past is checked against RAW factor/action rows, without funded source
execution. Its actual terminal factor, full past and raw event path feed typed
receiver initialization instructions. A realized, activated arrival executes the
SAME target row/updater used by resources. EVERY positive branch is an entry,
including unsafe branches. No entry predicate or endpoint is supplied.
All namespaces are polymorphic. Required inputs come from recipe dependencies.
This does not infer funded lineage from recorded support. The raw path rule is
separate from the stronger corridor/completion certifier. -/
namespace CSTTT.TargetTheory.GenericHandoff.HistoricalAcquisition
open RegisterInterpreter RegisterInitialization

/-- The action at each recorded edge is a raw instruction of the history,
edge index and factor. This allows arbitrary action words, including different
actions on two visits to the same factor; no stationary-policy restriction. -/
def recordedWord {Factor A : Type} (actions : Nat → Factor → A)
    (history : List Factor) : List (A × Factor) :=
  (history.zip (history.drop 1)).mapIdx fun i edge => (actions i edge.1,edge.2)

def RecordedSupport {Factor A : Type} (row : Factor → A → List (Factor × Rat))
    (actions : Nat → Factor → A) (history : List Factor) : Prop :=
  history ≠ [] ∧ ∀ indexed ∈ (history.zip (history.drop 1)).zipIdx,
    ∃ weight, (indexed.1.2,weight) ∈ row indexed.1.1 (actions indexed.2 indexed.1.1) ∧ 0 < weight

theorem recorded_word_terminal {Factor A : Type} (actions : Nat → Factor → A)
    (first : Factor) (rest : List Factor) (default : Factor) :
    HistoricalSupport.fold first (recordedWord actions (first::rest)) =
      (first::rest).getLastD default := by
  have go (z : Factor) (tail : List Factor) (i : Nat) :
      HistoricalSupport.fold z (((z::tail).zip tail).zipIdx i |>.map
        fun indexed => (actions indexed.2 indexed.1.1,indexed.1.2)) =
      (z::tail).getLastD default := by
    induction tail generalizing z i with
    | nil => rfl
    | cons w ws ih =>
      simpa [List.zipIdx_cons,HistoricalSupport.fold,List.getLastD] using ih w (i+1)
  simpa [recordedWord,List.mapIdx_eq_zipIdx_map] using go first rest 0

abbrev ReceiverInput (Factor History Id RouteId : Type) :=
  Factor × List Factor × List Id × History × RouteId

structure Bindings (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A Factor TargetFactor Stage Id History RouteId : Type) where
  histories : StaticView Cell Value (History → List Factor)
  sourceRows : StaticView Cell Value (Factor → A → List (Factor × Rat))
  sourcePolicy : StaticView Cell Value (History → Nat → Factor → A)
  targetCoordinate : StaticView Cell Value (Factor → TargetFactor)
  targetRows : StaticView Cell Value (TargetFactor → A → List (TargetFactor × Rat))
  targetPolicy : StaticView Cell Value (History → Nat → TargetFactor → A)
  routes : CellView Cell Value (RouteId → AcquisitionExecution.Route History Id)
  events : CellView Cell Value (Id → Option (AcquisitionExecution.Event Stage))
  /-- Raw record scan for activation, separate from first-record path lookup.
  The instance fixes the raw eligibility filter; duplicate IDs are allowed. -/
  activationEvents : StaticView Cell Value (List (AcquisitionExecution.Event Stage))
  realized : CellView Cell Value (List Stage)
  receiver : CellView Cell Value AcquisitionExecution.Receiver
  reset : InitialProgram Cell Value R RV (ReceiverInput Factor History Id RouteId)
  response : Expr Cell Value R RV (History × RouteId) (D × A)

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O Factor TargetFactor Stage Id History RouteId : Type)
    extends Bindings Cell Value R RV D A Factor TargetFactor Stage Id History RouteId where
  execution : ResourceRuntime.Execution Cell Value R RV D A O

variable {Cell R D A O Factor TargetFactor Stage Id History RouteId : Type}
  {Value : Cell → Type} {RV : R → Type}

def Raw.dependencies (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId) : List Cell :=
  raw.histories.dependencies ++ raw.sourceRows.dependencies ++ raw.sourcePolicy.dependencies ++
  raw.targetCoordinate.dependencies ++ raw.targetRows.dependencies ++ raw.targetPolicy.dependencies ++
  raw.activationEvents.dependencies ++
  [raw.routes.cell,raw.events.cell,raw.realized.cell,raw.receiver.cell] ++ raw.response.dependencies

def Ready (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  Complete raw.dependencies a ∧ RegisterInitialization.Ready raw.reset a ∧
  Complete raw.execution.row.dependencies a ∧ ProgramReady raw.execution.program a

noncomputable def reset (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a)
    (input : ReceiverInput Factor History Id RouteId) : Registers R RV :=
  RegisterInitialization.initial raw.reset a h.2.1 input

noncomputable def update (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a)
    (x : Registers R RV) (d : D) (act : A) (o : O) : Registers R RV :=
  checkedExecute raw.execution.program a h.2.2.2 x (d,act,o)

def rows (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (x : Registers R RV) (d : D) (act : A) : List (O × Rat) :=
  (raw.execution.row.eval a x (d,act)).getD []

/-- Realized contiguous strict raw steps and typed arrival boundary. Absent
references reject. Past tick/resource fields are not intrinsically consumed. -/
def PathCheck (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (events : Id → Option (AcquisitionExecution.Event Stage))
    (realized : List Stage) (path : List Id) : Prop :=
  ∃ first rest, path = first::rest ∧
    (∃ e, events first = some e ∧ e.fromStage = cfg.entryStage) ∧
    (∀ id ∈ path, id ∈ cfg.eventIds ∧ ∃ e, events id = some e ∧
      e.fromStage ∈ realized ∧ e.toStage ∈ realized ∧
      e.fromStage ∈ cfg.stages ∧ e.toStage ∈ cfg.stages ∧
      e.atomic = true ∧ e.strictStep = true ∧ e.orderAdvance > 0 ∧
      cfg.clock e.toStage = cfg.clock e.fromStage + e.orderAdvance) ∧
    (∀ pair ∈ path.zip (path.drop 1), ∃ e f,
      events pair.1 = some e ∧ events pair.2 = some f ∧ e.toStage = f.fromStage) ∧
    ∃ last e, path.getLast? = some last ∧ events last = some e ∧
      e.toStage = cfg.exitStage ∧ e.targetSupport = true ∧ e.sourceSupport = false

/-- Activation scans every eligible RAW record, not the first record for
an ID or only the selected route. The eligibility projection is a raw
instruction (POS-04 excludes the exit ID, exactly as frozen mixed7). -/
def Activated
    (receiver : AcquisitionExecution.Receiver)
    (records : List (AcquisitionExecution.Event Stage)) (realized : List Stage) : Prop :=
  receiver.sourcePresent = true ∧ receiver.targetFunded = true ∧ receiver.funded = true ∧
    (receiver.mixedRequired = true → ∃ e ∈ records,
      e.fromStage ∈ realized ∧ e.toStage ∈ realized ∧
        e.sourceSupport = true ∧ e.targetSupport = true ∧ e.atomic = true)

def DomainCheck (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId) : Prop :=
  cfg.routes ≠ [] ∧ cfg.histories ≠ [] ∧
  (∀ rid, rid ∈ cfg.routes) ∧ (∀ hist, hist ∈ cfg.histories) ∧
  raw.execution.disturbances ≠ [] ∧ (∀ d, d ∈ raw.execution.disturbances)

/-- Every primitive read succeeds before reception. The terminal is the raw
last factor, never a predictive representative or intended endpoint class. -/
def Arrival (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : RouteId)
    (received : Registers R RV) : Prop :=
  ∃ histories sr sp coordinate tr tp routes events realized receiver first rest,
    raw.histories.read a = some histories ∧ raw.sourceRows.read a = some sr ∧
    raw.sourcePolicy.read a = some sp ∧ raw.targetCoordinate.read a = some coordinate ∧
    raw.targetRows.read a = some tr ∧
    raw.targetPolicy.read a = some tp ∧ raw.routes.read a = some routes ∧
    raw.events.read a = some events ∧ raw.realized.read a = some realized ∧
    raw.receiver.read a = some receiver ∧ rid ∈ cfg.routes ∧
    (routes rid).history ∈ cfg.histories ∧ histories (routes rid).history = first::rest ∧
    RecordedSupport sr (sp (routes rid).history) (first::rest) ∧
    RecordedSupport tr (tp (routes rid).history) ((first::rest).map coordinate) ∧
    PathCheck cfg events realized (routes rid).path ∧
    (∃ records, raw.activationEvents.read a = some records ∧ Activated receiver records realized) ∧
    received = reset raw a h
      (HistoricalSupport.fold first (recordedWord (sp (routes rid).history) (first::rest)),
        first::rest,(routes rid).path,(routes rid).history,rid)

def Entry (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (entry : Registers R RV) : Prop :=
  DomainCheck cfg raw ∧ ∃ rid received routes da o,
    Arrival cfg raw a h rid received ∧ raw.routes.read a = some routes ∧
    raw.response.eval a received ((routes rid).history,rid) = some da ∧
    da.1 ∈ raw.execution.disturbances ∧ da.2 ∈ raw.execution.actions ∧
    StrategyGame.Normalized (rows raw a) received da.1 da.2 ∧
    StrategyGame.PositiveSupport (rows raw a) received da.1 da.2 o ∧
    entry = update raw a h received da.1 da.2 o

theorem arrival_terminal_defined (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : RouteId) (received : Registers R RV)
    (ha : Arrival cfg raw a h rid received) :
    ∃ histories routes first rest, raw.histories.read a = some histories ∧
      raw.routes.read a = some routes ∧ histories (routes rid).history = first::rest ∧
      received = reset raw a h ((first::rest).getLastD first,
        first::rest,(routes rid).path,(routes rid).history,rid) := by
  rcases ha with ⟨histories,sr,sp,coordinate,tr,tp,routes,events,realized,receiver,first,rest,
    hh,hs,hsp,hcoord,ht,htp,hr,he,hreal,hrecv,hrid,hhid,hlist,hss,hts,hp,hact,hreset⟩
  exact ⟨histories,routes,first,rest,hh,hr,hlist,
    hreset.trans (by rw [recorded_word_terminal])⟩

/-- Every ACTUAL supported branch is an entry, including exits/resource
failures. Safety cannot filter the acquisition support. -/
theorem every_supported_branch_is_entry
    (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (domain : DomainCheck cfg raw)
    (rid : RouteId) (received : Registers R RV) (ha : Arrival cfg raw a h rid received)
    (routes : RouteId → AcquisitionExecution.Route History Id)
    (hr : raw.routes.read a = some routes) (da : D × A)
    (hrsp : raw.response.eval a received ((routes rid).history,rid) = some da)
    (hd : da.1 ∈ raw.execution.disturbances) (hact : da.2 ∈ raw.execution.actions)
    (hn : StrategyGame.Normalized (rows raw a) received da.1 da.2) (o : O)
    (hp : StrategyGame.PositiveSupport (rows raw a) received da.1 da.2 o) :
    Entry cfg raw a h (update raw a h received da.1 da.2 o) :=
  ⟨domain,rid,received,routes,da,o,ha,hr,hrsp,hd,hact,hn,hp,rfl⟩

theorem normalized_arrival_has_entry
    (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (domain : DomainCheck cfg raw)
    (rid : RouteId) (received : Registers R RV) (ha : Arrival cfg raw a h rid received)
    (routes : RouteId → AcquisitionExecution.Route History Id)
    (hr : raw.routes.read a = some routes) (da : D × A)
    (hrsp : raw.response.eval a received ((routes rid).history,rid) = some da)
    (hd : da.1 ∈ raw.execution.disturbances) (hact : da.2 ∈ raw.execution.actions)
    (hn : StrategyGame.Normalized (rows raw a) received da.1 da.2) :
    ∃ entry, Entry cfg raw a h entry := by
  obtain ⟨o,ho⟩ := hn.2.2
  exact ⟨_,every_supported_branch_is_entry cfg raw a h domain rid received ha routes hr da hrsp hd hact hn o ho⟩

theorem missing_dependency_rejected (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.dependencies) (hm : a k = none) :
    ¬ Ready raw a := by
  intro h
  have hp := h.1 k hk
  rw [hm] at hp
  contradiction

theorem missing_reset_rejected (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (reg : R) (k : Cell) (hk : k ∈ (raw.reset reg).dependencies)
    (hm : a k = none) : ¬ Ready raw a :=
  fun h => RegisterInitialization.missing_rejected raw.reset a reg k hk hm h.2.1

theorem missing_target_row_rejected (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.execution.row.dependencies)
    (hm : a k = none) : ¬ Ready raw a := by
  intro h
  have hp := h.2.2.1 k hk
  rw [hm] at hp
  contradiction

theorem missing_target_update_rejected (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (reg : R) (k : Cell) (hk : k ∈ (raw.execution.program reg).dependencies)
    (hm : a k = none) : ¬ Ready raw a :=
  fun h => missing_program_rejected raw.execution.program a reg k hk hm h.2.2.2

theorem missing_source_rows_no_entry (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (entry : Registers R RV) (hm : raw.sourceRows.read a = none) :
    ¬ ∃ h : Ready raw a, Entry cfg raw a h entry := by
  rintro ⟨h,_,rid,received,routes,da,o,ha,_⟩
  rcases ha with ⟨_,sr,_,_,_,_,_,_,_,_,_,_,_,hs,_⟩
  rw [hm] at hs
  contradiction

theorem source_absent_no_entry (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (receiver : AcquisitionExecution.Receiver)
    (hr : raw.receiver.read a = some receiver) (absent : receiver.sourcePresent = false)
    (entry : Registers R RV) : ¬ Entry cfg raw a h entry := by
  rintro ⟨_,rid,received,routes,da,o,ha,_⟩
  rcases ha with ⟨_,_,_,_,_,_,_,_,_,rec,_,_,_,_,_,_,_,_,_,_,_,hrecv,_,_,_,_,_,_,hact,_⟩
  have he := Option.some.inj (hrecv.symm.trans hr)
  subst rec
  obtain ⟨records,_,act⟩ := hact
  have := act.1
  rw [absent] at this
  contradiction

theorem unrealized_path_no_arrival (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : RouteId)
    (routes : RouteId → AcquisitionExecution.Route History Id)
    (events : Id → Option (AcquisitionExecution.Event Stage)) (realized : List Stage)
    (hr : raw.routes.read a = some routes) (he : raw.events.read a = some events)
    (hs : raw.realized.read a = some realized) (id : Id) (hi : id ∈ (routes rid).path)
    (event : AcquisitionExecution.Event Stage) (hev : events id = some event)
    (bad : event.toStage ∉ realized) (received : Registers R RV) :
    ¬ Arrival cfg raw a h rid received := by
  rintro ⟨_,_,_,_,_,_,rs,es,ss,_,_,_,_,_,_,_,_,_,hrs,hes,hss,_,_,_,_,_,_,hp,_⟩
  have hr' := Option.some.inj (hrs.symm.trans hr)
  have he' := Option.some.inj (hes.symm.trans he)
  have hs' := Option.some.inj (hss.symm.trans hs)
  subst rs; subst es; subst ss
  rcases hp with ⟨_,_,_,_,hall,_⟩
  obtain ⟨_,e,heq,_,hen,_⟩ := hall id hi
  have ee := Option.some.inj (heq.symm.trans hev)
  subst e
  exact bad hen

/-- Missing views reject existence of an entry, not readiness conjoined
with an incompatible absence. Covers EVERY static consumed view. -/
theorem missing_view_no_entry (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (entry : Registers R RV)
    (hm : raw.histories.read a = none ∨ raw.sourceRows.read a = none ∨
      raw.sourcePolicy.read a = none ∨ raw.targetCoordinate.read a = none ∨
      raw.targetRows.read a = none ∨
      raw.targetPolicy.read a = none ∨ raw.routes.read a = none ∨
      raw.events.read a = none ∨ raw.realized.read a = none ∨ raw.receiver.read a = none) :
    ¬ ∃ h : Ready raw a, Entry cfg raw a h entry := by
  rintro ⟨h,_,rid,received,routes,da,o,ha,_⟩
  rcases ha with ⟨hs,sr,sp,coordinate,tr,tp,rs,es,ss,rec,first,rest,
    hh,hsr,hsp,hcoordinate,htr,htp,hrs,hev,hreal,hrec,_⟩
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;> simp_all

/-- A deleted/zero-support recorded source edge rejects actual reception.
The premise breaks one raw edge condition, not a stored acceptance field. -/
theorem unsupported_source_edge_no_arrival
    (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : RouteId)
    (histories : History → List Factor) (routes : RouteId → AcquisitionExecution.Route History Id)
    (sr : Factor → A → List (Factor × Rat)) (sp : History → Nat → Factor → A)
    (hh : raw.histories.read a = some histories) (hr : raw.routes.read a = some routes)
    (hs : raw.sourceRows.read a = some sr) (hp : raw.sourcePolicy.read a = some sp)
    (edge : (Factor × Factor) × Nat)
    (he : edge ∈ ((histories (routes rid).history).zip
      ((histories (routes rid).history).drop 1)).zipIdx)
    (bad : ∀ w, (edge.1.2,w) ∈ sr edge.1.1 (sp (routes rid).history edge.2 edge.1.1) → ¬ 0 < w)
    (received : Registers R RV) : ¬ Arrival cfg raw a h rid received := by
  rintro ⟨hist,srows,policy,coordinate,tr,tp,rs,es,ss,rec,first,rest,
    hhist,hsrows,hpolicy,_,_,_,hrs,_,_,_,_,_,hlist,hsource,_⟩
  have eh := Option.some.inj (hhist.symm.trans hh)
  have er := Option.some.inj (hrs.symm.trans hr)
  have es := Option.some.inj (hsrows.symm.trans hs)
  have ep := Option.some.inj (hpolicy.symm.trans hp)
  subst hist; subst rs; subst srows; subst policy
  rw [hlist] at he
  obtain ⟨w,hw,hwpos⟩ := hsource.2 edge he
  exact bad w hw hwpos

theorem empty_disturbances_no_entry
    (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (entry : Registers R RV)
    (empty : raw.execution.disturbances = []) : ¬ Entry cfg raw a h entry := by
  intro he
  exact he.1.2.2.2.2.1 empty

/-- Missing activation records reject an entry without assuming compatible
readiness beside an absent view. The raw activation instruction is consumed. -/
theorem missing_activation_no_entry (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (a : Assignment Cell Value) (entry : Registers R RV)
    (hm : raw.activationEvents.read a = none) :
    ¬ ∃ h : Ready raw a, Entry cfg raw a h entry := by
  rintro ⟨h,_,rid,received,routes,da,o,ha,_⟩
  rcases ha with ⟨hist,sr,sp,coord,tr,tp,rs,es,ss,recv,first,rest,
    hh,hs,hsp,hcoord,ht,htp,hr,he,hreal,hrecv,hrid,hhid,hlist,hss,hts,hpath,activation,hreset⟩
  obtain ⟨records,hr,_⟩ := activation
  rw [hm] at hr
  contradiction

/-- All-record semantics retains a mixed witness even when an earlier record
with the same ID is not mixed. No ID-uniqueness premise occurs. -/
theorem activated_append_right (receiver : AcquisitionExecution.Receiver)
    (before records : List (AcquisitionExecution.Event Stage)) (realized : List Stage)
    (h : Activated receiver records realized) : Activated receiver (before ++ records) realized := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro req
  obtain ⟨e,he,hrest⟩ := h.2.2.2 req
  exact ⟨e,List.mem_append_right _ he,hrest⟩

theorem no_mixed_record_rejected (receiver : AcquisitionExecution.Receiver)
    (records : List (AcquisitionExecution.Event Stage)) (realized : List Stage)
    (required : receiver.mixedRequired = true)
    (broken : ∀ e ∈ records, e.sourceSupport = false) : ¬ Activated receiver records realized := by
  intro h
  obtain ⟨e,he,_,_,hs,_⟩ := h.2.2.2 required
  have hb := broken e he
  rw [hb] at hs
  contradiction

/-- Missing event references cannot use a canonical event fallback. -/
theorem missing_event_rejected (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (events : Id → Option (AcquisitionExecution.Event Stage)) (realized : List Stage)
    (path : List Id) (id : Id) (hi : id ∈ path) (hm : events id = none) :
    ¬ PathCheck cfg events realized path := by
  rintro ⟨_,_,_,_,hall,_⟩
  obtain ⟨_,e,he,_⟩ := hall id hi
  rw [hm] at he
  contradiction

theorem nonstrict_event_rejected (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    (events : Id → Option (AcquisitionExecution.Event Stage)) (realized : List Stage)
    (path : List Id) (id : Id) (hi : id ∈ path) (e : AcquisitionExecution.Event Stage)
    (he : events id = some e) (bad : e.strictStep = false) : ¬ PathCheck cfg events realized path := by
  rintro ⟨_,_,_,_,hall,_⟩
  obtain ⟨_,f,hf,_,_,_,_,_,hs,_⟩ := hall id hi
  have ef := Option.some.inj (hf.symm.trans he)
  subst f
  rw [bad] at hs
  contradiction

/-- Locality includes reset and actual target updates, not merely static
arrival displays. Arbitrary unconsumed source-context cells may differ. -/
theorem locality (raw : Raw Cell Value R RV D A O Factor TargetFactor Stage Id History RouteId)
    (cfg : AcquisitionExecution.Schema Stage Id History RouteId)
    {a b : Assignment Cell Value} (ha : Ready raw a) (hb : Ready raw b)
    (hdeps : Agrees raw.dependencies a b)
    (hreset : ∀ reg, Agrees (raw.reset reg).dependencies a b)
    (hrows : Agrees raw.execution.row.dependencies a b)
    (hupdate : ∀ reg, Agrees (raw.execution.program reg).dependencies a b)
    (entry : Registers R RV) : Entry cfg raw a ha entry ↔ Entry cfg raw b hb entry := by
  have hs : raw.histories.read a = raw.histories.read b := raw.histories.locality (by
    intro k hk; exact hdeps k (by simp [Raw.dependencies,hk]))
  have hsr : raw.sourceRows.read a = raw.sourceRows.read b := raw.sourceRows.locality (by
    intro k hk; exact hdeps k (by simp [Raw.dependencies,hk]))
  have hsp : raw.sourcePolicy.read a = raw.sourcePolicy.read b := raw.sourcePolicy.locality (by
    intro k hk; exact hdeps k (by simp [Raw.dependencies,hk]))
  have hcoordinate : raw.targetCoordinate.read a = raw.targetCoordinate.read b := raw.targetCoordinate.locality (by
    intro k hk; exact hdeps k (by simp [Raw.dependencies,hk]))
  have htr : raw.targetRows.read a = raw.targetRows.read b := raw.targetRows.locality (by
    intro k hk; exact hdeps k (by simp [Raw.dependencies,hk]))
  have htp : raw.targetPolicy.read a = raw.targetPolicy.read b := raw.targetPolicy.locality (by
    intro k hk; exact hdeps k (by simp [Raw.dependencies,hk]))
  have hrs : raw.routes.read a = raw.routes.read b := view_locality _ (hdeps _ (by simp [Raw.dependencies]))
  have hev : raw.events.read a = raw.events.read b := view_locality _ (hdeps _ (by simp [Raw.dependencies]))
  have hactivation : raw.activationEvents.read a = raw.activationEvents.read b := raw.activationEvents.locality (by
    intro k hk; exact hdeps k (by simp [Raw.dependencies,hk]))
  have hrl : raw.realized.read a = raw.realized.read b := view_locality _ (hdeps _ (by simp [Raw.dependencies]))
  have hrc : raw.receiver.read a = raw.receiver.read b := view_locality _ (hdeps _ (by simp [Raw.dependencies]))
  have hrsp (x : Registers R RV) (env : History × RouteId) :
      raw.response.eval a x env = raw.response.eval b x env := raw.response.locality (by
    intro k hk; exact hdeps k (List.mem_append_right _ hk)) x env
  have hrst (input : ReceiverInput Factor History Id RouteId) : reset raw a ha input = reset raw b hb input :=
    RegisterInitialization.initial_locality _ ha.2.1 hb.2.1 hreset input
  have hrow (x : Registers R RV) (d : D) (act : A) : rows raw a x d act = rows raw b x d act := by
    simp only [rows,raw.execution.row.locality hrows x (d,act)]
  have hup (x : Registers R RV) (d : D) (act : A) (o : O) : update raw a ha x d act o = update raw b hb x d act o := by
    funext reg
    apply Option.some.inj
    unfold update
    rw [← checked_execute_eq raw.execution.program a ha.2.2.2 x (d,act,o) reg,
      ← checked_execute_eq raw.execution.program b hb.2.2.2 x (d,act,o) reg]
    exact (raw.execution.program reg).locality (hupdate reg) x (d,act,o)
  have rowFun : rows raw a = rows raw b := by
    funext x d act
    exact hrow x d act
  simp only [Entry,Arrival,hs,hsr,hsp,hcoordinate,htr,htp,hrs,hev,hactivation,hrl,hrc,hrsp,hrst,rowFun,hup]

end CSTTT.TargetTheory.GenericHandoff.HistoricalAcquisition
