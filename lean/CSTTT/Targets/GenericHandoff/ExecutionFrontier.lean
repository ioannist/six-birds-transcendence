import CSTTT.Targets.GenericHandoff.AcquisitionExecution
import CSTTT.Targets.GenericHandoff.RegisterReadoutLaws
import CSTTT.Targets.GenericHandoff.FutureLumping

/-! G6d-4b execution boundary. Every audit run is an actual instruction fold
from a raw initializer and an assigned history. The temporal interpreter uses
the acquisition's SAME rows and updater. No snapshot, future, code, observer,
weight, successor, or closure is a supplied object. This does not yet certify
the atomic corridor, typed bridge laws, or the enclosing RawHandoff. -/
namespace CSTTT.TargetTheory.GenericHandoff.ExecutionFrontier
open RegisterInterpreter CSTTT.TransportTheory

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O P Residue Maintenance Stage Id History RouteId : Type) where
  acquisition : AcquisitionExecution.Raw Cell Value R RV D A O Stage Id History RouteId
  readouts : RegisterFuture.Readouts Cell Value R RV P Residue Maintenance
  recipes : RegisterFuture.StepRecipes Cell Value R RV D A O P Residue Maintenance
  tickPeriod : Nat
  audit : List (History × Nat)
  schema : AcquisitionExecution.Schema Stage Id History RouteId
  auditRoute : History × Nat → RouteId

variable {Cell R D A O P Residue Maintenance Stage Id History RouteId : Type}
    {Value : Cell → Type} {RV : R → Type}

def temporal (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId) :
    RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance :=
  ⟨raw.acquisition.execution.outcomes,raw.acquisition.execution.actions,
    raw.acquisition.execution.disturbances,raw.tickPeriod,raw.acquisition.execution.row,
    raw.acquisition.execution.program,raw.readouts⟩

def Ready (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  AcquisitionExecution.Ready raw.acquisition a ∧ RegisterFuture.RawReady (temporal raw) a

noncomputable def initial (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (hist : History) : Registers R RV :=
  AcquisitionExecution.initial raw.acquisition a h.1 hist

noncomputable def roots (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) : List (Registers R RV) :=
  raw.audit.map (fun i => initial raw a h i.1)

/-- The helper default is never an acceptance path: Ready requires the
history cell, and AuditCheck additionally demands its actual decoded value. -/
def historyPrefix (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (i : History × Nat) : List (D × A × O) :=
  (((raw.acquisition.histories.read a).getD (fun _ => [])) i.1).take i.2

noncomputable def snapshot (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (i : History × Nat) : Registers R RV :=
  AcquisitionExecution.foldHistory raw.acquisition a h.1 (initial raw a h i.1) (historyPrefix raw a i)

noncomputable def observation (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (i : History × Nat) :=
  RegisterFuture.observation (temporal raw) a h.2 (snapshot raw a h i)

variable [DecidableEq O]

/-- Both the actual raw branch and its aggregated future probability are
checked. A positive list entry cannot hide cancellation in a malformed row. -/
noncomputable def PrefixCheck
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) : Registers R RV → List (D × A × O) → Prop
  | _, [] => True
  | r, (d,act,o)::rest =>
    d ∈ raw.acquisition.execution.disturbances ∧ act ∈ raw.acquisition.execution.actions ∧
    o ∈ raw.acquisition.execution.outcomes ∧
    StrategyGame.PositiveSupport (AcquisitionExecution.rows raw.acquisition a) r d act o ∧
    RegisterFuture.weight (temporal raw) a h.2 r (d,act) o > 0 ∧
    PrefixCheck raw a h (AcquisitionExecution.update raw.acquisition a h.1 r d act o) rest

def AuditCheck
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) : Prop :=
  raw.audit ≠ [] ∧ ∃ histories, raw.acquisition.histories.read a = some histories ∧
    (∀ i ∈ raw.audit, 0 < i.2 ∧ i.2 ≤ (histories i.1).length ∧
      PrefixCheck raw a h (initial raw a h i.1) (historyPrefix raw a i)) ∧
    (∀ hist ∈ raw.schema.histories, ∃ i ∈ raw.audit, i.1 = hist ∧ i.2 = (histories hist).length)

abbrev Closure
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) :=
  RegisterFuture.Closure (temporal raw) a h.2 (roots raw a h)

omit [DecidableEq O] in
theorem updater_shared
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (r : Registers R RV) (d : D) (act : A) (o : O) :
    RegisterFuture.next (temporal raw) a h.2 r (d,act) o =
      AcquisitionExecution.update raw.acquisition a h.1 r d act o := rfl

omit [DecidableEq O] in
theorem rows_shared
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (r : Registers R RV) (d : D) (act : A) :
    RegisterFuture.row (temporal raw) a h.2 r (d,act) =
      AcquisitionExecution.rows raw.acquisition a r d act := by
  unfold AcquisitionExecution.rows
  have he := RegisterFuture.row_eq (temporal raw) a h.2 r (d,act)
  change raw.acquisition.execution.row.eval a r (d,act) = _ at he
  rw [he]
  rfl

theorem prefix_executes
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (r : Registers R RV) (word : List (D × A × O))
    (hc : PrefixCheck raw a h r word) :
    AcquisitionExecution.HistoryExecution raw.acquisition a h.1 r word
      (AcquisitionExecution.foldHistory raw.acquisition a h.1 r word) := by
  induction word generalizing r with
  | nil => exact .nil r
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    exact .step hc.1 hc.2.1 hc.2.2.2.1 (ih _ hc.2.2.2.2.2)

theorem prefix_in_closure
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (r : Registers R RV) (word : List (D × A × O))
    (hr : Closure raw a h r) (hc : PrefixCheck raw a h r word) :
    Closure raw a h (AcquisitionExecution.foldHistory raw.acquisition a h.1 r word) := by
  induction word generalizing r with
  | nil => exact hr
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    apply ih _ _ hc.2.2.2.2.2
    have hn := FutureClosure.step hr (d,act) o hc.2.2.1
    simpa only [RegisterFuture.dynamics,updater_shared] using hn

theorem snapshot_execution
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (ha : AuditCheck raw a h)
    (i : History × Nat) (hi : i ∈ raw.audit) :
    AcquisitionExecution.HistoryExecution raw.acquisition a h.1 (initial raw a h i.1)
      (historyPrefix raw a i) (snapshot raw a h i) ∧ Closure raw a h (snapshot raw a h i) := by
  obtain ⟨histories,hh,hchecks,_⟩ := ha.2
  have hc := (hchecks i hi).2.2
  exact ⟨prefix_executes raw a h _ _ hc,
    prefix_in_closure raw a h _ _ (FutureClosure.root _ (List.mem_map.mpr ⟨i,hi,rfl⟩)) hc⟩

theorem snapshot_prefix_nonempty
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (ha : AuditCheck raw a h)
    (i : History × Nat) (hi : i ∈ raw.audit) : historyPrefix raw a i ≠ [] := by
  obtain ⟨histories,hh,hchecks,_⟩ := ha.2
  have hc := hchecks i hi
  intro he
  have hl := congrArg List.length he
  simp only [historyPrefix,hh,Option.getD_some,List.length_take,List.length_nil] at hl
  omega

noncomputable def frozen
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
    (i : Audited raw.audit) : TemporalSignature (snapshotAlphabet raw.audit (observation raw a h)) :=
  frozenSnapshot (RegisterFuture.future (temporal raw) a h.2) raw.audit (observation raw a h) i

theorem codec_roundtrip
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
    (i : Audited raw.audit) :
    decodeFrozenSnapshot raw.audit (observation raw a h) (frozen raw a h i) =
      RegisterFuture.observation (temporal raw) a h.2 (snapshot raw a h i.val) := rfl

variable [DecidableEq Stage]

/-- Availability belongs to this frame gate itself. Mere presence of events
cannot certify a snapshot on an unrealized route or an inactive receiver. -/
def PathsAvailable
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  ∃ routes events realized receiver,
    raw.acquisition.routes.read a = some routes ∧ raw.acquisition.events.read a = some events ∧
    raw.acquisition.realized.read a = some realized ∧ raw.acquisition.receiver.read a = some receiver ∧
    ∀ i ∈ raw.audit, raw.auditRoute i ∈ raw.schema.routes ∧ (routes (raw.auditRoute i)).history = i.1 ∧
      AcquisitionExecution.PathCheck raw.schema events realized (routes (raw.auditRoute i)).path ∧
      AcquisitionExecution.Activated receiver events realized (routes (raw.auditRoute i)).path

/-- Actual outcome and action coverage is structural finite-interface data.
An omitted positive branch must not disappear from the future's sum. -/
def ExecutionDomain
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId) : Prop :=
  raw.acquisition.execution.outcomes.Nodup ∧
    (∀ o, o ∈ raw.acquisition.execution.outcomes) ∧ (∀ act, act ∈ raw.acquisition.execution.actions)

/-- Every interpreted future row is a subprobability row: an unavailable
response may have mass zero. This ranges over the whole computed closure. -/
def RowLawGate
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) : Prop :=
  ∀ x, Closure raw a h x → ∀ d ∈ raw.acquisition.execution.disturbances,
    ∀ act ∈ raw.acquisition.execution.actions,
      (∀ e ∈ AcquisitionExecution.rows raw.acquisition a x d act, 0 ≤ e.2) ∧
      let mass := ((AcquisitionExecution.rows raw.acquisition a x d act).map Prod.snd).sum
      mass = 0 ∨ mass = 1

/-- The signature's future proposition is about the shared execution, with
unbounded words; the independently interpreted update recipes gate its closure. -/
def Valid
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance] : Prop :=
  ∃ h : Ready raw a, AuditCheck raw a h ∧
    AcquisitionExecution.DomainCheck raw.schema raw.acquisition ∧ ExecutionDomain raw ∧ PathsAvailable raw a ∧
    FutureLumping.OneStep (RegisterFuture.future (temporal raw) a h.2) ∧
    RegisterFuture.ReadoutLawGate (temporal raw) raw.recipes a h.2 (roots raw a h) ∧ RowLawGate raw a h

theorem soundness
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
    (hv : Valid raw a) :
    ∃ h : Ready raw a, (∃ r, Closure raw a h r) ∧
      FullFutureSufficient (RegisterFuture.future (temporal raw) a h.2) ∧
      RegisterFuture.ReadoutLawGate (temporal raw) raw.recipes a h.2 (roots raw a h) ∧
      RowLawGate raw a h ∧
      ∀ i : Audited raw.audit,
        Closure raw a h (snapshot raw a h i.val) ∧
        (frozen raw a h i).predictiveNow.futureSufficient ∧
        decodeFrozenSnapshot raw.audit (observation raw a h) (frozen raw a h i) = observation raw a h i.val := by
  obtain ⟨h,ha,_,_,_,hb,hl,hr⟩ := hv
  have hf := FutureLumping.all_words (RegisterFuture.future (temporal raw) a h.2) hb
  obtain ⟨i⟩ := audited_nonempty raw.audit ha.1
  exact ⟨h,⟨_,(snapshot_execution raw a h ha i.val i.property).2⟩,hf,hl,hr,
    fun j => ⟨(snapshot_execution raw a h ha j.val j.property).2,hf,rfl⟩⟩

theorem missing_atomic_view
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
    (hm : raw.acquisition.events.read a = none) : ¬ Valid raw a := by
  rintro ⟨h,_⟩
  have hc := h.1.1 raw.acquisition.events.cell (by simp [AcquisitionExecution.Raw.dependencies])
  cases he : a raw.acquisition.events.cell <;> simp_all [CellView.read]

theorem missing_consumed_input
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
    (k : Cell) (hk : k ∈ raw.acquisition.dependencies) (hm : a k = none) : ¬ Valid raw a :=
  fun ⟨h,_⟩ => AcquisitionExecution.missing_dependency_rejected raw.acquisition a k hk hm h.1

theorem inactive_receiver_rejected
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
    (receiver : AcquisitionExecution.Receiver) (he : raw.acquisition.receiver.read a = some receiver)
    (f : AcquisitionExecution.ActivationField) (bad : AcquisitionExecution.activationField receiver f = false) :
    ¬ Valid raw a := by
  rintro ⟨h,ha,_,_,⟨rs,es,realized,rec,_,_,_,hrec,hpaths⟩,_,_,_⟩
  obtain ⟨i⟩ := audited_nonempty raw.audit ha.1
  have heq := Option.some.inj (hrec.symm.trans he)
  subst rec
  have hg := AcquisitionExecution.activated_fields receiver es realized _ (hpaths i.val i.property).2.2.2 f
  rw [bad] at hg
  contradiction

theorem unrealized_path_rejected
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
    (routes : RouteId → AcquisitionExecution.Route History Id) (events : Id → AcquisitionExecution.Event Stage)
    (realized : List Stage) (hr : raw.acquisition.routes.read a = some routes)
    (he : raw.acquisition.events.read a = some events) (hs : raw.acquisition.realized.read a = some realized)
    (i : History × Nat) (hi : i ∈ raw.audit) (id : Id) (hid : id ∈ (routes (raw.auditRoute i)).path)
    (bad : (events id).toStage ∉ realized) : ¬ Valid raw a := by
  rintro ⟨h,ha,_,_,⟨rs,es,ss,rec,hrs,hes,hss,_,hpaths⟩,_,_,_⟩
  have hreq := Option.some.inj (hrs.symm.trans hr)
  have heeq := Option.some.inj (hes.symm.trans he)
  have hseq := Option.some.inj (hss.symm.trans hs)
  subst rs; subst es; subst ss
  obtain ⟨_,_,_,_,hall,_⟩ := (hpaths i hi).2.2.1
  exact bad (hall id hid).2.1

/-- The whole-closure guard ranges over EVERY readout field. Only its raw
instruction changes; the shared execution, audit and recipes stay fixed. -/
def replaceReadout
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (f : RegisterFuture.Field) (e : Expr Cell Value R RV Unit (RegisterFuture.FieldValue P Residue Maintenance f)) :=
  {raw with readouts := raw.readouts.replace f e}

theorem constant_readout_rejected
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
    (h : Ready raw a) (x : Registers R RV) (hx : Closure raw a h x)
    (d : D) (hd : d ∈ raw.acquisition.execution.disturbances)
    (act : A) (hac : act ∈ raw.acquisition.execution.actions)
    (o : O) (ho : o ∈ raw.acquisition.execution.outcomes) (f : RegisterFuture.Field)
    (expected wrong : RegisterFuture.FieldValue P Residue Maintenance f)
    (rhs : (raw.recipes f).eval a x (d,act,o) = some expected) (bad : wrong ≠ expected) :
    ¬ Valid (replaceReadout raw f (.literal wrong)) a := by
  rintro ⟨hn,_,_,_,_,_,hl,_⟩
  have hnew : RegisterFuture.RawReady (RegisterFuture.replaceReadout (temporal raw) f (.literal wrong)) a := hn.2
  have hg := RegisterFuture.constant_field_guard (temporal raw) raw.recipes a h.2
    (roots raw a h) x hx d hd act hac o ho f expected wrong rhs bad hnew
  exact hg hl

/-- General one-field law guard, allowing a capped expression that agrees
at the audit roots. Its counterexample must be in the ACTUAL full closure. -/
theorem readout_mismatch_rejected
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
    (h : Ready raw a) (x : Registers R RV) (hx : Closure raw a h x)
    (d : D) (hd : d ∈ raw.acquisition.execution.disturbances)
    (act : A) (ha : act ∈ raw.acquisition.execution.actions)
    (o : O) (ho : o ∈ raw.acquisition.execution.outcomes) (f : RegisterFuture.Field)
    (proposal : Expr Cell Value R RV Unit (RegisterFuture.FieldValue P Residue Maintenance f))
    (hn : Ready (replaceReadout raw f proposal) a)
    (bad : ¬ RegisterFuture.FieldLaw (temporal (replaceReadout raw f proposal)) raw.recipes a hn.2 x (d,act) o f) :
    ¬ Valid (replaceReadout raw f proposal) a := by
  rintro ⟨hnew,_,_,_,_,_,hl,_⟩
  exact RegisterFuture.field_guard (temporal (replaceReadout raw f proposal)) raw.recipes a hn.2
    (roots raw a h) x hx d hd act ha o ho f bad hl

end CSTTT.TargetTheory.GenericHandoff.ExecutionFrontier
