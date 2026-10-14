import CSTTT.Targets.GenericHandoff.ClauseDispatcher
import CSTTT.Targets.GenericHandoff.RegisterFuture
import CSTTT.Targets.GenericHandoff.TemporalFactorClosure
import CSTTT.Targets.GenericHandoff.FutureReindex

/-! Checked clause/runtime binding, not an assumption that arbitrary recipes
factor. Both futures, their probabilities, code and observer are DEFINED from
the same assignment and raw clause/runtime instructions. The projection is a
raw instruction; its simulation laws range over ALL run contexts and every
actual outcome. This is a potentially incomplete finite-clause certifier under
the hybrid architecture, not the final RawHandoff or a finite-context premise.
-/
namespace CSTTT.TargetTheory.GenericHandoff.TemporalRuntimeCoherence
open RegisterInterpreter CSTTT.TransportTheory

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (S A O H RouteId Stage Id Owner D : Type) where
  schema : TemporalFactorRules.Schema S A O H RouteId Stage Id Owner
  bindings : TemporalFactorCells.Bindings Cell Value S A O H RouteId Stage Id Owner
  runtime : RegisterFuture.Raw Cell Value R RV D A O
    (TemporalFactorRules.Predictive O) (List S × List Id) Bool
  projection : Expr Cell Value R RV Unit (TemporalFactorRules.Run O S Id)
  owner : Owner → CarrierId

variable {Cell R S A O H RouteId Stage Id Owner D : Type}
  {Value : Cell → Type} {RV : R → Type}

def Ready (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) : Prop :=
  (∃ d, TemporalFactorCells.decoded m.bindings a = some d) ∧
  RegisterFuture.RawReady m.runtime a ∧ Complete m.projection.dependencies a

noncomputable def data (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) := Classical.choose h.1

theorem decoded_data (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) :
    TemporalFactorCells.decoded m.bindings a = some (data m a h) := Classical.choose_spec h.1

noncomputable def project (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (x : Registers R RV) :=
  RegisterFuture.read m.projection a h.2.2 x

def observationImage (owner : Owner → CarrierId)
    (v : TemporalFactorRules.Observation O S Id Owner) :
    TemporalSnapshotReadout (TemporalFactorRules.Predictive O) (List S × List Id) Bool :=
  ⟨v.predictive,v.order,v.tickPhase,v.progress,v.record,v.residue,v.maintenance,owner v.owner⟩

def codeImage (owner : Owner → CarrierId) (v : TemporalFactorRules.Code O S Id Owner) :
    TemporalRunCode (TemporalFactorRules.Predictive O) (List S × List Id) Bool :=
  ⟨v.predictive,v.counter,v.tickPhase,v.residue,v.funded,owner v.owner⟩

theorem observationImage_injective (owner : Owner → CarrierId) (hi : Function.Injective owner) :
    Function.Injective (observationImage (O := O) (S := S) (Id := Id) owner) := by
  intro x y he
  have hp := congrArg TemporalSnapshotReadout.predictive he
  have hn := congrArg TemporalSnapshotReadout.order he
  have ht := congrArg TemporalSnapshotReadout.tickPhase he
  have hg := congrArg TemporalSnapshotReadout.progress he
  have hr := congrArg TemporalSnapshotReadout.record he
  have hs := congrArg TemporalSnapshotReadout.residue he
  have hm := congrArg TemporalSnapshotReadout.maintenance he
  have ho := hi (congrArg TemporalSnapshotReadout.owner he)
  cases x; cases y; simp_all [observationImage]

theorem codeImage_injective (owner : Owner → CarrierId) (hi : Function.Injective owner) :
    Function.Injective (codeImage (O := O) (S := S) (Id := Id) owner) := by
  intro x y he
  have hp := congrArg TemporalRunCode.predictive he
  have hn := congrArg TemporalRunCode.order he
  have ht := congrArg TemporalRunCode.tickPhase he
  have hs := congrArg TemporalRunCode.residue he
  have hm := congrArg TemporalRunCode.maintenance he
  have ho := hi (congrArg TemporalRunCode.owner he)
  cases x; cases y; simp_all [codeImage]

variable [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage]
  [DecidableEq Id]

noncomputable def clauseFuture (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) :=
  TemporalFactorRules.future m.schema (data m a h) m.runtime.tickPeriod

/-- List equality preserves every actual branch, not just class totals.
Unbounded counters and ledger context are retained by the actual updater.
Writer and absolute ticks are checked in addition to the eight observations.
Every field is an equation on interpreted raw data, not a stored verdict. -/
structure Laws (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) : Prop where
  ownerInjective : Function.Injective m.owner
  outcomes : m.runtime.outcomes = m.schema.base.outcomes
  rows : ∀ x da, RegisterFuture.row m.runtime a h.2.1 x da =
    TemporalFactorRules.actualRows m.schema (data m a h) (project m a h x) da.2
  successor : ∀ x da o, project m a h (RegisterFuture.next m.runtime a h.2.1 x da o) =
    TemporalFactorRules.update m.schema (data m a h) (project m a h x) da.2 o
  observation : ∀ x, RegisterFuture.observation m.runtime a h.2.1 x =
    observationImage m.owner (TemporalFactorRules.observe m.schema (data m a h)
      m.runtime.tickPeriod (project m a h x))
  ticks : ∀ x, m.runtime.readouts.ticks.eval a x () = some (project m a h x).ticks
  writer : ∀ x, m.runtime.readouts.writer.eval a x () =
    some (TemporalFactorRules.writer m.schema (data m a h) (project m a h x).residue)
  roots : ∀ p ∈ TemporalFactorRules.roots m.schema (data m a h),
    ∃ x, project m a h x = p

def Valid (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) : Prop :=
  ∃ h : Ready m a, TemporalFactorRules.Accept m.schema (data m a h) ∧ Laws m a h

/-- The enclosing dispatcher can require this exact constructor equation;
there is no independently supplied clause acceptance function. -/
def rule (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D) : ClauseDispatcher.Rule Cell Value .c6 :=
  .c6 inferInstance inferInstance inferInstance inferInstance inferInstance m.schema m.bindings

theorem valid_clause (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (hv : Valid m a) : (rule m).accept a := by
  obtain ⟨h,ha,_⟩ := hv
  exact ⟨data m a h,decoded_data m a h,ha⟩

omit [DecidableEq Stage] in
theorem weight_link (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (laws : Laws m a h)
    (x : Registers R RV) (da : D × A) (o : O) :
    RegisterFuture.weight m.runtime a h.2.1 x da o =
      (clauseFuture m a h).weight (project m a h x) da.2 o := by
  unfold RegisterFuture.weight
  rw [laws.rows]
  change _ = (((TemporalFactorRules.actualRows m.schema (data m a h) (project m a h x) da.2).filter fun e => decide (e.1 = o)).map Prod.snd).sum
  generalize TemporalFactorRules.actualRows m.schema (data m a h) (project m a h x) da.2 = xs
  induction xs with
  | nil => rfl
  | cons e es ih =>
    by_cases he : e.1 = o <;> simp [he,ih,Rat.zero_add]

omit [DecidableEq Stage] in
theorem code_link (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (laws : Laws m a h)
    (x : Registers R RV) :
    (RegisterFuture.future m.runtime a h.2.1).code x =
      codeImage m.owner ((clauseFuture m a h).code (project m a h x)) := by
  change bridgeCodeOfObservation (RegisterFuture.observation m.runtime a h.2.1 x) = _
  rw [laws.observation]
  rfl

variable [DecidableEq Owner]

omit [DecidableEq Stage] in
/-- Exact full-observation word law on ALL runtime states. The word is not
bounded and actual outcome labels/weights are not quotient representatives. -/

theorem word_law (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (laws : Laws m a h)
    (x : Registers R RV) (word : List (D × A))
    (trace : List (TemporalFactorRules.Observation O S Id Owner)) :
    fullFuture (RegisterFuture.future m.runtime a h.2.1) x word (trace.map (observationImage m.owner)) =
      fullFuture (clauseFuture m a h) (project m a h x) (word.map Prod.snd) trace :=
  FutureReindex.mapped_word_law (clauseFuture m a h) (RegisterFuture.future m.runtime a h.2.1)
    (project m a h) Prod.snd (observationImage m.owner)
    (fun _ _ he => observationImage_injective m.owner laws.ownerInjective he)
    laws.outcomes laws.observation (weight_link m a h laws) laws.successor x word trace

theorem soundness (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (hv : Valid m a) :
    ∃ h : Ready m a, FullFutureSufficient (RegisterFuture.future m.runtime a h.2.1) := by
  obtain ⟨h,ha,laws⟩ := hv
  refine ⟨h,?_⟩
  exact FutureReindex.sufficient_transport (clauseFuture m a h)
    (RegisterFuture.future m.runtime a h.2.1) (project m a h) Prod.snd
    (observationImage m.owner) (fun _ _ he => observationImage_injective m.owner laws.ownerInjective he)
    laws.outcomes laws.observation (weight_link m a h laws) laws.successor
    (fun x y hc => codeImage_injective m.owner laws.ownerInjective (by
      simpa only [code_link m a h laws] using hc))
    (TemporalFactorRules.all_words m.schema (data m a h) m.runtime.tickPeriod ha)

omit [DecidableEq Owner] in
/-- Actual distinct runtime contexts, not just a merge in an unused factor
table. Root coverage rejects an empty or unrepresentable runtime carrier. -/
theorem actual_coarser (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (hv : Valid m a) :
    ∃ h : Ready m a, ∃ x y : Registers R RV, x ≠ y ∧
      (RegisterFuture.future m.runtime a h.2.1).code x =
        (RegisterFuture.future m.runtime a h.2.1).code y := by
  obtain ⟨h,ha,laws⟩ := hv
  obtain ⟨p,hp,q,hq,hne,hcode⟩ :=
    TemporalFactorRules.accepted_coarse_roots m.schema (data m a h) m.runtime.tickPeriod ha
  obtain ⟨x,hx⟩ := laws.roots p hp
  obtain ⟨y,hy⟩ := laws.roots q hq
  refine ⟨h,x,y,?_,?_⟩
  · intro he; subst y; exact hne (hx.symm.trans hy)
  · rw [code_link m a h laws,code_link m a h laws,hx,hy]
    exact congrArg (codeImage m.owner) hcode

omit [DecidableEq O] [DecidableEq Stage] [DecidableEq Owner] in
/-- The ACTUAL runtime's eight readouts and absolute ticks/writer obey the
decoded update equations on every context, hence also its entire closure.
This is not merely equality of code-equivalent observations. -/
theorem actual_readout_updates (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (laws : Laws m a h)
    (x : Registers R RV) (da : D × A) (o : O) :
    let d := data m a h
    let p := project m a h x
    let next := RegisterFuture.next m.runtime a h.2.1 x da o
    (project m a h next).factor = o ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).predictive = TemporalFactorRules.prediction m.schema d o ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).order = p.counter + m.schema.stageAdvance ∧
    m.runtime.readouts.ticks.eval a next () = some (p.ticks + TemporalFactorRules.delta m.schema d p.factor da.2) ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).tickPhase =
      (p.ticks + TemporalFactorRules.delta m.schema d p.factor da.2) % m.runtime.tickPeriod ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).progress = p.counter + m.schema.stageAdvance ∧
    m.runtime.readouts.writer.eval a next () = some (TemporalFactorRules.writer m.schema d p.residue) ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).record =
      (if (p.funded && decide (TemporalFactorRules.budgetAfter d > 0)) &&
        TemporalFactorRules.writer m.schema d p.residue then p.counter + m.schema.stageAdvance else 0) ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).residue = p.residue ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).maintenance =
      (p.funded && decide (TemporalFactorRules.budgetAfter d > 0)) ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).owner = m.owner d.resource.owner := by
  dsimp only
  simp only [laws.observation,laws.ticks,laws.writer,laws.successor]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

omit [DecidableEq Owner] in
/-- Funded progress and record growth on the computed factor closure, carried
to the ACTUAL interpreter by its proved simulation. The enclosing acquisition
adapter must prove its entry/closure projection; it is not assumed here. -/
theorem actual_funded_advancement (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a)
    (ha : TemporalFactorRules.Accept m.schema (data m a h)) (laws : Laws m a h)
    (x : Registers R RV) (hx : TemporalFactorRules.Closure m.schema (data m a h) (project m a h x))
    (da : D × A) (o : O) :
    let next := RegisterFuture.next m.runtime a h.2.1 x da o
    (RegisterFuture.observation m.runtime a h.2.1 next).maintenance = true ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).progress >
      (RegisterFuture.observation m.runtime a h.2.1 x).progress ∧
    (RegisterFuture.observation m.runtime a h.2.1 next).record =
      (RegisterFuture.observation m.runtime a h.2.1 x).record + m.schema.stageAdvance := by
  have hp := TemporalFactorRules.accepted_advancement m.schema (data m a h) m.runtime.tickPeriod
    ha (project m a h x) hx da.2 o
  dsimp only
  simp only [laws.observation,laws.successor,observationImage]
  exact ⟨hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩

omit [DecidableEq Owner] in
theorem missing_clause_input (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ m.bindings.scope) (hm : a k = none) : ¬ Valid m a := by
  rintro ⟨h,_,_⟩
  obtain ⟨d,hd⟩ := h.1
  rw [TemporalFactorCells.missing_input m.bindings a k hk hm] at hd
  contradiction

omit [DecidableEq Owner] in
theorem missing_projection_input (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ m.projection.dependencies) (hm : a k = none) : ¬ Valid m a := by
  rintro ⟨h,_,_⟩
  have hp := h.2.2 k hk
  rw [hm] at hp
  contradiction

omit [DecidableEq Owner] in
theorem missing_runtime_row (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ m.runtime.row.dependencies)
    (hm : a k = none) : ¬ Valid m a :=
  fun ⟨h,_,_⟩ => RegisterFuture.missing_row_rejected m.runtime a k hk hm h.2.1

omit [DecidableEq Owner] in
theorem missing_runtime_readout (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ m.runtime.readouts.dependencies)
    (hm : a k = none) : ¬ Valid m a :=
  fun ⟨h,_,_⟩ => RegisterFuture.missing_readout_rejected m.runtime a k hk hm h.2.1

omit [DecidableEq Owner] in
theorem missing_runtime_update (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (reg : R) (k : Cell)
    (hk : k ∈ (m.runtime.program reg).dependencies) (hm : a k = none) : ¬ Valid m a :=
  fun ⟨h,_,_⟩ => missing_program_rejected m.runtime.program a reg k hk hm h.2.1.2.1

omit [DecidableEq Owner] in
theorem row_guard (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (x : Registers R RV) (da : D × A)
    (bad : RegisterFuture.row m.runtime a h.2.1 x da ≠
      TemporalFactorRules.actualRows m.schema (data m a h) (project m a h x) da.2) : ¬ Valid m a :=
  fun ⟨_,_,laws⟩ => bad (laws.rows x da)

omit [DecidableEq Owner] in
theorem successor_guard (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (x : Registers R RV) (da : D × A) (o : O)
    (bad : project m a h (RegisterFuture.next m.runtime a h.2.1 x da o) ≠
      TemporalFactorRules.update m.schema (data m a h) (project m a h x) da.2 o) : ¬ Valid m a :=
  fun ⟨_,_,laws⟩ => bad (laws.successor x da o)

omit [DecidableEq Owner] in
/-- Parameterized guard for each of the eight observed components. The
counterexample is an actual run; audit-root agreement cannot mask it. -/
theorem observation_field_guard {X : Type}
    (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (x : Registers R RV)
    (field : TemporalSnapshotReadout (TemporalFactorRules.Predictive O) (List S × List Id) Bool → X)
    (bad : field (RegisterFuture.observation m.runtime a h.2.1 x) ≠
      field (observationImage m.owner (TemporalFactorRules.observe m.schema (data m a h)
        m.runtime.tickPeriod (project m a h x)))) : ¬ Valid m a :=
  fun ⟨_,_,laws⟩ => bad (congrArg field (laws.observation x))

omit [DecidableEq Owner] in
theorem writer_guard (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (x : Registers R RV)
    (bad : m.runtime.readouts.writer.eval a x () ≠
      some (TemporalFactorRules.writer m.schema (data m a h) (project m a h x).residue)) : ¬ Valid m a :=
  fun ⟨_,_,laws⟩ => bad (laws.writer x)

omit [DecidableEq Owner] in
theorem ticks_guard (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a) (x : Registers R RV)
    (bad : m.runtime.readouts.ticks.eval a x () ≠ some (project m a h x).ticks) : ¬ Valid m a :=
  fun ⟨_,_,laws⟩ => bad (laws.ticks x)

omit [DecidableEq Owner] in
theorem missing_root_guard (m : Raw Cell Value R RV S A O H RouteId Stage Id Owner D)
    (a : Assignment Cell Value) (h : Ready m a)
    (p : TemporalFactorRules.Run O S Id) (hp : p ∈ TemporalFactorRules.roots m.schema (data m a h))
    (bad : ∀ x, project m a h x ≠ p) : ¬ Valid m a := by
  rintro ⟨_,_,laws⟩
  obtain ⟨x,hx⟩ := laws.roots p hp
  exact bad x hx

end CSTTT.TargetTheory.GenericHandoff.TemporalRuntimeCoherence
