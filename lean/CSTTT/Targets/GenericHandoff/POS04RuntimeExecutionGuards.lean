import CSTTT.Targets.GenericHandoff.POS04RuntimeExecutionLink
import CSTTT.Targets.GenericHandoff.RegisterReadoutLaws

/-! Sensitivity guards for the whole-run representation link. Each proposal
changes only one raw source execution field. Both proposals are ready, so
rejection does not arise from incompatible missing-input premises. Uniform
weights and an identity successor are interpreter probes, not new registered
scientific models or modifications of the POS-04 declaration. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RuntimeExecutionGuards
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RegisterDynamics POS04RouteExecution POS04RuntimeExecutionLink
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def uniformRows : List (Ambient × Rat) :=
  ambientStates.map (fun o => (o,(1 : Rat) / ambientStates.length))
def uniformSource := {(raw .source) with source :=
  {(raw .source).source with row := .literal uniformRows}}
def identitySource := {(raw .source) with source :=
  {(raw .source).source with program := fun k => .register k}}

theorem uniform_ready : ExecutionLink.Ready uniformSource canonical := by
  refine ⟨⟨?_,(ready canonical (canonical_complete _) .source).1.2⟩,
    (ready canonical (canonical_complete _) .source).2.1,
    (ready canonical (canonical_complete _) .source).2.2⟩
  intro k hk; simp [uniformSource,Expr.dependencies] at hk

theorem identity_ready : ExecutionLink.Ready identitySource canonical := by
  refine ⟨⟨(ready canonical (canonical_complete _) .source).1.1,?_⟩,
    (ready canonical (canonical_complete _) .source).2.1,
    (ready canonical (canonical_complete _) .source).2.2⟩
  intro r k hk; simp [identitySource,Expr.dependencies] at hk

theorem uniform_embedding (x : Registers Register RegisterValue) :
    ExecutionLink.embed uniformSource canonical uniform_ready x = frame .source (decodeRun x) := by
  funext k
  exact Option.some.inj (ExecutionLink.embed_equation uniformSource canonical uniform_ready x k).symm

theorem identity_embedding (x : Registers Register RegisterValue) :
    ExecutionLink.embed identitySource canonical identity_ready x = frame .source (decodeRun x) := by
  funext k
  exact Option.some.inj (ExecutionLink.embed_equation identitySource canonical identity_ready x k).symm

def witness : Run6 := ⟨.inK .p1w0,0,0,routeRegister .a,true⟩

theorem uniform_rejected : ¬ ExecutionLink.Pass uniformSource canonical := by
  apply ExecutionLink.rows_mismatch_rejected uniformSource canonical uniform_ready
    (encode witness) .nominal .cw
  rw [uniform_embedding,decode_encode]
  change AcquisitionExecution.rows acquisition canonical (frame .source witness) .nominal .cw ≠ uniformRows
  rw [POS04RouteExecution.rows_eq canonical (canonical_complete _)]
  decide +kernel

theorem identity_update (x : Registers Register RegisterValue)
    (d : LaneDisturbance) (act : Action) (o : Ambient) :
    ExecutionLink.update identitySource.source canonical identity_ready.1 x d act o = x := by
  funext k
  exact Option.some.inj (checked_execute_eq identitySource.source.program canonical
    identity_ready.1.2 x (d,act,o) k).symm

theorem identity_rejected : ¬ ExecutionLink.Pass identitySource canonical := by
  apply ExecutionLink.successor_mismatch_rejected identitySource canonical identity_ready
    (encode witness) .nominal (by decide) .cw (by decide) (.inK .p2w1) (by decide)
  rw [identity_update,identity_embedding,decode_encode]
  change frame .source witness ≠ AcquisitionExecution.update acquisition canonical
    (POS04RouteExecution.ready canonical (canonical_complete _)) (frame .source witness)
      .nominal .cw (.inK .p2w1)
  rw [POS04RouteExecution.update_eq canonical (canonical_complete _)]
  intro bad
  have hc := congrArg (fun x : Registers Unit FrameValue => (x ()).2.counter) bad
  change (0 : Nat) = 1 at hc
  contradiction

end CSTTT.TargetTheory.GenericHandoff.POS04RuntimeExecutionGuards

/-! Eddy's omitted-support diagnostic. The fair two-branch raw row is fixed
first; only `false` is advertised. The source writes zero on either branch;
the target writes one on `true`. These are interpreter sensitivity probes. -/
namespace CSTTT.TargetTheory.GenericHandoff.ExecutionLinkOmission
open RegisterInterpreter

def Value (k : Empty) : Type := nomatch k
abbrev RV : Unit → Type := fun _ => Nat
def assignment : Assignment Empty Value := fun k => nomatch k
def fairRow : List (Bool × Rat) := [(false,1/2),(true,1/2)]

def source : ResourceRuntime.Execution Empty Value Unit RV Unit Unit Bool :=
  ⟨[()],[()],[false],.literal fairRow,fun _ => .literal 0⟩
def target : ResourceRuntime.Execution Empty Value Unit RV Unit Unit Bool :=
  {source with program := (fun _ => Expr.map (fun o : Bool => if o then 1 else 0)
    (.environment (fun e => e.2.2)))}
def raw : ExecutionLink.Raw Empty Value Unit Unit RV RV Unit Unit Bool :=
  ⟨source,target,fun k => .register k⟩

theorem ready : ExecutionLink.Ready raw assignment := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
  all_goals simp [Complete,ProgramReady,raw,source,target,Expr.dependencies]

def initial : Registers Unit RV := fun _ => 0

theorem embed_identity (x : Registers Unit RV) : ExecutionLink.embed raw assignment ready x = x := by
  funext k
  exact Option.some.inj (ExecutionLink.embed_equation raw assignment ready x k).symm

theorem listed_successor (x : Registers Unit RV) (d act : Unit) (o : Bool)
    (ho : o ∈ raw.source.outcomes) :
    ExecutionLink.embed raw assignment ready (ExecutionLink.update source assignment ready.1 x d act o) =
      ExecutionLink.update target assignment ready.2.1 (ExecutionLink.embed raw assignment ready x) d act o := by
  have he : o = false := by simpa [raw,source] using ho
  subst o
  rw [embed_identity,embed_identity]
  funext k
  have hs : ExecutionLink.update source assignment ready.1 x d act false k = 0 :=
    Option.some.inj (checked_execute_eq source.program assignment ready.1.2 x (d,act,false) k).symm
  have ht : ExecutionLink.update target assignment ready.2.1 x d act false k = 0 :=
    Option.some.inj (checked_execute_eq target.program assignment ready.2.1.2 x (d,act,false) k).symm
  rw [hs,ht]

/-- All old link obligations hold, so the negative specifically exercises
the new coverage law rather than an already failing row or successor gate. -/
theorem previous_checks_hold :
    raw.target.disturbances = raw.source.disturbances ∧
    raw.target.actions = raw.source.actions ∧ raw.target.outcomes = raw.source.outcomes ∧
    (∀ x d act, ExecutionLink.rows raw.target assignment (ExecutionLink.embed raw assignment ready x) d act =
      ExecutionLink.rows raw.source assignment x d act) ∧
    (∀ x, ∀ d ∈ raw.source.disturbances, ∀ act ∈ raw.source.actions, ∀ o ∈ raw.source.outcomes,
      ExecutionLink.embed raw assignment ready (ExecutionLink.update source assignment ready.1 x d act o) =
        ExecutionLink.update target assignment ready.2.1 (ExecutionLink.embed raw assignment ready x) d act o) :=
  ⟨rfl,rfl,rfl,fun _ _ _ => rfl,fun x d _ act _ o ho => listed_successor x d act o ho⟩

theorem true_positive : StrategyGame.PositiveSupport (ExecutionLink.rows raw.source assignment)
    initial () () true := by
  refine ⟨1/2,by simp [raw,source,ExecutionLink.rows,Expr.eval,fairRow],?_⟩
  decide +kernel

theorem omission_rejected : ¬ ExecutionLink.Pass raw assignment :=
  ExecutionLink.omitted_source_support_rejected raw assignment initial () () true
    true_positive (by decide)

theorem actual_updates_differ :
    ExecutionLink.update source assignment ready.1 initial () () true () = 0 ∧
    ExecutionLink.update target assignment ready.2.1 initial () () true () = 1 := by
  constructor
  all_goals apply Option.some.inj
  all_goals exact (checked_execute_eq _ assignment _ initial ((),(),true) ()).symm

/-- The register gate is checked separately: it too must reject the raw
positive true branch, rather than only checking the advertised false branch. -/
def temporal : RegisterFuture.Raw Empty Value Unit RV Unit Unit Bool Unit Unit Unit :=
  ⟨[false],[()],[()],1,.literal fairRow,fun _ =>
    .map (fun p : Nat × Bool => if p.2 then p.1 else p.1 + 1)
      (.pair (.register ()) (.environment (fun e => e.2.2))),
    ⟨.literal (),.register (),.register (),.register (),.literal true,
      .register (),.literal (),.literal (),.literal ⟨0⟩⟩⟩
def recipes : RegisterFuture.StepRecipes Empty Value Unit RV Unit Unit Bool Unit Unit Unit
  | .predictive | .residue | .maintenance => .literal ()
  | .writer => .literal true
  | .owner => .literal ⟨0⟩
  | .order | .ticks | .progress | .record => temporal.program ()

theorem temporal_ready : RegisterFuture.RawReady temporal assignment := by
  refine ⟨?_,?_,?_⟩
  all_goals simp [Complete,ProgramReady,temporal,RegisterFuture.Readouts.dependencies,Expr.dependencies]

theorem temporal_row : RegisterFuture.row temporal assignment temporal_ready initial ((),()) = fairRow :=
  Option.some.inj (RegisterFuture.row_eq temporal assignment temporal_ready initial ((),())).symm

theorem temporal_false_next (x : Registers Unit RV) :
    RegisterFuture.next temporal assignment temporal_ready x ((),()) false () = x () + 1 :=
  Option.some.inj (checked_execute_eq temporal.program assignment temporal_ready.2.1 x ((),(),false) ()).symm

/-- The old field/advancement checks all pass on the advertised false branch.
The omitted true branch is nonadvancing and must not escape by domain filtering. -/
theorem readout_previous_steps (x : Registers Unit RV) :
    (∀ f, RegisterFuture.FieldLaw temporal recipes assignment temporal_ready x ((),()) false f) ∧
    RegisterFuture.PositiveRecipes temporal recipes assignment temporal_ready x ((),()) false := by
  constructor
  · intro f
    cases f <;> first
      | rfl
      | (change some (RegisterFuture.next temporal assignment temporal_ready x ((),()) false ()) = some (x () + 1)
         rw [temporal_false_next])
  · have horder : (RegisterFuture.observation temporal assignment temporal_ready x).order = x () :=
      (Option.some.inj (RegisterFuture.observation_order_eval temporal assignment temporal_ready x)).symm
    have hprogress : (RegisterFuture.observation temporal assignment temporal_ready x).progress = x () :=
      (Option.some.inj (RegisterFuture.observation_progress_eval temporal assignment temporal_ready x)).symm
    have hrecord : (RegisterFuture.observation temporal assignment temporal_ready x).record = x () :=
      (Option.some.inj (RegisterFuture.observation_record_eval temporal assignment temporal_ready x)).symm
    refine ⟨x () + 1,x () + 1,x () + 1,x () + 1,rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩
    · rw [horder]; omega
    · simp [temporal,Expr.eval]
    · rw [hprogress]; omega
    · rw [hrecord]; omega

theorem readout_omission_rejected :
    ¬ RegisterFuture.ReadoutLawGate temporal recipes assignment temporal_ready [initial] := by
  apply RegisterFuture.omitted_support_rejects_readout_gate temporal recipes assignment temporal_ready
    [initial] initial (CSTTT.TransportTheory.FutureClosure.root _ (by simp))
    () (by simp [temporal]) () (by simp [temporal]) true
  · change ∃ w, (true,w) ∈ RegisterFuture.row temporal assignment temporal_ready initial ((),()) ∧ 0 < w
    rw [temporal_row]
    refine ⟨1/2,by simp [fairRow],?_⟩
    decide +kernel
  · decide

end CSTTT.TargetTheory.GenericHandoff.ExecutionLinkOmission
