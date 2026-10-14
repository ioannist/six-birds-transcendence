import CSTTT.Targets.GenericHandoff.SemanticExecutionBridge

/-! Locality of actual execution, including all runs/words and closure laws.
Agreement concerns raw instruction dependencies, not a supplied future/verdict. -/
namespace CSTTT.TargetTheory.GenericHandoff.ExecutionLocality
open RegisterInterpreter CSTTT.TransportTheory
variable {Cell R D A O P Residue Maintenance Stage Id History RouteId : Type}
  {Value : Cell → Type} {RV : R → Type}

theorem complete_transfer {xs : List Cell} {a b : Assignment Cell Value}
    (h : Agrees xs a b) (ha : Complete xs a) : Complete xs b := by
  intro k hk; rw [← h k hk]; exact ha k hk

def TemporalAgreement (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    (a b : Assignment Cell Value) : Prop :=
  Agrees raw.row.dependencies a b ∧ (∀ r, Agrees (raw.program r).dependencies a b) ∧
    Agrees raw.readouts.dependencies a b

theorem temporal_ready {raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance}
    {a b : Assignment Cell Value} (h : TemporalAgreement raw a b)
    (ha : RegisterFuture.RawReady raw a) : RegisterFuture.RawReady raw b :=
  ⟨complete_transfer h.1 ha.1,fun r => complete_transfer (h.2.1 r) (ha.2.1 r),
    complete_transfer h.2.2 ha.2.2⟩

theorem checked_congr {Env : Type} (p : Program Cell Value R RV Env)
    {a b : Assignment Cell Value} (h : ∀r, Agrees (p r).dependencies a b)
    (ha : ProgramReady p a) (hb : ProgramReady p b) (x : Registers R RV) (env : Env) :
    checkedExecute p a ha x env = checkedExecute p b hb x env := by
  funext r; apply Option.some.inj
  rw [← checked_execute_eq p a ha x env r,← checked_execute_eq p b hb x env r]
  exact congrFun (execute_locality p h x env) r

theorem read_congr {X : Type} (e : Expr Cell Value R RV Unit X)
    {a b : Assignment Cell Value} (h : Agrees e.dependencies a b)
    (ha : Complete e.dependencies a) (hb : Complete e.dependencies b) (x : Registers R RV) :
    RegisterFuture.read e a ha x = RegisterFuture.read e b hb x := by
  apply Option.some.inj
  rw [← RegisterFuture.read_eq e a ha x,← RegisterFuture.read_eq e b hb x]
  exact e.locality h x ()

theorem field_agrees (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    {a b : Assignment Cell Value} (h : TemporalAgreement raw a b) (f : RegisterFuture.Field) :
    Agrees (RegisterFuture.fieldExpr raw.readouts f).dependencies a b := by
  intro k hk; apply h.2.2 k
  cases f <;> simp_all [RegisterFuture.fieldExpr,RegisterFuture.Readouts.dependencies]

theorem observation_congr (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    {a b : Assignment Cell Value} (h : TemporalAgreement raw a b)
    (ha : RegisterFuture.RawReady raw a) (hb : RegisterFuture.RawReady raw b) (x : Registers R RV) :
    RegisterFuture.observation raw a ha x = RegisterFuture.observation raw b hb x := by
  dsimp only [RegisterFuture.observation]
  congr 1
  · exact read_congr _ (field_agrees raw h .predictive) _ _ x
  · exact read_congr _ (field_agrees raw h .order) _ _ x
  · exact congrArg (fun n => n % raw.tickPeriod) (read_congr _ (field_agrees raw h .ticks) _ _ x)
  · exact read_congr _ (field_agrees raw h .progress) _ _ x
  · exact read_congr _ (field_agrees raw h .record) _ _ x
  · exact read_congr _ (field_agrees raw h .residue) _ _ x
  · exact read_congr _ (field_agrees raw h .maintenance) _ _ x
  · exact read_congr _ (field_agrees raw h .owner) _ _ x

theorem row_congr (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    {a b : Assignment Cell Value} (h : TemporalAgreement raw a b)
    (ha : RegisterFuture.RawReady raw a) (hb : RegisterFuture.RawReady raw b) (x : Registers R RV) (da : D × A) :
    RegisterFuture.row raw a ha x da = RegisterFuture.row raw b hb x da := by
  apply Option.some.inj
  rw [← RegisterFuture.row_eq raw a ha x da,← RegisterFuture.row_eq raw b hb x da]
  exact raw.row.locality h.1 x da

theorem next_congr (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    {a b : Assignment Cell Value} (h : TemporalAgreement raw a b)
    (ha : RegisterFuture.RawReady raw a) (hb : RegisterFuture.RawReady raw b) (x : Registers R RV) (da : D × A) (o : O) :
    RegisterFuture.next raw a ha x da o = RegisterFuture.next raw b hb x da o :=
  checked_congr raw.program h.2.1 ha.2.1 hb.2.1 x (da.1,da.2,o)

variable [DecidableEq O]
theorem future_congr (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    {a b : Assignment Cell Value} (h : TemporalAgreement raw a b)
    (ha : RegisterFuture.RawReady raw a) (hb : RegisterFuture.RawReady raw b) :
    RegisterFuture.future raw a ha = RegisterFuture.future raw b hb := by
  have ho : RegisterFuture.observation raw a ha = RegisterFuture.observation raw b hb := funext (observation_congr raw h ha hb)
  have hn : RegisterFuture.next raw a ha = RegisterFuture.next raw b hb := by
    funext x da o; exact next_congr raw h ha hb x da o
  have hr : RegisterFuture.row raw a ha = RegisterFuture.row raw b hb := by
    funext x da; exact row_congr raw h ha hb x da
  have hw : RegisterFuture.weight raw a ha = RegisterFuture.weight raw b hb := by
    funext x da o
    unfold RegisterFuture.weight
    rw [hr]
  simp only [RegisterFuture.future,ho,hw,hn]

def Agreement (raw : ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a b : Assignment Cell Value) : Prop :=
  TemporalAgreement (ExecutionFrontier.temporal raw) a b ∧
  Agrees raw.acquisition.dependencies a b ∧
  (∀r, Agrees (raw.acquisition.initializer r).dependencies a b) ∧
  (∀r, Agrees (raw.acquisition.receive r).dependencies a b) ∧
  (∀f, Agrees (raw.recipes f).dependencies a b)

omit [DecidableEq O] in
theorem ready (raw : ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    {a b : Assignment Cell Value} (h : Agreement raw a b) (ha : ExecutionFrontier.Ready raw a) :
    ExecutionFrontier.Ready raw b :=
  ⟨⟨complete_transfer h.2.1 ha.1.1,fun r => complete_transfer (h.2.2.1 r) (ha.1.2.1 r),
      complete_transfer h.1.1 ha.1.2.2.1,
      fun r => complete_transfer (h.1.2.1 r) (ha.1.2.2.2.1 r),
      fun r => complete_transfer (h.2.2.2.1 r) (ha.1.2.2.2.2 r)⟩,
    temporal_ready h.1 ha.2⟩

omit [DecidableEq O] in
theorem initial_congr (raw : ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    {a b : Assignment Cell Value} (h : Agreement raw a b) (ha : ExecutionFrontier.Ready raw a)
    (hb : ExecutionFrontier.Ready raw b) (hist : History) :
    ExecutionFrontier.initial raw a ha hist = ExecutionFrontier.initial raw b hb hist :=
  RegisterInitialization.initial_locality _ ha.1.2.1 hb.1.2.1 h.2.2.1 hist

omit [DecidableEq O] in
theorem histories_congr (raw : ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    {a b : Assignment Cell Value} (h : Agreement raw a b) :
    raw.acquisition.histories.read a = raw.acquisition.histories.read b := by
  apply raw.acquisition.histories.locality
  intro k hk; apply h.2.1 k
  exact List.mem_append_left _ (List.mem_append_left _ hk)

omit [DecidableEq O] in
theorem rows_congr (raw : ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    {a b : Assignment Cell Value} (h : Agreement raw a b) :
    AcquisitionExecution.rows raw.acquisition a = AcquisitionExecution.rows raw.acquisition b := by
  funext x d act; unfold AcquisitionExecution.rows
  rw [raw.acquisition.execution.row.locality h.1.1]

theorem prefix_congr (raw : ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    {a b : Assignment Cell Value} (h : Agreement raw a b) (ha : ExecutionFrontier.Ready raw a)
    (hb : ExecutionFrontier.Ready raw b) (x : Registers R RV) (word : List (D × A × O)) :
    ExecutionFrontier.PrefixCheck raw a ha x word ↔ ExecutionFrontier.PrefixCheck raw b hb x word := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    have hw : RegisterFuture.weight (ExecutionFrontier.temporal raw) a ha.2 x (d,act) o =
        RegisterFuture.weight (ExecutionFrontier.temporal raw) b hb.2 x (d,act) o :=
      congrArg (fun m => m.weight x (d,act) o) (future_congr (ExecutionFrontier.temporal raw) h.1 ha.2 hb.2)
    have hn := next_congr (ExecutionFrontier.temporal raw) h.1 ha.2 hb.2 x (d,act) o
    change AcquisitionExecution.update raw.acquisition a ha.1 x d act o =
      AcquisitionExecution.update raw.acquisition b hb.1 x d act o at hn
    simp only [ExecutionFrontier.PrefixCheck,rows_congr raw h,hw,hn,ih]

variable [DecidableEq Stage] [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]

theorem semantic_transfer (raw : ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    {a b : Assignment Cell Value} (h : Agreement raw a b)
    (hv : ExecutionFrontier.SemanticReadout raw a) : ExecutionFrontier.SemanticReadout raw b := by
  obtain ⟨ha,audit,domain,exec,paths,future,laws,rows⟩ := hv
  let hb := ready raw h ha
  have hinit : ExecutionFrontier.initial raw a ha = ExecutionFrontier.initial raw b hb := funext (initial_congr raw h ha hb)
  have hroots : ExecutionFrontier.roots raw a ha = ExecutionFrontier.roots raw b hb := by
    simp only [ExecutionFrontier.roots,hinit]
  have hdyn : RegisterFuture.dynamics (ExecutionFrontier.temporal raw) a ha.2 =
      RegisterFuture.dynamics (ExecutionFrontier.temporal raw) b hb.2 := by
    have hf := future_congr (ExecutionFrontier.temporal raw) h.1 ha.2 hb.2
    exact congrArg (fun f => ({outcomes := f.outcomes,actionRow := f.weight,update := f.next} : RawFutureDynamics _ _ _)) hf
  have hclosure : ∀x, ExecutionFrontier.Closure raw a ha x ↔ ExecutionFrontier.Closure raw b hb x := by
    intro x; simp only [ExecutionFrontier.Closure,RegisterFuture.Closure,hdyn,hroots]
  have hfields : ∀ f x, (RegisterFuture.fieldExpr (ExecutionFrontier.temporal raw).readouts f).eval a x () =
      (RegisterFuture.fieldExpr (ExecutionFrontier.temporal raw).readouts f).eval b x () := by
    intro f x; exact (RegisterFuture.fieldExpr raw.readouts f).locality (field_agrees _ h.1 f) x ()
  have hrecipes : ∀f x env, (raw.recipes f).eval a x env = (raw.recipes f).eval b x env := by
    intro f x env; exact (raw.recipes f).locality (h.2.2.2.2 f) x env
  have hn : ∀x da o, RegisterFuture.next (ExecutionFrontier.temporal raw) a ha.2 x da o =
      RegisterFuture.next (ExecutionFrontier.temporal raw) b hb.2 x da o := next_congr _ h.1 _ _
  have ho : ∀x, RegisterFuture.observation (ExecutionFrontier.temporal raw) a ha.2 x =
      RegisterFuture.observation (ExecutionFrontier.temporal raw) b hb.2 x := observation_congr _ h.1 _ _
  have hw : ∀x da o, RegisterFuture.weight (ExecutionFrontier.temporal raw) a ha.2 x da o =
      RegisterFuture.weight (ExecutionFrontier.temporal raw) b hb.2 x da o := by
    intro x da o; exact congrArg (fun f => f.weight x da o) (future_congr _ h.1 _ _)
  have hticks : ∀x, (ExecutionFrontier.temporal raw).readouts.ticks.eval a x () = (ExecutionFrontier.temporal raw).readouts.ticks.eval b x () := hfields .ticks
  have views : raw.acquisition.routes.read a = raw.acquisition.routes.read b ∧
      raw.acquisition.events.read a = raw.acquisition.events.read b ∧
      raw.acquisition.realized.read a = raw.acquisition.realized.read b ∧
      raw.acquisition.receiver.read a = raw.acquisition.receiver.read b := by
    refine ⟨?_,?_,?_,?_⟩
    all_goals unfold CellView.read
    all_goals rw [h.2.1 _ (by simp [AcquisitionExecution.Raw.dependencies])]
  refine ⟨hb,?_,domain,exec,?_,?_,?_,?_⟩
  · obtain ⟨nonempty,hists,he,hcheck,hcover⟩ := audit
    refine ⟨nonempty,hists,(histories_congr raw h).symm.trans he,?_,hcover⟩
    intro i hi
    obtain ⟨hp,hle,hprefix⟩ := hcheck i hi
    refine ⟨hp,hle,?_⟩
    rw [← hinit]
    have hword : ExecutionFrontier.historyPrefix raw a i = ExecutionFrontier.historyPrefix raw b i := by
      simp only [ExecutionFrontier.historyPrefix,histories_congr raw h]
    rw [← hword]
    exact (prefix_congr raw h ha hb _ _).mp hprefix
  · simpa only [ExecutionFrontier.PathsAvailable,← views.1,← views.2.1,← views.2.2.1,← views.2.2.2] using paths
  · rwa [← future_congr (ExecutionFrontier.temporal raw) h.1 ha.2 hb.2]
  · obtain ⟨hd,haction,hnodup,htick,hnonempty,hsteps,hcoverage⟩ := laws
    refine ⟨hd,haction,hnodup,htick,by rwa [← hroots],?_,?_⟩
    · intro x hx d hdist act hact o hout
      have hp := hsteps x ((hclosure x).mpr hx) d hdist act hact o hout
      constructor
      · intro f
        have eq := hp.1 f
        simpa only [RegisterFuture.FieldLaw,hn,hfields,hrecipes] using eq
      · intro hweight
        have hp' := hp.2 (by rwa [hw])
        simpa only [RegisterFuture.PositiveRecipes,hrecipes,ho,hticks] using hp'
    · intro x hx d hdist act hact o hp
      apply hcoverage x ((hclosure x).mpr hx) d hdist act hact o
      have hrow : RegisterFuture.row (ExecutionFrontier.temporal raw) a ha.2 x (d,act) =
          RegisterFuture.row (ExecutionFrontier.temporal raw) b hb.2 x (d,act) := by
        rw [ExecutionFrontier.rows_shared raw a ha,ExecutionFrontier.rows_shared raw b hb,rows_congr raw h]
      simpa only [StrategyGame.PositiveSupport,hrow] using hp
  · intro x hx d hd act ha
    simpa only [rows_congr raw h] using rows x ((hclosure x).mpr hx) d hd act ha

end CSTTT.TargetTheory.GenericHandoff.ExecutionLocality
