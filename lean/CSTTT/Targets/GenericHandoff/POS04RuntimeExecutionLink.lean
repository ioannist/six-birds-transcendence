import CSTTT.Targets.GenericHandoff.ExecutionLink
import CSTTT.Targets.GenericHandoff.POS04RuntimeRoute
import CSTTT.Targets.GenericHandoff.POS04HistoricalRuntime
import CSTTT.Targets.GenericHandoff.POS04ExecutionBridge

/-! Whole-run register lift into the shared POS-04 runtime. Source and target
G1c programs use five registers; the funded acquisition/resource runtime uses
one typed carrier/run frame. Their link is checked against actual assigned
rows and actual counter/ledger/residue updates on ALL runs and branches.
No predictive representative or audit-root-only equality substitutes for it.

The historical autonomy updater is separately linked to the SAME target
program. This does not fund the recorded source past: autonomy still uses
historical support, while complete lineage uses actual funded execution. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RuntimeExecutionLink
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RegisterDynamics POS04RouteExecution
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def execution (tag : Tag) : ResourceRuntime.Execution Cell Value Register RegisterValue
    LaneDisturbance Action Ambient :=
  ⟨[.nominal],actions,ambientStates,POS04RegisterFuture.enabledRow tag,program tag⟩

/-- Raw typed coordinates, not a candidate run-to-run function. -/
def embedding (tag : Tag) : (k : Unit) → Expr Cell Value Register RegisterValue Unit (FrameValue k) := by
  exact fun _ => .map (fun p => (tag,Run6.mk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (.pair (.register Register.factor) (.pair (.register Register.counter)
      (.pair (.register Register.ticks) (.pair (.register Register.residue) (.register Register.funded)))))

def raw (tag : Tag) : ExecutionLink.Raw Cell Value Register Unit RegisterValue FrameValue
    LaneDisturbance Action Ambient :=
  ⟨execution tag,acquisition.execution,embedding tag⟩

def historicalRaw : ExecutionLink.Raw Cell Value Register Unit RegisterValue FrameValue
    LaneDisturbance Action Ambient :=
  ⟨execution .target,POS04HistoricalRuntime.execution,embedding .target⟩

theorem core_complete (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) : Complete (coreDependencies tag) a := by
  intro k hk
  apply hc k
  cases tag <;> simp_all [coreDependencies,dependencies] <;> grind

theorem source_ready (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) : ExecutionLink.ExecutionReady (execution tag) a := by
  refine ⟨?_,program_ready a tag (core_complete a hc tag)⟩
  intro k hk
  apply hc k
  cases tag <;>
    simp_all [execution,POS04RegisterFuture.enabledRow,rowExpression,Expr.dependencies,dependencies] <;> grind

theorem ready (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) : ExecutionLink.Ready (raw tag) a := by
  refine ⟨source_ready a hc tag,?_,?_⟩
  · exact ⟨(POS04RouteExecution.ready a hc).2.2.1,(POS04RouteExecution.ready a hc).2.2.2.1⟩
  · intro r k hk; simp [raw,embedding,Expr.dependencies] at hk

theorem embed_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : ExecutionLink.Ready (raw tag) a) (x : Registers Register RegisterValue) :
    ExecutionLink.embed (raw tag) a h x = frame tag (decodeRun x) := by
  funext k
  apply Option.some.inj
  exact (ExecutionLink.embed_equation (raw tag) a h x k).symm

theorem source_rows (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) (x : Run6) (d : LaneDisturbance) (act : Action) :
    ExecutionLink.rows (execution tag) a (encode x) d act = actualRows6 (runInputs6 a tag) x act := by
  have hr := cell_value (hc (.resources tag) (by cases tag <;> simp [dependencies]))
  have hl := cell_value (hc .maintenance (by simp [dependencies]))
  have hrow := row_eval a tag (hc (.rows tag) (by cases tag <;> simp [dependencies])) x d act
  simp only [ExecutionLink.rows,execution,POS04RegisterFuture.enabledRow,Expr.eval,encode]
  rw [hr,hl,hrow]
  cases tag <;> rfl

theorem source_update (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) (x : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    ExecutionLink.update (execution tag) a (source_ready a hc tag) (encode x) d act o =
      encode (actualUpdate6 (runInputs6 a tag) x act o) := by
  funext k
  apply Option.some.inj
  have he := congrFun (program_actual a tag (core_complete a hc tag) x d act o) k
  exact (checked_execute_eq (program tag) a (source_ready a hc tag).2 (encode x) (d,act,o) k).symm.trans he

/-- The imported ambient enumeration covers every actual outcome, including
both exits, on every partial assignment and every raw row. -/
theorem ambient_coverage {R : Type} {V : R → Type}
    (e : ResourceRuntime.Execution Cell Value R V LaneDisturbance Action Ambient)
    (a : CSTTT.POS04.Assigned.Assignment) (he : e.outcomes = ambientStates) :
    ExecutionLink.SupportCoverage e a := by
  intro x d act o _
  rw [he]
  cases o with
  | inK k => cases k <;> decide
  | p2w0 => decide
  | p5w1 => decide

theorem laws (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) : ExecutionLink.Laws (raw tag) a (ready a hc tag) := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro x d act
    rw [embed_eq,← encode_decode x]
    change AcquisitionExecution.rows acquisition a (frame tag (decodeRun x)) d act =
      ExecutionLink.rows (execution tag) a (encode (decodeRun x)) d act
    rw [POS04RouteExecution.rows_eq a hc,source_rows a hc]
  · exact ⟨ambient_coverage _ a rfl,ambient_coverage _ a rfl⟩
  · intro x d hd act ha o ho
    rw [embed_eq,embed_eq,← encode_decode x]
    dsimp only [raw]
    rw [source_update a hc,decode_encode,decode_encode]
    change frame tag _ = AcquisitionExecution.update acquisition a (POS04RouteExecution.ready a hc) _ d act o
    rw [POS04RouteExecution.update_eq a hc]

theorem checked (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) : ExecutionLink.Pass (raw tag) a :=
  ⟨ready a hc tag,laws a hc tag⟩

/-- Direct connection of G1c's source/receiver program to the runtime execution.
These equations do not rely on the baseline transition table. -/
theorem g1c_source_execution : POS04ExecutionFrontier.raw.acquisition.execution = execution .source := rfl
theorem g1c_receiver_execution : POS04ReceiverFrontier.raw.acquisition.execution = execution .target := rfl

/-- Every actual finite supported word commutes with the shared run frame.
In particular exit2 and exit5 remain different Ambient outcomes. -/
theorem every_supported_word (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (tag : Tag) (x : Registers Register RegisterValue)
    (word : List (LaneDisturbance × Action × Ambient))
    (hw : ExecutionLink.Supported (execution tag) a (source_ready a hc tag) x word) :
    ExecutionLink.embed (raw tag) a (ready a hc tag)
        (ExecutionLink.fold (execution tag) a (source_ready a hc tag) x word) =
      ExecutionLink.fold acquisition.execution a (ready a hc tag).2.1
        (frame tag (decodeRun x)) word := by
  have h := ExecutionLink.supported_fold (raw tag) a (ready a hc tag) (laws a hc tag) x word hw
  simpa only [embed_eq] using h

/-- Only the target updater's consumed primitives. No source ticks/funding,
hazards, histories or audit fields are added to the autonomy dynamic link. -/
def targetDependencies : List Cell :=
  [.rows .target,.ticks .target,.maintenance,.resources .target]

theorem historical_ready (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete targetDependencies a) : ExecutionLink.Ready historicalRaw a := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
  · intro k hk
    apply hc k
    simp_all [historicalRaw,execution,POS04RegisterFuture.enabledRow,rowExpression,
      Expr.dependencies,targetDependencies] <;> grind
  · apply program_ready a .target
    intro k hk; apply hc k
    simp_all [coreDependencies,targetDependencies] <;> grind
  · intro k hk
    apply hc k
    simp_all [historicalRaw,POS04HistoricalRuntime.execution,lift,RunFrame.dependencies,
      POS04RegisterFuture.enabledRow,rowExpression,Expr.dependencies,targetDependencies] <;> grind
  · intro r k hk
    apply hc k
    simp [historicalRaw,POS04HistoricalRuntime.execution,nextExpression,program,lift,
      RunFrame.dependencies,Expr.dependencies] at hk
    simp_all [targetDependencies] <;> grind
  · intro r k hk; simp [historicalRaw,embedding,Expr.dependencies] at hk

theorem historical_embed (a : CSTTT.POS04.Assigned.Assignment)
    (h : ExecutionLink.Ready historicalRaw a) (x : Registers Register RegisterValue) :
    ExecutionLink.embed historicalRaw a h x = frame .target (decodeRun x) := by
  funext k
  exact Option.some.inj (ExecutionLink.embed_equation historicalRaw a h x k).symm

theorem historical_next_eval (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete targetDependencies a) (x : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    (nextExpression .target).eval a (frame .target x) (d,act,o) =
      some (.target,actualUpdate6 (runInputs6 a .target) x act o) := by
  have hcore : Complete (coreDependencies .target) a := by
    intro k hk; apply hc k; simp_all [coreDependencies,targetDependencies] <;> grind
  have hp := program_actual a .target hcore x d act o
  simp only [nextExpression,Expr.eval,lift,RunFrame.evaluation,frame,RunFrame.pack,POS04RouteExecution.decode]
  have hfactor := congrFun hp Register.factor
  have hcounter := congrFun hp Register.counter
  have hticks := congrFun hp Register.ticks
  have hresidue := congrFun hp Register.residue
  have hfunded := congrFun hp Register.funded
  simp only [execute] at hfactor hcounter hticks hresidue hfunded
  rw [hfactor,hcounter,hticks,hresidue,hfunded]
  rfl

/-- Historical autonomy has exactly the target G1c updater, for every partial
assignment with its consumed cells, including unfunded contexts and exits.
Neither acquisition-source funding nor a finite-context assumption is used. -/
theorem historical_laws (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete targetDependencies a) :
    ExecutionLink.Laws historicalRaw a (historical_ready a hc) := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro x d act
    rw [historical_embed]
    unfold ExecutionLink.rows
    simp only [historicalRaw,POS04HistoricalRuntime.execution,lift,RunFrame.evaluation,
      frame,POS04RouteExecution.decode,decodeRun]
    rfl
  · exact ⟨ambient_coverage _ a rfl,ambient_coverage _ a rfl⟩
  · intro x d hd act ha o ho
    rw [historical_embed,historical_embed]
    have hs : ExecutionLink.update historicalRaw.source a (historical_ready a hc).1 x d act o =
        encode (actualUpdate6 (runInputs6 a .target) (decodeRun x) act o) := by
      funext k
      apply Option.some.inj
      have hcore : Complete (coreDependencies .target) a := by
        intro k hk; apply hc k; simp_all [coreDependencies,targetDependencies] <;> grind
      have he := congrFun (program_actual a .target hcore (decodeRun x) d act o) k
      rw [encode_decode] at he
      exact (checked_execute_eq historicalRaw.source.program a (historical_ready a hc).1.2 x (d,act,o) k).symm.trans he
    rw [hs,decode_encode]
    funext k
    apply Option.some.inj
    exact (historical_next_eval a hc (decodeRun x) d act o).symm.trans
      (checked_execute_eq historicalRaw.target.program a (historical_ready a hc).2.1.2
        (frame .target (decodeRun x)) (d,act,o) k)

theorem historical_checked (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete targetDependencies a) : ExecutionLink.Pass historicalRaw a :=
  ⟨historical_ready a hc,historical_laws a hc⟩

/-- Exact missing-input boundary of this updater link, independent of whether
the enclosing arrival protocol or any response strategy exists. -/
theorem historical_pass_iff (a : CSTTT.POS04.Assigned.Assignment) :
    ExecutionLink.Pass historicalRaw a ↔ Complete targetDependencies a := by
  constructor
  · rintro ⟨h,_⟩ k hk
    simp only [targetDependencies,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with hk | hk | hk | hk
    all_goals subst k
    · apply h.1.1; simp [historicalRaw,execution,POS04RegisterFuture.enabledRow,rowExpression,Expr.dependencies]
    · apply h.1.2 Register.ticks; simp [historicalRaw,execution,program,Expr.dependencies]
    · apply h.1.1; simp [historicalRaw,execution,POS04RegisterFuture.enabledRow,rowExpression,Expr.dependencies]
    · apply h.1.1; simp [historicalRaw,execution,POS04RegisterFuture.enabledRow,rowExpression,Expr.dependencies]
  · exact historical_checked a

end CSTTT.TargetTheory.GenericHandoff.POS04RuntimeExecutionLink
