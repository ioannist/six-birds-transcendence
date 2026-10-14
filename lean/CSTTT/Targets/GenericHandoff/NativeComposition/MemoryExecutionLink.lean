import CSTTT.Targets.GenericHandoff.NativeComposition.MemoryFrames
import CSTTT.Targets.GenericHandoff.NativeComposition.ModeExecution
import CSTTT.Targets.GenericHandoff.NativeComposition.Resources
import CSTTT.Targets.GenericHandoff.ExecutionLink

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.MemoryExecutionLink
open RegisterInterpreter

def mode (sourceOwner : Owner) (source : Bool) : Owner :=
  if source then sourceOwner else swapOwner sourceOwner

def embedding (sourceOwner : Owner) (source : Bool) :
    (k : Unit) → Expr Owner MemoryValue Unit (fun _ => Frame.State) Unit ModeExecution.State :=
  fun _ => .map (fun x => (x,mode sourceOwner source)) (.register ())

def execution (cell sourceOwner : Owner) (source : Bool) (names : Owner → CarrierId) :
    ResourceRuntime.Execution Owner MemoryValue Unit (fun _ => Frame.State) Unit Bool Factor :=
  let f := MemoryFrames.raw cell source (mode sourceOwner source) names
  ⟨f.disturbances,f.actions,f.outcomes,f.row,f.program⟩

def raw (cell sourceOwner : Owner) (source : Bool) (names : Owner → CarrierId) :
    ExecutionLink.Raw Owner MemoryValue Unit Unit (fun _ => Frame.State) (fun _ => ModeExecution.State) Unit Bool Factor :=
  ⟨execution cell sourceOwner source names,ModeExecution.execution cell sourceOwner,embedding sourceOwner source⟩

theorem ready (cell sourceOwner : Owner) (source : Bool) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (ha : (a cell).isSome=true) :
    ExecutionLink.Ready (raw cell sourceOwner source names) a := by
  have hf := MemoryFrames.ready cell source (mode sourceOwner source) names a ha
  have hr := ModeExecution.resources_ready cell sourceOwner names a ha
  refine ⟨⟨hf.1,hf.2.1⟩,⟨hr.1,hr.2.1⟩,?_⟩
  intro r k hk
  simp [raw,embedding,Expr.dependencies] at hk

theorem embed (cell sourceOwner : Owner) (source : Bool) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : ExecutionLink.Ready (raw cell sourceOwner source names) a)
    (x : Frame.Registers) :
    ExecutionLink.embed (raw cell sourceOwner source names) a h x =
      ModeExecution.pack (x (),mode sourceOwner source) := by
  funext r
  cases r
  have he := ExecutionLink.embed_equation (raw cell sourceOwner source names) a h x ()
  change some (x (),mode sourceOwner source) = some (ExecutionLink.embed _ a h x ()) at he
  exact (Option.some.inj he).symm

theorem selected_data (sourceOwner : Owner) (source : Bool) (p : Input × Input) :
    (if mode sourceOwner source=swapOwner sourceOwner then p.1.temporal else p.2.temporal) =
      (MemoryFrames.selectInput source p).temporal := by
  cases sourceOwner <;> cases source <;> rfl

theorem rows (cell sourceOwner : Owner) (source : Bool) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : ExecutionLink.Ready (raw cell sourceOwner source names) a)
    (p : Input × Input) (hp : a cell=some p) (x : Frame.Registers) (d : Unit) (act : Bool) :
    ExecutionLink.rows (raw cell sourceOwner source names).target a (ExecutionLink.embed (raw cell sourceOwner source names) a h x) d act =
      ExecutionLink.rows (raw cell sourceOwner source names).source a x d act := by
  rw [embed]
  unfold ExecutionLink.rows
  have hf := MemoryFrames.ready cell source (mode sourceOwner source) names a (by rw [hp]; rfl)
  have hs := RegisterFuture.row_eq (MemoryFrames.raw cell source (mode sourceOwner source) names) a hf x (d,act)
  rw [MemoryFrames.row cell source (mode sourceOwner source) names a hf p hp] at hs
  change ((ModeExecution.rowExpr cell sourceOwner).eval a _ (d,act)).getD [] =
    ((MemoryFrames.raw cell source (mode sourceOwner source) names).row.eval a x (d,act)).getD []
  rw [ModeExecution.mode_row_evaluation cell sourceOwner a p hp,hs]
  simp only [ModeExecution.pack,selected_data]
  rfl

theorem source_update (cell sourceOwner : Owner) (source : Bool) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : ExecutionLink.Ready (raw cell sourceOwner source names) a)
    (p : Input × Input) (hp : a cell=some p) (x : Frame.Registers) (d : Unit) (act : Bool) (o : Factor) :
    ExecutionLink.update (raw cell sourceOwner source names).source a h.1 x d act o =
      Frame.pack (TemporalFactorRules.update (factorSchema (mode sourceOwner source))
        (MemoryFrames.selectInput source p).temporal (x ()) act o) := by
  have hf := MemoryFrames.ready cell source (mode sourceOwner source) names a (by rw [hp]; rfl)
  exact MemoryFrames.next cell source (mode sourceOwner source) names a hf p hp x (d,act) o

theorem target_update (cell sourceOwner : Owner) (source : Bool) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : ExecutionLink.Ready (raw cell sourceOwner source names) a)
    (p : Input × Input) (hp : a cell=some p) (x : Frame.Registers) (d : Unit) (act : Bool) (o : Factor) :
    ExecutionLink.update (raw cell sourceOwner source names).target a h.2.1
      (ModeExecution.pack (x (),mode sourceOwner source)) d act o =
      ModeExecution.pack (TemporalFactorRules.update (factorSchema sourceOwner)
        (MemoryFrames.selectInput source p).temporal (x ()) act o,mode sourceOwner source) := by
  funext r
  have he := checked_execute_eq (raw cell sourceOwner source names).target.program a h.2.1.2
    (ModeExecution.pack (x (),mode sourceOwner source)) (d,act,o) r
  simp only [execute,raw,ModeExecution.execution] at he
  rw [ModeExecution.mode_update_evaluation cell sourceOwner a p hp] at he
  simp only [ModeExecution.pack,selected_data] at he
  exact (Option.some.inj he).symm

/-- Exact all-state embedding laws, with every declared outcome retained even
when its current row weight is zero. No finite audit is substituted here. -/
theorem laws (cell sourceOwner : Owner) (source : Bool) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : ExecutionLink.Ready (raw cell sourceOwner source names) a)
    (p : Input × Input) (hp : a cell=some p) : ExecutionLink.Laws (raw cell sourceOwner source names) a h := by
  refine ⟨rfl,rfl,rfl,rows cell sourceOwner source names a h p hp,?_,?_⟩
  · exact ⟨(fun _ _ _ o _ => factor_mem o),(fun _ _ _ o _ => factor_mem o)⟩
  · intro x d _ act _ o _
    rw [source_update cell sourceOwner source names a h p hp,embed,embed,
      target_update cell sourceOwner source names a h p hp]
    rfl

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.MemoryExecutionLink
