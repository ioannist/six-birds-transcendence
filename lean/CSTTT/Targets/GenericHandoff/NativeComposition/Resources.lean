import CSTTT.Targets.GenericHandoff.NativeComposition.ModeExecution

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter

def stateExpr : Expr Owner MemoryValue Unit (fun _ => State) Unit State := .register ()
def resources (cell : Owner) (sourceOwner : Owner) (names : Owner → CarrierId) :
    ResourceRuntime.Raw Owner MemoryValue Unit (fun _ => State) Unit Bool Factor Factor Bool Frame.Residue where
  execution := execution cell sourceOwner
  accounts := .map (fun p : FactorData × State => fun r : Bool =>
    if r then ⟨some (names p.1.resource.owner),decide (p.2.2=swapOwner sourceOwner),
      if p.2.1.funded then p.1.ledger.initial else 0⟩ else ⟨none,false,0⟩) (context cell sourceOwner)
  required := .literal [true]
  charge := .map (fun p : FactorData × State =>
    (⟨names p.1.resource.owner,(if p.2.2=swapOwner sourceOwner then [true] else []),
      (fun r => if r then p.1.ledger.cost else 0),
      (fun r => if r then p.1.ledger.recharge else 0)⟩ : ResourceRuntime.Charge Bool))
    ((context cell sourceOwner).reenv (fun _ => ()))
  advances := .literal ⟨1,1,1,1⟩
  factor := .map (fun s => some s.1.factor) stateExpr
  order := .map (fun s => s.1.counter) stateExpr
  ticks := .map (fun s => s.1.ticks) stateExpr
  progress := .map (fun s => s.1.counter) stateExpr
  record := .map (fun p : FactorData × State =>
    if p.2.1.funded && TemporalFactorRules.writer (factorSchema sourceOwner) p.1 p.2.1.residue
    then p.2.1.counter else 0) (context cell sourceOwner)
  writer := .map (fun p : FactorData × State =>
    TemporalFactorRules.writer (factorSchema sourceOwner) p.1 p.2.1.residue) (context cell sourceOwner)
  residue := .map (fun s => s.1.residue) stateExpr
  sourcePresent := .map (fun s => decide (s.2=sourceOwner)) stateExpr
  withdrawal := ⟨cell,fun p => p.1.withdrawal⟩

def resourceSchema (sourceOwner : Owner) (names : Owner → CarrierId) : ResourceRuntime.Schema Factor Bool :=
  ⟨factors,[false,true],names sourceOwner,names (swapOwner sourceOwner)⟩

theorem resources_ready (cell : Owner) (sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (ha : (a cell).isSome = true) :
    ResourceRuntime.Ready (resources cell sourceOwner names) a := by
  refine ⟨?_,?_,?_⟩
  · intro k hk
    have he : k=cell := by
      simpa [resources,execution,rowExpr,context,activeData,sourceData,targetData,Expr.dependencies,
        Expr.reenv_dependencies] using hk
    subst k; exact ha
  · intro r k hk
    have he : k=cell := by
      simpa [resources,execution,updateExpr,context,activeData,sourceData,targetData,Expr.dependencies,
        Expr.reenv_dependencies] using hk
    subst k; exact ha
  · intro k hk
    have he : k=cell := by
      simpa [resources,ResourceRuntime.Raw.readDependencies,stateExpr,context,activeData,sourceData,
        targetData,Expr.dependencies,Expr.reenv_dependencies] using hk
    subst k; exact ha

theorem actual_source_absence (cell : Owner) (sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (s : Frame.State) :
    (resources cell sourceOwner names).sourcePresent.eval a (pack (s,swapOwner sourceOwner)) () = some false := by
  cases sourceOwner <;> rfl

theorem actual_target_ownership (cell : Owner) (sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (p : Input × Input) (hp : a cell=some p)
    (s : Frame.State) :
    (resources cell sourceOwner names).accounts.eval a (pack (s,swapOwner sourceOwner)) () = some
      (fun r : Bool => if r then
        ⟨some (names p.1.temporal.resource.owner),true,if s.funded then p.1.temporal.ledger.initial else 0⟩
        else ⟨none,false,0⟩) := by
  have hc := context_evaluation cell sourceOwner a p hp (pack (s,swapOwner sourceOwner))
  simp only [resources,Expr.eval,hc,pack,ite_true,Option.map_some,decide_true]

theorem actual_target_charge (cell : Owner) (sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (p : Input × Input) (hp : a cell=some p)
    (s : Frame.State) (d : Unit) (act : Bool) :
    (resources cell sourceOwner names).charge.eval a (pack (s,swapOwner sourceOwner)) (d,act) = some
      (⟨names p.1.temporal.resource.owner,[true],
        (fun r => if r then p.1.temporal.ledger.cost else 0),
        (fun r => if r then p.1.temporal.ledger.recharge else 0)⟩ : ResourceRuntime.Charge Bool) := by
  have hc := context_evaluation cell sourceOwner a p hp (pack (s,swapOwner sourceOwner))
  simp only [resources,Expr.eval,Expr.reenv_eval,hc,pack,ite_true,Option.map_some]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
