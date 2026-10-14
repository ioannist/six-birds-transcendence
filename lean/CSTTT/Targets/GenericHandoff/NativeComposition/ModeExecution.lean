import CSTTT.Targets.GenericHandoff.NativeComposition.Frame
import CSTTT.Targets.GenericHandoff.NativeComposition.SourceMemory

/-! Actual shared source/target execution. Carrier mode is part of the run.
Rows and updates read the assigned primitive source copy or current target;
reception changes mode and duplicates the ACTUAL incoming history residue. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter
abbrev State := Frame.State × Owner
abbrev Registers := RegisterInterpreter.Registers Unit (fun _ => State)
def pack (s : State) : Registers := fun _ => s

def sourceData (cell : Owner) : Expr Owner MemoryValue Unit (fun _ => State) Unit FactorData :=
  .map (fun p => p.2.temporal) (.cell cell)
def targetData (cell : Owner) : Expr Owner MemoryValue Unit (fun _ => State) Unit FactorData :=
  .map (fun p => p.1.temporal) (.cell cell)
def activeData (cell : Owner) (sourceOwner : Owner) :
    Expr Owner MemoryValue Unit (fun _ => State) Unit FactorData :=
  .choose (.map (fun s => decide (s.2 = swapOwner sourceOwner)) (.register ()))
    (targetData cell) (sourceData cell)
def context (cell : Owner) (sourceOwner : Owner) :
    Expr Owner MemoryValue Unit (fun _ => State) Unit (FactorData × State) :=
  .pair (activeData cell sourceOwner) (.register ())

def rowExpr (cell : Owner) (sourceOwner : Owner) :
    Expr Owner MemoryValue Unit (fun _ => State) (Unit × Bool) (List (Factor × Rat)) :=
  .map (fun p => TemporalFactorRules.actualRows (factorSchema sourceOwner) p.1.1 p.1.2.1 p.2.2)
    (.pair ((context cell sourceOwner).reenv (fun _ => ())) (.environment id))
def updateExpr (cell : Owner) (sourceOwner : Owner) :
    Expr Owner MemoryValue Unit (fun _ => State) (Unit × Bool × Factor) State :=
  .map (fun p => (TemporalFactorRules.update (factorSchema sourceOwner) p.1.1 p.1.2.1 p.2.2.1 p.2.2.2,p.1.2.2))
    (.pair ((context cell sourceOwner).reenv (fun _ => ())) (.environment id))
def execution (cell : Owner) (sourceOwner : Owner) :
    ResourceRuntime.Execution Owner MemoryValue Unit (fun _ => State) Unit Bool Factor :=
  ⟨[()],[false,true],factors,rowExpr cell sourceOwner,fun _ => updateExpr cell sourceOwner⟩

def routePath (d : FactorData) (h : History) : List Bool :=
  ((d.routes.find? (fun r => decide (r.id = h))).map TemporalFactorRules.Route.eventPath).getD []

def initializer (cell : Owner) (sourceOwner : Owner) (start : Nat) :
    RegisterInitialization.InitialProgram Owner MemoryValue Unit (fun _ => State) History :=
  fun _ => .map (fun p : FactorData × History =>
    ((⟨(p.1.histories p.2).getD 0 p.2,start,start,(p.1.histories p.2,routePath p.1 p.2),
      p.1.receiverFunded && p.1.resource.rechargeAvailable && decide (p.1.ledger.initial ≥ p.1.ledger.cost)⟩ : Frame.State),sourceOwner))
    (.pair (.map (fun p : Input × Input => p.2.temporal) (.cell cell)) (.environment id))

def histories (cell : Owner) :
    StaticView Owner MemoryValue (History → List (Unit × Bool × Factor)) :=
  ⟨.map (fun d : FactorData => fun h =>
      ((d.histories h).zip ((d.histories h).drop 1)).map (fun e => ((),d.policy e.1,e.2)))
    (.map (fun p => p.2.temporal) (.cell cell))⟩

def receiveExpr (cell : Owner) (sourceOwner : Owner) :
    Expr Owner MemoryValue Unit (fun _ => State) (History × Route) State :=
  .map (fun p : FactorData × State =>
    (({p.2.1 with
      residue := (p.2.1.residue.1++p.2.1.residue.1,p.2.1.residue.2)
      funded := p.2.1.funded && p.1.resource.rechargeAvailable && decide (p.1.ledger.initial ≥ p.1.ledger.cost)} : Frame.State),
      swapOwner sourceOwner))
    (.pair ((targetData cell).reenv (fun _ => ())) (.register ()))

/-- Complete actual data selection, including arbitrary unbounded states. -/
theorem context_evaluation (cell : Owner) (sourceOwner : Owner) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell = some p) (x : Registers) :
    (context cell sourceOwner).eval a x () = some
      ((if (x ()).2 = swapOwner sourceOwner then p.1.temporal else p.2.temporal),x ()) := by
  by_cases hm : (x ()).2 = swapOwner sourceOwner
  all_goals simp [context,activeData,sourceData,targetData,Expr.eval,hp,hm]

theorem mode_update_evaluation (cell : Owner) (sourceOwner : Owner) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell = some p) (x : Registers) (d : Unit) (act : Bool) (o : Factor) :
    (updateExpr cell sourceOwner).eval a x (d,act,o) = some
      (TemporalFactorRules.update (factorSchema sourceOwner)
        (if (x ()).2 = swapOwner sourceOwner then p.1.temporal else p.2.temporal) (x ()).1 act o,(x ()).2) := by
  have h := context_evaluation cell sourceOwner a p hp x
  simp [updateExpr,Expr.eval,Expr.reenv_eval,h]

theorem mode_row_evaluation (cell : Owner) (sourceOwner : Owner) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell = some p) (x : Registers) (d : Unit) (act : Bool) :
    (rowExpr cell sourceOwner).eval a x (d,act) = some
      (TemporalFactorRules.actualRows (factorSchema sourceOwner)
        (if (x ()).2 = swapOwner sourceOwner then p.1.temporal else p.2.temporal) (x ()).1 act) := by
  have h := context_evaluation cell sourceOwner a p hp x
  simp [rowExpr,Expr.eval,Expr.reenv_eval,h]

theorem actual_receive (cell : Owner) (sourceOwner : Owner) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell = some p) (x : Registers) (hist : History) (rid : Route) :
    (receiveExpr cell sourceOwner).eval a x (hist,rid) = some
      (({(x ()).1 with
        residue := ((x ()).1.residue.1++(x ()).1.residue.1,(x ()).1.residue.2)
        funded := (x ()).1.funded && p.1.temporal.resource.rechargeAvailable &&
          decide (p.1.temporal.ledger.initial ≥ p.1.temporal.ledger.cost)} : Frame.State),swapOwner sourceOwner) := by
  simp [receiveExpr,targetData,Expr.eval,Expr.reenv_eval,hp]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
