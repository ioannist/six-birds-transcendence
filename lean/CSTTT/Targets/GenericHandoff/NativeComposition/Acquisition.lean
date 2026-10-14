import CSTTT.Targets.GenericHandoff.NativeComposition.Resources
import CSTTT.Targets.GenericHandoff.SupportedAcquisitionSequence

/-! Native acquisition consumes the copied source primitives for the assigned
word and the current target primitives for reception. The same mode-aware
execution supplies the acquisition rows and the resource game. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter

/-- The mixed clock counts the executed source word, and the exit adds its
actual post-exit step. Native stride1/2 gives clocks0,1,2 and2,5,6. -/
def clock (start stride : Nat) (s : Stage) :=
  if s.val=0 then start else if s.val=1 then start+(2*stride-1) else start+2*stride

def acquisitionSchema (sourceOwner : Owner) (names : Owner → CarrierId) (start stride : Nat) :
    AcquisitionExecution.Schema Stage Bool History Route :=
  ⟨stages,[false,true],factors,factors,0,2,names sourceOwner,names (swapOwner sourceOwner),clock start stride⟩

def acquisitionRoutes (p : Input × Input) (rid : Route) : AcquisitionExecution.Route History Bool :=
  match TemporalFactorRules.route p.2.temporal rid with
  | some r => ⟨r.history,r.eventPath⟩
  | none => ⟨rid,[]⟩

def acquisitionEvents (start stride : Nat) (p : Input × Input) (id : Bool) :
    AcquisitionExecution.Event Stage :=
  match TemporalFactorRules.event p.2.temporal id with
  | some e => ⟨e.fromStage,e.toStage,(!id && p.1.receiver.sourcePresent),
      p.1.receiver.targetFunded,e.strictStep,e.atomic,
      clock start stride e.toStage - clock start stride e.fromStage⟩
  | none => ⟨0,0,false,false,false,false,0⟩

def acquisition (cell sourceOwner : Owner) (start stride : Nat) :
    AcquisitionExecution.Raw Owner MemoryValue Unit (fun _ => State) Unit Bool Factor Stage Bool History Route where
  initializer := initializer cell sourceOwner start
  histories := histories cell
  routes := ⟨cell,acquisitionRoutes⟩
  events := ⟨cell,acquisitionEvents start stride⟩
  realized := ⟨cell,fun p => p.2.temporal.realized⟩
  receiver := ⟨cell,fun p => p.1.receiver⟩
  receive := fun _ => receiveExpr cell sourceOwner
  arrivalResponse := .literal ((),false)
  execution := execution cell sourceOwner

theorem acquisition_ready (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (ha : (a cell).isSome = true) :
    AcquisitionExecution.Ready (acquisition cell sourceOwner start stride) a := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k hk
    have he : k=cell := by
      simpa [acquisition,AcquisitionExecution.Raw.dependencies,histories,StaticView.dependencies,
        Expr.dependencies] using hk
    subst k; exact ha
  · intro r k hk
    have he : k=cell := by simpa [acquisition,initializer,Expr.dependencies] using hk
    subst k; exact ha
  · intro k hk
    have he : k=cell := by
      simpa [acquisition,execution,rowExpr,context,activeData,sourceData,targetData,Expr.dependencies,
        Expr.reenv_dependencies] using hk
    subst k; exact ha
  · intro r k hk
    have he : k=cell := by
      simpa [acquisition,execution,updateExpr,context,activeData,sourceData,targetData,Expr.dependencies,
        Expr.reenv_dependencies] using hk
    subst k; exact ha
  · intro r k hk
    have he : k=cell := by
      simpa [acquisition,receiveExpr,targetData,Expr.dependencies,Expr.reenv_dependencies] using hk
    subst k; exact ha

def initialized (p : Input × Input) (sourceOwner : Owner) (start : Nat) (hist : History) : State :=
  ((⟨(p.2.temporal.histories hist).getD 0 hist,start,start,
    (p.2.temporal.histories hist,routePath p.2.temporal hist),
    p.2.temporal.receiverFunded && p.2.temporal.resource.rechargeAvailable &&
      decide (p.2.temporal.ledger.initial ≥ p.2.temporal.ledger.cost)⟩ : Frame.State),sourceOwner)

theorem acquisition_initial (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (h : AcquisitionExecution.Ready (acquisition cell sourceOwner start stride) a)
    (p : Input × Input) (hp : a cell=some p) (hist : History) :
    AcquisitionExecution.initial (acquisition cell sourceOwner start stride) a h hist =
      pack (initialized p sourceOwner start hist) := by
  funext r
  have he := RegisterInitialization.initial_eq (acquisition cell sourceOwner start stride).initializer a h.2.1 hist r
  simp only [RegisterInitialization.evaluate,acquisition,initializer,Expr.eval,hp,
    Option.map_some] at he
  exact (Option.some.inj he).symm

theorem acquisition_update (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (h : AcquisitionExecution.Ready (acquisition cell sourceOwner start stride) a)
    (p : Input × Input) (hp : a cell=some p) (x : Registers) (d : Unit) (act : Bool) (o : Factor) :
    AcquisitionExecution.update (acquisition cell sourceOwner start stride) a h x d act o =
      pack (TemporalFactorRules.update (factorSchema sourceOwner)
        (if (x ()).2=swapOwner sourceOwner then p.1.temporal else p.2.temporal) (x ()).1 act o,(x ()).2) := by
  funext r
  have he := checked_execute_eq (acquisition cell sourceOwner start stride).execution.program a h.2.2.2.1 x (d,act,o) r
  simp only [execute,acquisition,execution] at he
  rw [mode_update_evaluation cell sourceOwner a p hp] at he
  exact (Option.some.inj he).symm

theorem acquisition_rows (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (p : Input × Input) (hp : a cell=some p)
    (x : Registers) (d : Unit) (act : Bool) :
    AcquisitionExecution.rows (acquisition cell sourceOwner start stride) a x d act =
      TemporalFactorRules.actualRows (factorSchema sourceOwner)
        (if (x ()).2=swapOwner sourceOwner then p.1.temporal else p.2.temporal) (x ()).1 act := by
  unfold AcquisitionExecution.rows
  rw [show (acquisition cell sourceOwner start stride).execution.row = rowExpr cell sourceOwner from rfl,
    mode_row_evaluation cell sourceOwner a p hp]
  rfl

def received (p : Input × Input) (sourceOwner : Owner) (x : State) : State :=
  (({x.1 with
      residue := (x.1.residue.1++x.1.residue.1,x.1.residue.2)
      funded := x.1.funded && p.1.temporal.resource.rechargeAvailable &&
        decide (p.1.temporal.ledger.initial ≥ p.1.temporal.ledger.cost)} : Frame.State),swapOwner sourceOwner)

theorem acquisition_receive (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (h : AcquisitionExecution.Ready (acquisition cell sourceOwner start stride) a)
    (p : Input × Input) (hp : a cell=some p) (x : Registers) (hist : History) (rid : Route) :
    AcquisitionExecution.receive (acquisition cell sourceOwner start stride) a h x hist rid =
      pack (received p sourceOwner (x ())) := by
  funext r
  have he := checked_execute_eq (acquisition cell sourceOwner start stride).receive a h.2.2.2.2 x (hist,rid) r
  simp only [execute,acquisition] at he
  rw [actual_receive cell sourceOwner a p hp] at he
  exact (Option.some.inj he).symm

theorem consumed_missing (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (hm : a cell=none) :
    ¬ AcquisitionExecution.Ready (acquisition cell sourceOwner start stride) a := by
  apply AcquisitionExecution.missing_dependency_rejected _ a cell _ hm
  simp [acquisition,AcquisitionExecution.Raw.dependencies]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
