import CSTTT.POS04.Assigned.C8Guards
import CSTTT.POS04.FutureDynamics

/-! G2b-3, dynamics/closure seam. Authority: M3_model_spec.md:22,30–33.
The factor quotient, probabilities, lifted updater, code and full observer are
computed from decoded cells. No future-model candidate is accepted. Budget is
the declared constant-budget POS-04 lift, not a variable-budget model; the
ledger's conservation equation is an explicit check below. Acceptance and
all-word sufficiency are reserved for the next seam. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

structure RunInputs6 where
  base : ExtraInputs
  ticks : KState → Action → Nat
  resource : ResourceData
  ledger : Ledger
  interface : List FutureObservable

def runInputs6 (a : Assignment) (tag : Tag) : RunInputs6 :=
  let decoded := decode (clauseScope tag .c6) a
  ⟨extraInputs decoded tag,
   (decoded (.ticks tag)).getD (canonicalValue (.ticks tag)),
   (decoded (.resources tag)).getD (canonicalValue (.resources tag)),
   (decoded .maintenance).getD (canonicalValue .maintenance),
   (decoded .interface).getD (canonicalValue .interface)⟩

def predictive6 (d : RunInputs6) : Ambient → PredictiveNow
  | .inK s => .active (predictive d.base.base s)
  | .p2w0 => .exit2
  | .p5w1 => .exit5
/-- Exact image, with first-occurrence class order from the raw ambient carrier. -/
def representatives6 (d : RunInputs6) := ambientStates.filter fun s =>
  decide (ambientStates.find? (fun t => decide (predictive6 d t = predictive6 d s)) = some s)
def outcomes6 (d : RunInputs6) := (representatives6 d).map (predictive6 d)
def representative6 (d : RunInputs6) (o : PredictiveNow) : Ambient :=
  (ambientStates.find? (fun s => decide (predictive6 d s = o))).getD (.inK .p0w0)
def row6 (d : RunInputs6) : Ambient → Action → List (Ambient × Nat)
  | .inK s, a => d.base.base.rows s a
  | .p2w0, _ => []
  | .p5w1, _ => []
def mass6 (d : RunInputs6) (s : Ambient) (a : Action) (o : PredictiveNow) : Nat :=
  ((row6 d s a).filter fun e => decide (predictive6 d e.1 = o)).foldl (fun n e => n + e.2) 0

theorem representative6_exact (d : RunInputs6) (o : PredictiveNow)
    (h : o ∈ outcomes6 d) : predictive6 d (representative6 d o) = o := by
  obtain ⟨s,hs,he⟩ := List.mem_map.mp h
  have hr := (List.mem_filter.mp hs).2
  simp only [decide_eq_true_eq] at hr
  unfold representative6
  rw [← he,hr]
  rfl

theorem outcomes6_cover (d : RunInputs6) (s : Ambient) : predictive6 d s ∈ outcomes6 d := by
  have hs : s ∈ ambientStates := by
    cases s with
    | inK k => cases k <;> decide
    | p2w0 => decide
    | p5w1 => decide
  have hf : (ambientStates.find? (fun t => decide (predictive6 d t = predictive6 d s))).isSome = true :=
    List.find?_isSome.mpr ⟨s,hs,by simp⟩
  generalize hr : ambientStates.find? (fun t => decide (predictive6 d t = predictive6 d s)) = r at hf
  cases r with
  | none => simp at hf
  | some t =>
    have hp' : decide (predictive6 d t = predictive6 d s) = true := List.find?_some (p := fun u => decide (predictive6 d u = predictive6 d s)) hr
    have hp : predictive6 d t = predictive6 d s := of_decide_eq_true hp'
    apply List.mem_map.mpr
    refine ⟨t,List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hr,?_⟩,hp⟩
    apply decide_eq_true
    rw [hp]
    exact hr

structure Run6 where
  factor : Ambient
  counter : Nat
  ticks : Nat
  residue : List KState × List EventId
  funded : Bool
  deriving DecidableEq, Repr

def budget6 (d : RunInputs6) : Nat := d.ledger.initialBudget
def budgetAfter6 (d : RunInputs6) := budget6 d - d.ledger.actionCost + d.ledger.rechargePerAction
def enabled6 (d : RunInputs6) (x : Run6) :=
  x.funded && d.resource.rechargeAvailable && decide (budget6 d ≥ d.ledger.actionCost)
def delta6 (d : RunInputs6) (s : Ambient) (a : Action) : Nat :=
  match s with | .inK k => d.ticks k a | .p2w0 | .p5w1 => 0
def writer6 (d : RunInputs6) (tag : Tag) (residue : List KState × List EventId) : Bool :=
  if routeTuple d.base .a = some residue then d.base.writers tag .a
  else if routeTuple d.base .b = some residue then d.base.writers tag .b
  else false


def update6 (d : RunInputs6) (x : Run6) (a : Action) (o : PredictiveNow) : Run6 :=
  ⟨representative6 d o,x.counter + 1,x.ticks + delta6 d x.factor a,
   x.residue,x.funded && decide (budgetAfter6 d > 0)⟩
def weight6 (d : RunInputs6) (x : Run6) (a : Action) (o : PredictiveNow) : Rat :=
  if enabled6 d x then (mass6 d x.factor a o : Rat) / 4 else 0

def code6 (d : RunInputs6) (x : Run6) : C6Code :=
  ⟨predictive6 d x.factor,x.counter,x.ticks % 2,x.residue,x.funded,d.resource.owner⟩
def observation6 (d : RunInputs6) (tag : Tag) (x : Run6) : C6Observation :=
  ⟨predictive6 d x.factor,x.counter,x.ticks % 2,x.counter,
   if x.funded && writer6 d tag x.residue then x.counter else 0,
   x.residue,x.funded,d.resource.owner⟩

def dynamics6 (a : Assignment) (tag : Tag) : RawFutureDynamics Run6 Action PredictiveNow :=
  let d := runInputs6 a tag
  ⟨outcomes6 d,weight6 d,update6 d⟩
def future6 (a : Assignment) (tag : Tag) : FullFutureModel Run6 Action PredictiveNow C6Code C6Observation :=
  let d := runInputs6 a tag
  ⟨outcomes6 d,code6 d,observation6 d tag,weight6 d,update6 d⟩

/-- The finite factor roots are the clause's ten-state domain, with each
available raw route tuple. Occurrence zero is L6a's declared c6Witness context;
future counters remain unbounded. Missing route references produce no root. -/
def roots6 (a : Assignment) (tag : Tag) : List Run6 :=
  let d := runInputs6 a tag
  routeIds.flatMap fun r => match routeTuple d.base r with
    | none => []
    | some residue => kernel.map fun s => ⟨.inK s,0,0,residue,d.base.receiver.funded⟩
abbrev Closure6 (a : Assignment) (tag : Tag) := FutureClosure (dynamics6 a tag) (roots6 a tag)

theorem dynamics6_check (a : Assignment) (tag : Tag) :
    FutureDynamicsCheck (future6 a tag) (dynamics6 a tag) (roots6 a tag) :=
  ⟨rfl,fun _ _ _ _ => ⟨rfl,rfl⟩⟩
theorem closure6_step {a : Assignment} {tag : Tag} {x : Run6}
    (hx : Closure6 a tag x) (act : Action) (o : PredictiveNow)
    (ho : o ∈ outcomes6 (runInputs6 a tag)) :
    Closure6 a tag (update6 (runInputs6 a tag) x act o) := FutureClosure.step hx act o ho

theorem run_inputs6_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c6) a b) : runInputs6 a tag = runInputs6 b tag := by
  unfold runInputs6
  rw [decoder_locality h]
theorem future6_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c6) a b) : future6 a tag = future6 b tag := by
  simp only [future6,run_inputs6_locality h]
theorem dynamics6_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c6) a b) : dynamics6 a tag = dynamics6 b tag := by
  simp only [dynamics6,run_inputs6_locality h]
theorem roots6_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c6) a b) : roots6 a tag = roots6 b tag := by
  simp only [roots6,run_inputs6_locality h]
theorem closure6_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c6) a b) (x : Run6) : Closure6 a tag x ↔ Closure6 b tag x := by
  simp only [Closure6,dynamics6_locality h,roots6_locality h]

/-- A defined run update has these laws for every state, hence throughout
its computed closure. Strict advancement and funded ledger conservation are
separate raw checks, not hidden in these algebraic equations. -/
structure UpdateLaws6 (d : RunInputs6) (tag : Tag) (x : Run6) (act : Action) (o : PredictiveNow) : Prop where
  factor : (update6 d x act o).factor = representative6 d o
  predictive : o ∈ outcomes6 d → predictive6 d (update6 d x act o).factor = o
  counter : (update6 d x act o).counter = x.counter + 1
  ticks : (update6 d x act o).ticks = x.ticks + delta6 d x.factor act
  tickPhase : (observation6 d tag (update6 d x act o)).tickPhase = (x.ticks + delta6 d x.factor act) % 2
  progress : (observation6 d tag (update6 d x act o)).cumulativeProgress = x.counter + 1
  residue : (update6 d x act o).residue = x.residue
  maintenance : (update6 d x act o).funded = (x.funded && decide (budgetAfter6 d > 0))
  owner : (observation6 d tag (update6 d x act o)).owner = d.resource.owner
  writer : writer6 d tag (update6 d x act o).residue = writer6 d tag x.residue
  record : (observation6 d tag (update6 d x act o)).endogenousRecordCount =
    if (x.funded && decide (budgetAfter6 d > 0)) && writer6 d tag x.residue then x.counter + 1 else 0
  enabled : enabled6 d (update6 d x act o) =
    ((x.funded && decide (budgetAfter6 d > 0)) && d.resource.rechargeAvailable &&
      decide (budget6 d ≥ d.ledger.actionCost))

theorem update_laws6 (d : RunInputs6) (tag : Tag) (x : Run6) (act : Action) (o : PredictiveNow) :
    UpdateLaws6 d tag x act o :=
  ⟨rfl,representative6_exact d o,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
def ClosureReadoutLaws6 (a : Assignment) (tag : Tag) : Prop :=
  ∀ x, Closure6 a tag x → ∀ act o, UpdateLaws6 (runInputs6 a tag) tag x act o
theorem closure_readout_laws6 (a : Assignment) (tag : Tag) : ClosureReadoutLaws6 a tag :=
  fun x _ act o => update_laws6 _ _ x act o

end CSTTT.POS04.Assigned
