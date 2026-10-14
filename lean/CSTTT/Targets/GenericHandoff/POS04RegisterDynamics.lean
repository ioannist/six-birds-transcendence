import CSTTT.Targets.GenericHandoff.RegisterFuture
import CSTTT.Targets.GenericHandoff.POS04ExactGameGuards
import CSTTT.POS04.Assigned.C6ActualFutureEquivalence

/-! POS-04 specialization of polymorphic raw register instructions.
No assignment cell contains a future, observer, updater or verdict. The actual
ambient outcome is written to the factor register; no predictive representative
is substituted. Proofs quantify over arbitrary partial assignments, subject
only to presence of the primitives actually consumed by the expression.
This is the run-component adapter, not the polymorphic acquisition/assembly. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RegisterDynamics
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH
open RegisterInterpreter

inductive Register where | factor | counter | ticks | residue | funded deriving DecidableEq

def RegisterValue : Register → Type
  | .factor => Ambient
  | .counter | .ticks => Nat
  | .residue => List KState × List EventId
  | .funded => Bool

def encode (r : Run6) : Registers Register RegisterValue
  | .factor => r.factor
  | .counter => r.counter
  | .ticks => r.ticks
  | .residue => r.residue
  | .funded => r.funded

def decodeRun (r : Registers Register RegisterValue) : Run6 :=
  ⟨r .factor,r .counter,r .ticks,r .residue,r .funded⟩

@[simp] theorem decode_encode (r : Run6) : decodeRun (encode r) = r := by cases r; rfl
@[simp] theorem encode_decode (r : Registers Register RegisterValue) : encode (decodeRun r) = r := by
  funext k; cases k <;> rfl

abbrev E (Env X : Type) := Expr Cell Value Register RegisterValue Env X
abbrev StepEnv := LaneDisturbance × Action × Ambient

def program (tag : Tag) : Program Cell Value Register RegisterValue StepEnv
  | .factor => .environment (fun e => e.2.2)
  | .counter => .map (fun (n : Nat) => n + 1) (.register Register.counter)
  | .ticks => .map (fun (p : Nat × (KState → Action → Nat) × Ambient × Action) => p.1 + match p.2.2.1 with
        | .inK s => p.2.1 s p.2.2.2
        | _ => 0)
      (.pair (.register Register.ticks) (.pair (.cell (Cell.ticks tag))
        (.pair (.register Register.factor) (.environment (fun e => e.2.1)))))
  | .residue => .register Register.residue
  | .funded => .map (fun (p : Bool × Ledger) => p.1 && decide
      (p.2.initialBudget - p.2.actionCost + p.2.rechargePerAction > 0))
      (.pair (.register Register.funded) (.cell Cell.maintenance))

def rowExpression (tag : Tag) : E (LaneDisturbance × Action) (List (Ambient × Rat)) :=
  .map (fun (p : (KState → Action → List (Ambient × Nat)) × Ambient × Action) => match p.2.1 with
      | .inK s => (p.1 s p.2.2).map fun e => (e.1,(e.2 : Rat)/4)
      | _ => [])
    (.pair (.cell (Cell.rows tag)) (.pair (.register Register.factor) (.environment Prod.snd)))

def predictiveExpression (tag : Tag) : E Unit CSTTT.POS04.PredictiveNow :=
  .map (fun (p : (KState → Nat) × (KState → Action → List (Ambient × Nat)) × (Ambient → Bool) × Ambient) => match p.2.2.2 with
    | .inK s => .active (p.1 s,actions.map fun a => (p.2.1 s a).map fun e => p.2.2.1 e.1)
    | .p2w0 => .exit2
    | .p5w1 => .exit5)
    (.pair (.cell Cell.positions) (.pair (.cell (Cell.rows tag)) (.pair (.cell Cell.hazards) (.register Register.factor))))

def writerExpression (tag : Tag) : E Unit Bool :=
  .map (fun (p : List Route × (HistoryId → List KState) × (Tag → RouteId → Bool) × (List KState × List EventId)) =>
    let tuple := fun (id : RouteId) => (p.1.find? (fun r => r.id == id)).map fun r => (p.2.1 r.sourceHistory,r.eventPath)
    if tuple .a = some p.2.2.2 then p.2.2.1 tag .a
    else if tuple .b = some p.2.2.2 then p.2.2.1 tag .b else false)
    (.pair (.cell Cell.routeTable) (.pair (.cell Cell.histories) (.pair (.cell Cell.writers) (.register Register.residue))))

def recordExpression (tag : Tag) : E Unit Nat :=
  .map (fun (p : Bool × Bool × Nat) => if p.1 && p.2.1 then p.2.2 else 0)
    (.pair (.register Register.funded) (.pair (writerExpression tag) (.register Register.counter)))

def readouts (tag : Tag) : RegisterFuture.Readouts Cell Value Register RegisterValue
    CSTTT.POS04.PredictiveNow (List KState × List EventId) Bool :=
  ⟨predictiveExpression tag,.register Register.counter,.register Register.ticks,.register Register.counter,
   writerExpression tag,recordExpression tag,.register Register.residue,.register Register.funded,
   .map (fun (r : ResourceData) => tagCarrierId r.owner) (.cell (Cell.resources tag))⟩

/-- O core dependencies do NOT include hazards; full temporal readouts do. -/
def coreDependencies (tag : Tag) : List Cell := [.rows tag,.ticks tag,.maintenance]
def temporalDependencies (tag : Tag) : List Cell :=
  coreDependencies tag ++ [.positions,.hazards,.routeTable,.histories,.writers,.resources tag]

/-- Presence gives an exact assigned value, not permission to use a fallback. -/
theorem cell_value {a : CSTTT.POS04.Assigned.Assignment} {k : Cell}
    (h : (a k).isSome = true) : a k = some ((a k).getD (canonicalValue k)) := by
  cases he : a k with
  | none => simp [he] at h
  | some v => rfl

set_option maxRecDepth 4096

theorem program_ready (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : Complete (coreDependencies tag) a) : ProgramReady (program tag) a := by
  intro r k hk
  cases r <;> simp [program,Expr.dependencies] at hk
  · subst k; exact h _ (by simp [coreDependencies])
  · subst k; exact h _ (by simp [coreDependencies])

/-- Each coordinate follows the ACTUAL assigned C6 updater, on every run,
action and ambient outcome, not only positive or canonical states. -/
theorem program_actual (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : Complete (coreDependencies tag) a) (r : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    execute (program tag) a (encode r) (d,act,o) =
      fun k => some (encode (actualUpdate6 (runInputs6 a tag) r act o) k) := by
  have ht := cell_value (h (.ticks tag) (by simp [coreDependencies]))
  have hl := cell_value (h .maintenance (by simp [coreDependencies]))
  funext k
  cases k <;> simp only [execute,program,Expr.eval,encode,Option.map_some]
  · rfl
  · rfl
  · rw [ht]
    cases tag <;> cases hf : r.factor <;> simp only [actualUpdate6,delta6,hf] <;> rfl
  · rfl
  · rw [hl]
    rfl

/-- Total interpreter equality is derived from the Option execution equation.
No separately supplied total updater appears in the raw component. -/
theorem checked_actual (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : Complete (coreDependencies tag) a) (r : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    checkedExecute (program tag) a (program_ready a tag h) (encode r) (d,act,o) =
      encode (actualUpdate6 (runInputs6 a tag) r act o) := by
  funext k
  exact Option.some.inj ((checked_execute_eq (program tag) a (program_ready a tag h)
    (encode r) (d,act,o) k).symm.trans (congrFun (program_actual a tag h r d act o) k))

theorem row_eval (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : (a (.rows tag)).isSome = true) (r : Run6) (d : LaneDisturbance) (act : Action) :
    (rowExpression tag).eval a (encode r) (d,act) =
      some ((row6 (runInputs6 a tag) r.factor act).map fun e => (e.1,(e.2 : Rat)/4)) := by
  have hr := cell_value h
  simp only [rowExpression,Expr.eval,encode]
  rw [hr]
  cases tag <;> cases r.factor <;> simp only [row6] <;> rfl

theorem predictive_eval (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : Complete (temporalDependencies tag) a) (r : Run6) :
    (predictiveExpression tag).eval a (encode r) () = some (predictive6 (runInputs6 a tag) r.factor) := by
  have hp := cell_value (h .positions (by simp [temporalDependencies]))
  have hr := cell_value (h (.rows tag) (by simp [temporalDependencies,coreDependencies]))
  have hh := cell_value (h .hazards (by simp [temporalDependencies]))
  simp only [predictiveExpression,Expr.eval,encode]
  rw [hp,hr,hh]
  cases tag <;> cases r.factor <;> simp only [predictive6] <;> rfl

theorem writer_eval (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : Complete (temporalDependencies tag) a) (r : Run6) :
    (writerExpression tag).eval a (encode r) () = some (writer6 (runInputs6 a tag) tag r.residue) := by
  have hr := cell_value (h .routeTable (by simp [temporalDependencies]))
  have hh := cell_value (h .histories (by simp [temporalDependencies]))
  have hw := cell_value (h .writers (by simp [temporalDependencies]))
  simp only [writerExpression,Expr.eval,encode]
  rw [hr,hh,hw]
  rfl

theorem record_eval (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : Complete (temporalDependencies tag) a) (r : Run6) :
    (recordExpression tag).eval a (encode r) () =
      some ((observation6 (runInputs6 a tag) tag r).endogenousRecordCount) := by
  simp only [recordExpression,Expr.eval,encode,writer_eval a tag h r]
  rfl

/-- Missing-input guards range over every consumed cell of every instruction.
The static expression namespaces contain no default/canonical value reads. -/
theorem missing_program_guard (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (r : Register) (k : Cell) (hk : k ∈ (program tag r).dependencies) :
    ¬ ProgramReady (program tag) (CSTTT.POS04.Assigned.put a k none) :=
  missing_program_rejected _ _ r k hk (CSTTT.POS04.Assigned.put_same _ _ _)

theorem missing_predictive_guard (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (k : Cell) (hk : k ∈ (predictiveExpression tag).dependencies) (r : Run6) :
    (predictiveExpression tag).eval (CSTTT.POS04.Assigned.put a k none) (encode r) () = none :=
  Expr.missing _ _ k hk (CSTTT.POS04.Assigned.put_same _ _ _) _ _

theorem missing_writer_guard (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (k : Cell) (hk : k ∈ (writerExpression tag).dependencies) (r : Run6) :
    (writerExpression tag).eval (CSTTT.POS04.Assigned.put a k none) (encode r) () = none :=
  Expr.missing _ _ k hk (CSTTT.POS04.Assigned.put_same _ _ _) _ _

end CSTTT.TargetTheory.GenericHandoff.POS04RegisterDynamics
