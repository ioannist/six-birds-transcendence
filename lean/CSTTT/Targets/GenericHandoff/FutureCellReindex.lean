import CSTTT.Targets.GenericHandoff.CellReindex
import CSTTT.Targets.GenericHandoff.RegisterReadoutLaws

/-! Raw future and all readout-law instructions translated to a common
primitive namespace. Actual interpretations agree for every partial assignment
once the same computed pullback is used. Readiness is transported exactly. -/
namespace CSTTT.TargetTheory.GenericHandoff.FutureCellReindex
open RegisterInterpreter CellReindex CSTTT.TransportTheory
variable {SC TC R D A O P Residue Maintenance : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type}

def readouts (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Readouts SC SV R RV P Residue Maintenance) :
    RegisterFuture.Readouts TC TV R RV P Residue Maintenance :=
  ⟨expression cell value r.predictive,expression cell value r.order,
    expression cell value r.ticks,expression cell value r.progress,
    expression cell value r.writer,expression cell value r.record,
    expression cell value r.residue,expression cell value r.maintenance,
    expression cell value r.owner⟩

def raw (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance) :
    RegisterFuture.Raw TC TV R RV D A O P Residue Maintenance :=
  ⟨r.outcomes,r.actions,r.disturbances,r.tickPeriod,expression cell value r.row,
    program cell value r.program,readouts cell value r.readouts⟩

def recipes (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.StepRecipes SC SV R RV D A O P Residue Maintenance) :
    RegisterFuture.StepRecipes TC TV R RV D A O P Residue Maintenance :=
  fun f => expression cell value (r f)

theorem readouts_dependencies (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Readouts SC SV R RV P Residue Maintenance) :
    (readouts cell value r).dependencies = r.dependencies.map cell := by
  simp only [RegisterFuture.Readouts.dependencies,readouts,dependencies,List.map_append]

theorem ready_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance) (a : Assignment TC TV) :
    RegisterFuture.RawReady (raw cell value r) a ↔ RegisterFuture.RawReady r (pullback cell value a) := by
  simp only [RegisterFuture.RawReady,raw,CellReindex.ready_iff,program_ready_iff,
    readouts_dependencies,complete_iff cell value r.readouts.dependencies a]

theorem read_equation {X : Type} (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (e : Expr SC SV R RV Unit X) (a : Assignment TC TV)
    (h : Complete (expression cell value e).dependencies a)
    (run : Registers R RV) :
    RegisterFuture.read (expression cell value e) a h run =
      RegisterFuture.read e (pullback cell value a) ((CellReindex.ready_iff cell value e a).mp h) run := by
  apply Option.some.inj
  rw [← RegisterFuture.read_eq,← RegisterFuture.read_eq]
  exact evaluation cell value e a run ()

theorem observation_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance) (a : Assignment TC TV)
    (h : RegisterFuture.RawReady (raw cell value r) a)
    (j : RegisterFuture.RawReady r (pullback cell value a)) (run : Registers R RV) :
    RegisterFuture.observation (raw cell value r) a h run =
      RegisterFuture.observation r (pullback cell value a) j run := by
  simp only [RegisterFuture.observation,raw,readouts,read_equation]

theorem row_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance) (a : Assignment TC TV)
    (h : RegisterFuture.RawReady (raw cell value r) a)
    (j : RegisterFuture.RawReady r (pullback cell value a)) (run : Registers R RV) (da : D × A) :
    RegisterFuture.row (raw cell value r) a h run da =
      RegisterFuture.row r (pullback cell value a) j run da := by
  apply Option.some.inj
  rw [← RegisterFuture.row_eq,← RegisterFuture.row_eq]
  exact evaluation cell value r.row a run da

theorem next_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance) (a : Assignment TC TV)
    (h : RegisterFuture.RawReady (raw cell value r) a)
    (j : RegisterFuture.RawReady r (pullback cell value a)) (run : Registers R RV) (da : D × A) (o : O) :
    RegisterFuture.next (raw cell value r) a h run da o =
      RegisterFuture.next r (pullback cell value a) j run da o :=
  checked_execute_equation cell value r.program a h.2.1 j.2.1 run (da.1,da.2,o)

variable [DecidableEq O]
theorem weight_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance) (a : Assignment TC TV)
    (h : RegisterFuture.RawReady (raw cell value r) a)
    (j : RegisterFuture.RawReady r (pullback cell value a)) (run : Registers R RV) (da : D × A) (o : O) :
    RegisterFuture.weight (raw cell value r) a h run da o =
      RegisterFuture.weight r (pullback cell value a) j run da o := by
  simp only [RegisterFuture.weight,row_equation cell value r a h j]

theorem future_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance) (a : Assignment TC TV)
    (h : RegisterFuture.RawReady (raw cell value r) a)
    (j : RegisterFuture.RawReady r (pullback cell value a)) :
    RegisterFuture.future (raw cell value r) a h =
      RegisterFuture.future r (pullback cell value a) j := by
  have ho := funext (observation_equation cell value r a h j)
  have hw := funext (fun run => funext (fun da => funext (weight_equation cell value r a h j run da)))
  have hn := funext (fun run => funext (fun da => funext (next_equation cell value r a h j run da)))
  simp only [RegisterFuture.future,ho,hw,hn]
  rfl

theorem dynamics_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance) (a : Assignment TC TV)
    (h : RegisterFuture.RawReady (raw cell value r) a)
    (j : RegisterFuture.RawReady r (pullback cell value a)) :
    RegisterFuture.dynamics (raw cell value r) a h =
      RegisterFuture.dynamics r (pullback cell value a) j := by
  have hw := funext (fun run => funext (fun da => funext (weight_equation cell value r a h j run da)))
  have hn := funext (fun run => funext (fun da => funext (next_equation cell value r a h j run da)))
  simp only [RegisterFuture.dynamics,hw,hn]
  rfl

theorem field_expression (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Readouts SC SV R RV P Residue Maintenance) (f : RegisterFuture.Field) :
    RegisterFuture.fieldExpr (readouts cell value r) f =
      expression cell value (RegisterFuture.fieldExpr r f) := by
  cases f <;> rfl

omit [DecidableEq O] in
theorem field_law_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance)
    (law : RegisterFuture.StepRecipes SC SV R RV D A O P Residue Maintenance)
    (a : Assignment TC TV) (h : RegisterFuture.RawReady (raw cell value r) a)
    (j : RegisterFuture.RawReady r (pullback cell value a)) (run : Registers R RV)
    (da : D × A) (o : O) (f : RegisterFuture.Field) :
    RegisterFuture.FieldLaw (raw cell value r) (recipes cell value law) a h run da o f ↔
      RegisterFuture.FieldLaw r law (pullback cell value a) j run da o f := by
  simp only [RegisterFuture.FieldLaw,next_equation cell value r a h j]
  change (RegisterFuture.fieldExpr (readouts cell value r.readouts) f).eval a _ () = _ ↔ _
  rw [field_expression]
  simp only [recipes,evaluation]

omit [DecidableEq O] in
theorem positive_recipes_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance)
    (law : RegisterFuture.StepRecipes SC SV R RV D A O P Residue Maintenance)
    (a : Assignment TC TV) (h : RegisterFuture.RawReady (raw cell value r) a)
    (j : RegisterFuture.RawReady r (pullback cell value a)) (run : Registers R RV)
    (da : D × A) (o : O) :
    RegisterFuture.PositiveRecipes (raw cell value r) (recipes cell value law) a h run da o ↔
      RegisterFuture.PositiveRecipes r law (pullback cell value a) j run da o := by
  simp only [RegisterFuture.PositiveRecipes,recipes,evaluation,
    observation_equation cell value r a h j]
  simp only [raw,readouts,evaluation]

theorem readout_gate_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : RegisterFuture.Raw SC SV R RV D A O P Residue Maintenance)
    (law : RegisterFuture.StepRecipes SC SV R RV D A O P Residue Maintenance)
    (a : Assignment TC TV) (h : RegisterFuture.RawReady (raw cell value r) a)
    (j : RegisterFuture.RawReady r (pullback cell value a)) (roots : List (Registers R RV)) :
    RegisterFuture.ReadoutLawGate (raw cell value r) (recipes cell value law) a h roots ↔
      RegisterFuture.ReadoutLawGate r law (pullback cell value a) j roots := by
  simp only [RegisterFuture.ReadoutLawGate,RegisterFuture.ReadoutSupportCoverage,RegisterFuture.Closure,
    dynamics_equation cell value r a h j,
    field_law_iff cell value r law a h j,positive_recipes_iff cell value r law a h j,
    weight_equation cell value r a h j,row_equation cell value r a h j]
  rfl

end CSTTT.TargetTheory.GenericHandoff.FutureCellReindex
