import CSTTT.Targets.GenericHandoff.CellReindex
import CSTTT.Targets.GenericHandoff.AcquisitionExecution

/-! Translate the whole raw acquisition instruction interface to a common
primitive namespace. No initialized, acquired or terminal run is supplied. -/
namespace CSTTT.TargetTheory.GenericHandoff.AcquisitionCellReindex
open RegisterInterpreter CellReindex
variable {SC TC R D A O Stage Id History RouteId : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type}

def execution (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (e : ResourceRuntime.Execution SC SV R RV D A O) :
    ResourceRuntime.Execution TC TV R RV D A O :=
  ⟨e.disturbances,e.actions,e.outcomes,expression cell value e.row,program cell value e.program⟩

def raw (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) :
    AcquisitionExecution.Raw TC TV R RV D A O Stage Id History RouteId where
  initializer := initializer cell value r.initializer
  histories := view cell value r.histories
  routes := cellView cell value r.routes
  events := cellView cell value r.events
  realized := cellView cell value r.realized
  receiver := cellView cell value r.receiver
  receive := program cell value r.receive
  arrivalResponse := expression cell value r.arrivalResponse
  execution := execution cell value r.execution

theorem dependencies (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) :
    (raw cell value r).dependencies = r.dependencies.map cell := by
  simp only [AcquisitionExecution.Raw.dependencies,raw,cellView,view_dependencies,
    CellReindex.dependencies,List.map_append,List.map_cons,List.map_nil]

theorem ready_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV) :
    AcquisitionExecution.Ready (raw cell value r) a ↔
      AcquisitionExecution.Ready r (pullback cell value a) := by
  unfold AcquisitionExecution.Ready
  rw [dependencies,complete_iff cell value r.dependencies a]
  simp only [raw,execution,initializer_ready_iff,CellReindex.ready_iff,program_ready_iff]

theorem initial_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV)
    (h : AcquisitionExecution.Ready (raw cell value r) a)
    (j : AcquisitionExecution.Ready r (pullback cell value a)) (hist : History) :
    AcquisitionExecution.initial (raw cell value r) a h hist =
      AcquisitionExecution.initial r (pullback cell value a) j hist :=
  initialize_equation cell value r.initializer a h.2.1 j.2.1 hist

theorem update_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV)
    (h : AcquisitionExecution.Ready (raw cell value r) a)
    (j : AcquisitionExecution.Ready r (pullback cell value a)) (run : Registers R RV)
    (d : D) (act : A) (o : O) :
    AcquisitionExecution.update (raw cell value r) a h run d act o =
      AcquisitionExecution.update r (pullback cell value a) j run d act o :=
  checked_execute_equation cell value r.execution.program a h.2.2.2.1 j.2.2.2.1 run (d,act,o)

theorem receive_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV)
    (h : AcquisitionExecution.Ready (raw cell value r) a)
    (j : AcquisitionExecution.Ready r (pullback cell value a)) (run : Registers R RV)
    (hist : History) (rid : RouteId) :
    AcquisitionExecution.receive (raw cell value r) a h run hist rid =
      AcquisitionExecution.receive r (pullback cell value a) j run hist rid :=
  checked_execute_equation cell value r.receive a h.2.2.2.2 j.2.2.2.2 run (hist,rid)

theorem rows_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV)
    (run : Registers R RV) (d : D) (act : A) :
    AcquisitionExecution.rows (raw cell value r) a run d act =
      AcquisitionExecution.rows r (pullback cell value a) run d act := by
  simp only [AcquisitionExecution.rows,raw,execution,evaluation]

theorem fold_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV)
    (h : AcquisitionExecution.Ready (raw cell value r) a)
    (j : AcquisitionExecution.Ready r (pullback cell value a)) (run : Registers R RV)
    (word : List (D × A × O)) :
    AcquisitionExecution.foldHistory (raw cell value r) a h run word =
      AcquisitionExecution.foldHistory r (pullback cell value a) j run word := by
  induction word generalizing run with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [AcquisitionExecution.foldHistory,ih,update_equation cell value r a h j]

theorem history_check_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV)
    (h : AcquisitionExecution.Ready (raw cell value r) a)
    (j : AcquisitionExecution.Ready r (pullback cell value a)) (run : Registers R RV)
    (word : List (D × A × O)) :
    AcquisitionExecution.HistoryCheck (raw cell value r) a h run word ↔
      AcquisitionExecution.HistoryCheck r (pullback cell value a) j run word := by
  have hr := funext (fun run => funext (fun d => funext (rows_equation cell value r a run d)))
  induction word generalizing run with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [AcquisitionExecution.HistoryCheck,
      hr,update_equation cell value r a h j,ih]
    rfl

theorem history_execution_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV)
    (h : AcquisitionExecution.Ready (raw cell value r) a)
    (j : AcquisitionExecution.Ready r (pullback cell value a)) (start final : Registers R RV)
    (word : List (D × A × O)) :
    AcquisitionExecution.HistoryExecution (raw cell value r) a h start word final ↔
      AcquisitionExecution.HistoryExecution r (pullback cell value a) j start word final := by
  constructor
  · intro he
    have hf := AcquisitionExecution.history_terminal_defined _ a h he
    rw [fold_equation cell value r a h j] at hf
    rw [hf]
    exact AcquisitionExecution.history_check_executes r _ j start word
      ((history_check_iff cell value r a h j start word).mp (AcquisitionExecution.history_execution_checked _ a h he))
  · intro he
    have hf := AcquisitionExecution.history_terminal_defined r _ j he
    rw [← fold_equation cell value r a h j] at hf
    rw [hf]
    exact AcquisitionExecution.history_check_executes _ a h start word
      ((history_check_iff cell value r a h j start word).mpr (AcquisitionExecution.history_execution_checked r _ j he))

theorem domain_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId)
    (cfg : AcquisitionExecution.Schema Stage Id History RouteId) :
    AcquisitionExecution.DomainCheck cfg (raw cell value r) ↔ AcquisitionExecution.DomainCheck cfg r := Iff.rfl

variable [DecidableEq Stage]
theorem arrival_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionExecution.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV)
    (h : AcquisitionExecution.Ready (raw cell value r) a)
    (j : AcquisitionExecution.Ready r (pullback cell value a))
    (cfg : AcquisitionExecution.Schema Stage Id History RouteId) (rid : RouteId) (arrived : Registers R RV) :
    AcquisitionExecution.Arrival cfg (raw cell value r) a h rid arrived ↔
      AcquisitionExecution.Arrival cfg r (pullback cell value a) j rid arrived := by
  simp only [AcquisitionExecution.Arrival,
    initial_equation cell value r a h j,receive_equation cell value r a h j,
    history_execution_iff cell value r a h j]
  simp only [raw,view_equation,cell_view_equation]

end CSTTT.TargetTheory.GenericHandoff.AcquisitionCellReindex
