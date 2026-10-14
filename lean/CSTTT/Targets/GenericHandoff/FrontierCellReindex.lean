import CSTTT.Targets.GenericHandoff.AcquisitionCellReindex
import CSTTT.Targets.GenericHandoff.FutureCellReindex
import CSTTT.Targets.GenericHandoff.SemanticExecutionBridge

/-! Whole executed frame translation, including actual roots, all supported
histories, full future closure and every original validity/semantic obligation.
This preserves the raw program while changing its primitive namespace. -/
namespace CSTTT.TargetTheory.GenericHandoff.FrontierCellReindex
open RegisterInterpreter CellReindex CSTTT.TransportTheory
variable {SC TC R D A O P Residue Maintenance Stage Id History RouteId : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type}

def raw (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId) :
    ExecutionFrontier.Raw TC TV R RV D A O P Residue Maintenance Stage Id History RouteId :=
  ⟨AcquisitionCellReindex.raw cell value r.acquisition,
    FutureCellReindex.readouts cell value r.readouts,FutureCellReindex.recipes cell value r.recipes,
    r.tickPeriod,r.audit,r.schema,r.auditRoute⟩

theorem temporal_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId) :
    ExecutionFrontier.temporal (raw cell value r) = FutureCellReindex.raw cell value (ExecutionFrontier.temporal r) := rfl

theorem ready_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) :
    ExecutionFrontier.Ready (raw cell value r) a ↔ ExecutionFrontier.Ready r (pullback cell value a) := by
  unfold ExecutionFrontier.Ready
  rw [temporal_equation,FutureCellReindex.ready_iff]
  exact and_congr (AcquisitionCellReindex.ready_iff cell value r.acquisition a) Iff.rfl

theorem initial_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) (hist : History) :
    ExecutionFrontier.initial (raw cell value r) a h hist =
      ExecutionFrontier.initial r (pullback cell value a) j hist :=
  AcquisitionCellReindex.initial_equation cell value r.acquisition a h.1 j.1 hist

theorem roots_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) :
    ExecutionFrontier.roots (raw cell value r) a h = ExecutionFrontier.roots r (pullback cell value a) j := by
  simp only [ExecutionFrontier.roots,initial_equation cell value r a h j]
  rfl

theorem history_prefix_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (i : History × Nat) :
    ExecutionFrontier.historyPrefix (raw cell value r) a i =
      ExecutionFrontier.historyPrefix r (pullback cell value a) i := by
  simp only [ExecutionFrontier.historyPrefix,raw,AcquisitionCellReindex.raw,view_equation]

theorem snapshot_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) (i : History × Nat) :
    ExecutionFrontier.snapshot (raw cell value r) a h i =
      ExecutionFrontier.snapshot r (pullback cell value a) j i := by
  simp only [ExecutionFrontier.snapshot,history_prefix_equation,initial_equation cell value r a h j]
  exact AcquisitionCellReindex.fold_equation cell value r.acquisition a h.1 j.1 _ _

theorem observation_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) (i : History × Nat) :
    ExecutionFrontier.observation (raw cell value r) a h i =
      ExecutionFrontier.observation r (pullback cell value a) j i := by
  unfold ExecutionFrontier.observation
  rw [snapshot_equation cell value r a h j i]
  exact FutureCellReindex.observation_equation cell value (ExecutionFrontier.temporal r) a h.2 j.2 _

variable [DecidableEq O]
omit [DecidableEq O] in
theorem temporal_observation_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) (run : Registers R RV) :
    RegisterFuture.observation (ExecutionFrontier.temporal (raw cell value r)) a h.2 run =
      RegisterFuture.observation (ExecutionFrontier.temporal r) (pullback cell value a) j.2 run :=
  FutureCellReindex.observation_equation cell value (ExecutionFrontier.temporal r) a h.2 j.2 run

theorem dynamics_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) :
    RegisterFuture.dynamics (ExecutionFrontier.temporal (raw cell value r)) a h.2 =
      RegisterFuture.dynamics (ExecutionFrontier.temporal r) (pullback cell value a) j.2 :=
  FutureCellReindex.dynamics_equation cell value (ExecutionFrontier.temporal r) a h.2 j.2

theorem future_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) :
    RegisterFuture.future (ExecutionFrontier.temporal (raw cell value r)) a h.2 =
      RegisterFuture.future (ExecutionFrontier.temporal r) (pullback cell value a) j.2 :=
  FutureCellReindex.future_equation cell value (ExecutionFrontier.temporal r) a h.2 j.2

theorem weight_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) (run : Registers R RV) (da : D × A) (o : O) :
    RegisterFuture.weight (ExecutionFrontier.temporal (raw cell value r)) a h.2 run da o =
      RegisterFuture.weight (ExecutionFrontier.temporal r) (pullback cell value a) j.2 run da o :=
  FutureCellReindex.weight_equation cell value (ExecutionFrontier.temporal r) a h.2 j.2 run da o

omit [DecidableEq O] in
theorem update_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) (run : Registers R RV) (d : D) (act : A) (o : O) :
    AcquisitionExecution.update (raw cell value r).acquisition a h.1 run d act o =
      AcquisitionExecution.update r.acquisition (pullback cell value a) j.1 run d act o :=
  AcquisitionCellReindex.update_equation cell value r.acquisition a h.1 j.1 run d act o

omit [DecidableEq O] in
theorem rows_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (run : Registers R RV) (d : D) (act : A) :
    AcquisitionExecution.rows (raw cell value r).acquisition a run d act =
      AcquisitionExecution.rows r.acquisition (pullback cell value a) run d act :=
  AcquisitionCellReindex.rows_equation cell value r.acquisition a run d act

theorem closure_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) (run : Registers R RV) :
    ExecutionFrontier.Closure (raw cell value r) a h run ↔
      ExecutionFrontier.Closure r (pullback cell value a) j run := by
  unfold ExecutionFrontier.Closure RegisterFuture.Closure
  rw [roots_equation cell value r a h j,dynamics_equation cell value r a h j]

theorem prefix_check_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) (run : Registers R RV) (word : List (D × A × O)) :
    ExecutionFrontier.PrefixCheck (raw cell value r) a h run word ↔
      ExecutionFrontier.PrefixCheck r (pullback cell value a) j run word := by
  have hr := funext (fun run => funext (fun d => funext (rows_equation cell value r a run d)))
  induction word generalizing run with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [ExecutionFrontier.PrefixCheck]
    simp only [hr,weight_equation cell value r a h j,update_equation cell value r a h j,ih]
    rfl

theorem audit_check_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) :
    ExecutionFrontier.AuditCheck (raw cell value r) a h ↔
      ExecutionFrontier.AuditCheck r (pullback cell value a) j := by
  simp only [ExecutionFrontier.AuditCheck,history_prefix_equation,
    initial_equation cell value r a h j,prefix_check_iff cell value r a h j]
  simp only [raw,AcquisitionCellReindex.raw,view_equation]

omit [DecidableEq O] in
theorem execution_domain_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId) :
    ExecutionFrontier.ExecutionDomain (raw cell value r) ↔ ExecutionFrontier.ExecutionDomain r := Iff.rfl

theorem row_gate_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) :
    ExecutionFrontier.RowLawGate (raw cell value r) a h ↔
      ExecutionFrontier.RowLawGate r (pullback cell value a) j := by
  simp only [ExecutionFrontier.RowLawGate,closure_iff cell value r a h j,
    rows_equation cell value r a]
  rfl

variable [DecidableEq Stage]
omit [DecidableEq O] in
theorem paths_available_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) :
    ExecutionFrontier.PathsAvailable (raw cell value r) a ↔
      ExecutionFrontier.PathsAvailable r (pullback cell value a) := by
  simp only [ExecutionFrontier.PathsAvailable,raw,AcquisitionCellReindex.raw,cell_view_equation]

variable [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
omit [DecidableEq Stage] [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance] in
theorem readout_gate_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) :
    RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal (raw cell value r)) (raw cell value r).recipes a h.2
        (ExecutionFrontier.roots (raw cell value r) a h) ↔
      RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal r) r.recipes (pullback cell value a) j.2
        (ExecutionFrontier.roots r (pullback cell value a) j) := by
  rw [roots_equation cell value r a h j]
  exact FutureCellReindex.readout_gate_iff cell value (ExecutionFrontier.temporal r) r.recipes a h.2 j.2 _

theorem checks_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) :
    (ExecutionFrontier.AuditCheck (raw cell value r) a h ∧
      AcquisitionExecution.DomainCheck (raw cell value r).schema (raw cell value r).acquisition ∧
      ExecutionFrontier.ExecutionDomain (raw cell value r) ∧ ExecutionFrontier.PathsAvailable (raw cell value r) a ∧
      FutureLumping.OneStep (RegisterFuture.future (ExecutionFrontier.temporal (raw cell value r)) a h.2) ∧
      RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal (raw cell value r)) (raw cell value r).recipes a h.2
        (ExecutionFrontier.roots (raw cell value r) a h) ∧ ExecutionFrontier.RowLawGate (raw cell value r) a h) ↔
    (ExecutionFrontier.AuditCheck r (pullback cell value a) j ∧
      AcquisitionExecution.DomainCheck r.schema r.acquisition ∧ ExecutionFrontier.ExecutionDomain r ∧
      ExecutionFrontier.PathsAvailable r (pullback cell value a) ∧
      FutureLumping.OneStep (RegisterFuture.future (ExecutionFrontier.temporal r) (pullback cell value a) j.2) ∧
      RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal r) r.recipes (pullback cell value a) j.2
        (ExecutionFrontier.roots r (pullback cell value a) j) ∧ ExecutionFrontier.RowLawGate r (pullback cell value a) j) := by
  rw [audit_check_iff cell value r a h j,execution_domain_iff,paths_available_iff,
    row_gate_iff cell value r a h j,future_equation cell value r a h j,readout_gate_iff cell value r a h j]
  rfl

theorem valid_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) :
    ExecutionFrontier.Valid (raw cell value r) a ↔ ExecutionFrontier.Valid r (pullback cell value a) := by
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨(ready_iff cell value r a).mp h,
      (checks_iff cell value r a h ((ready_iff cell value r a).mp h)).mp hc⟩
  · rintro ⟨j,hc⟩
    exact ⟨(ready_iff cell value r a).mpr j,
      (checks_iff cell value r a ((ready_iff cell value r a).mpr j) j).mpr hc⟩

theorem semantic_checks_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionFrontier.Ready (raw cell value r) a)
    (j : ExecutionFrontier.Ready r (pullback cell value a)) :
    (ExecutionFrontier.AuditCheck (raw cell value r) a h ∧
      AcquisitionExecution.DomainCheck (raw cell value r).schema (raw cell value r).acquisition ∧
      ExecutionFrontier.ExecutionDomain (raw cell value r) ∧ ExecutionFrontier.PathsAvailable (raw cell value r) a ∧
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal (raw cell value r)) a h.2) ∧
      RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal (raw cell value r)) (raw cell value r).recipes a h.2
        (ExecutionFrontier.roots (raw cell value r) a h) ∧ ExecutionFrontier.RowLawGate (raw cell value r) a h) ↔
    (ExecutionFrontier.AuditCheck r (pullback cell value a) j ∧
      AcquisitionExecution.DomainCheck r.schema r.acquisition ∧ ExecutionFrontier.ExecutionDomain r ∧
      ExecutionFrontier.PathsAvailable r (pullback cell value a) ∧
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal r) (pullback cell value a) j.2) ∧
      RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal r) r.recipes (pullback cell value a) j.2
        (ExecutionFrontier.roots r (pullback cell value a) j) ∧ ExecutionFrontier.RowLawGate r (pullback cell value a) j) := by
  rw [audit_check_iff cell value r a h j,execution_domain_iff,paths_available_iff,
    row_gate_iff cell value r a h j,future_equation cell value r a h j,readout_gate_iff cell value r a h j]
  rfl

theorem semantic_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionFrontier.Raw SC SV R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) :
    ExecutionFrontier.SemanticReadout (raw cell value r) a ↔
      ExecutionFrontier.SemanticReadout r (pullback cell value a) := by
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨(ready_iff cell value r a).mp h,
      (semantic_checks_iff cell value r a h ((ready_iff cell value r a).mp h)).mp hc⟩
  · rintro ⟨j,hc⟩
    exact ⟨(ready_iff cell value r a).mpr j,
      (semantic_checks_iff cell value r a ((ready_iff cell value r a).mpr j) j).mpr hc⟩

end CSTTT.TargetTheory.GenericHandoff.FrontierCellReindex
