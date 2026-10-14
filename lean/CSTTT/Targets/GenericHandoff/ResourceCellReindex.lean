import CSTTT.Targets.GenericHandoff.AcquisitionCellReindex
import CSTTT.Targets.GenericHandoff.ResourceRuntime

namespace CSTTT.TargetTheory.GenericHandoff.ResourceCellReindex
open RegisterInterpreter CellReindex
variable {SC TC R D A O Factor Res Residue : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type}
-- Class (b): every native instruction reads the shared translated primitive namespace.
def raw (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue) :
    ResourceRuntime.Raw TC TV R RV D A O Factor Res Residue where
  accounts := expression cell value r.accounts
  required := expression cell value r.required
  charge := expression cell value r.charge
  advances := expression cell value r.advances
  factor := expression cell value r.factor
  order := expression cell value r.order
  ticks := expression cell value r.ticks
  progress := expression cell value r.progress
  record := expression cell value r.record
  writer := expression cell value r.writer
  residue := expression cell value r.residue
  sourcePresent := expression cell value r.sourcePresent
  withdrawal := cellView cell value r.withdrawal
  execution := AcquisitionCellReindex.execution cell value r.execution
-- Class (b): exact all-field raw dependency translation.
theorem dependencies (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue) :
    (raw cell value r).readDependencies=r.readDependencies.map cell := by
  simp [ResourceRuntime.Raw.readDependencies,raw,CellReindex.dependencies,
    CellReindex.cellView,List.map_append]
-- Class (b): readiness equivalence on every partial shared primitive assignment.
theorem ready_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue) (a : Assignment TC TV) :
    ResourceRuntime.Ready (raw cell value r) a ↔ ResourceRuntime.Ready r (pullback cell value a) := by
  unfold ResourceRuntime.Ready
  rw [dependencies,complete_iff cell value r.readDependencies a]
  simp only [raw,AcquisitionCellReindex.execution,CellReindex.ready_iff,program_ready_iff]
-- Class (b): the actual updater is preserved, independently of derived state readouts.
theorem update_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue) (a : Assignment TC TV)
    (h : ResourceRuntime.Ready (raw cell value r) a)
    (j : ResourceRuntime.Ready r (pullback cell value a)) (run : Registers R RV) (d : D) (act : A) (o : O) :
    ResourceRuntime.update (raw cell value r) a h run d act o=
      ResourceRuntime.update r (pullback cell value a) j run d act o :=
  checked_execute_equation cell value r.execution.program a h.2.1 j.2.1 run (d,act,o)
-- Class (b): complete actual optional row, including all missing-input behavior.
theorem row_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue) (a : Assignment TC TV)
    (run : Registers R RV) (d : D) (act : A) :
    (raw cell value r).execution.row.eval a run (d,act)=
      r.execution.row.eval (pullback cell value a) run (d,act) :=
  evaluation cell value r.execution.row a run (d,act)
-- Class (b): no new support convention is introduced by primitive translation.
theorem rows_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue) (a : Assignment TC TV)
    (run : Registers R RV) (d : D) (act : A) :
    ResourceRuntime.rows (raw cell value r) a run d act=
      ResourceRuntime.rows r (pullback cell value a) run d act := by
  simp only [ResourceRuntime.rows,row_equation]
-- Class (b): whole finite-domain declaration is unchanged.
theorem domain_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue) (cfg : ResourceRuntime.Schema Factor Res) :
    ResourceRuntime.DomainCheck cfg (raw cell value r) ↔ ResourceRuntime.DomainCheck cfg r := Iff.rfl
-- Class (b): all six actual withdrawal roles and resource-set equations are preserved.
theorem withdrawal_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue)
    (cfg : ResourceRuntime.Schema Factor Res) (a : Assignment TC TV) :
    ResourceRuntime.WithdrawalCheck cfg (raw cell value r) a ↔
      ResourceRuntime.WithdrawalCheck cfg r (pullback cell value a) := by
  simp only [ResourceRuntime.WithdrawalCheck,raw,cell_view_equation]
-- Class (b): actual optional factor membership is preserved for every run.
theorem inside_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue)
    (cfg : ResourceRuntime.Schema Factor Res) (a : Assignment TC TV) (run : Registers R RV) :
    ResourceRuntime.Inside cfg (raw cell value r) a run ↔
      ResourceRuntime.Inside cfg r (pullback cell value a) run := by
  simp only [ResourceRuntime.Inside,raw,evaluation]
-- Class (b): all account ownership, strict balance, removed-resource and source-absence clauses survive.
theorem closed_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue)
    (cfg : ResourceRuntime.Schema Factor Res) (a : Assignment TC TV) (run : Registers R RV) :
    ResourceRuntime.ResourceClosed cfg (raw cell value r) a run ↔
      ResourceRuntime.ResourceClosed cfg r (pullback cell value a) run := by
  simp only [ResourceRuntime.ResourceClosed,raw,evaluation,cell_view_equation]
-- Class (b): actual selected action and the full vector resource ledger retain legality.
theorem legal_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue)
    (cfg : ResourceRuntime.Schema Factor Res) (a : Assignment TC TV) (run : Registers R RV) (d : D) (act : A) :
    ResourceRuntime.Legal cfg (raw cell value r) a run d act ↔
      ResourceRuntime.Legal cfg r (pullback cell value a) run d act := by
  simp only [ResourceRuntime.Legal,raw,AcquisitionCellReindex.execution,evaluation,cell_view_equation]
-- Class (b): the entire actual after-state law, including residue and next resource closure.
theorem step_law_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ResourceRuntime.Raw SC SV R RV D A O Factor Res Residue)
    (cfg : ResourceRuntime.Schema Factor Res) (a : Assignment TC TV)
    (h : ResourceRuntime.Ready (raw cell value r) a)
    (j : ResourceRuntime.Ready r (pullback cell value a)) (run : Registers R RV) (d : D) (act : A) (o : O) :
    ResourceRuntime.StepLaw cfg (raw cell value r) a h run d act o ↔
      ResourceRuntime.StepLaw cfg r (pullback cell value a) j run d act o := by
  unfold ResourceRuntime.StepLaw
  dsimp only
  rw [update_equation cell value r a h j,closed_iff]
  simp only [raw,evaluation,cell_view_equation]
end CSTTT.TargetTheory.GenericHandoff.ResourceCellReindex
