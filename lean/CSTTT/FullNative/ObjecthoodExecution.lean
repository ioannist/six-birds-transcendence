import CSTTT.FullNative.ObjecthoodDefect
namespace CSTTT.FullNative.Objecthood
open CSTTT.TargetTheory.GenericHandoff FixedPointVerifier
set_option autoImplicit false
open AccountExecution PhysicalExecution
/-! The C1 matrix is derived from actual funded execution rows. No stationary
claim is made for the increasing receipt or environmental-cursor registers. -/
def actualP (x : Execution) (t : State) : Rat :=
  ((normalizedRows renewable x false).map fun e =>
    if e.1.resident.current=t then e.2 else 0).sum

theorem actual_matrix (x : Execution) (h : sector x) : actualP x=P x.resident.current := by
  funext t
  unfold actualP P
  simp only [normalizedRows,sector_rows x h false,List.map_map,Function.comp_def]
  rfl

theorem source_actual_matrix : actualP source=P source.resident.current :=
  actual_matrix source source_sector

theorem successors_actual_matrix :
    actualP ⟨SnapshotExecution.autonomousSiblings.accounts,SnapshotExecution.activatedLocal 1⟩=
      P (SnapshotExecution.activatedLocal 1).current ∧
    actualP ⟨SnapshotExecution.autonomousSiblings.accounts,SnapshotExecution.activatedLocal 2⟩=
      P (SnapshotExecution.activatedLocal 2).current :=
  ⟨actual_matrix _ SnapshotExecution.siblings_actual_sectors.1,
    actual_matrix _ SnapshotExecution.siblings_actual_sectors.2⟩
end CSTTT.FullNative.Objecthood
