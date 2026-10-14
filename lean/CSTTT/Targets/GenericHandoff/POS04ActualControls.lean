import CSTTT.Targets.GenericHandoff.POS04ActualGame
import CSTTT.Targets.ComputedFIACH.LineagePackage

/-! Direct semantic controls and the finite-predicate comparison. A failed
sufficient check is not used to refute a game readout. C4–C7 remain surrogates.
The unrestricted partial-assignment equivalence is obstructed below; it is
not silently replaced with an equivalence on complete assignments. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ActualGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH

theorem package_deletion_dependencies :
    Complete POS04GameBinding.dependencies (image packageDeletion.assignment) := by decide

theorem package_deletion_c8_locality :
    C8Accept (withdrawnAssignment packageDeletion) .target ↔ C8Accept (withdrawnAssignment baseline) .target := by
  apply c8_accept_locality
  intro k hk
  cases k <;> try rfl
  case publishedC => simp [clauseScope] at hk

theorem package_deletion_operational_game : OperationalAutonomy packageDeletion := by
  have hrow : rows packageDeletion = rows baseline := by
    funext r d a
    simp only [rows,if_pos package_deletion_dependencies,if_pos baseline_dependencies]
    rfl
  have he : POS04GameBinding.Entries packageDeletion = POS04GameBinding.Entries baseline := by
    funext r
    unfold POS04GameBinding.Entries
    rw [show entries packageDeletion = entries baseline from by decide]
    rfl
  have hw : POS04GameBinding.Withdrawal packageDeletion = POS04GameBinding.Withdrawal baseline := by
    apply propext
    exact ⟨fun _ => ⟨baseline_dependencies,by decide⟩,
      fun _ => ⟨package_deletion_dependencies,by decide⟩⟩
  have hp : POS04GameBinding.OperationalAt packageDeletion = POS04GameBinding.OperationalAt baseline := by
    funext r
    apply propext
    simp only [POS04GameBinding.OperationalAt,package_deletion_c8_locality,
      package_deletion_operational_inputs]
  have hr : POS04GameBinding.ResourceClosed packageDeletion = POS04GameBinding.ResourceClosed baseline := by
    funext r
    apply propext
    simp only [POS04GameBinding.ResourceClosed,package_deletion_dependencies,baseline_dependencies,true_and]
    rfl
  have hl : POS04GameBinding.Legal packageDeletion = POS04GameBinding.Legal baseline := by
    funext r d a
    simp only [POS04GameBinding.Legal,hr]
    rfl
  change StrategyGame.GameReadout _ _ _ _ _ _ _ _
  rw [hrow,he,hw,hp,hr,hl]
  exact baseline_operational_autonomy

/-- The registered package-deletion control remains an O isolation witness
at the actual strategy readout, not merely at finite acceptance. -/
theorem package_control_games :
    ¬ FullAutonomy packageDeletion ∧ OperationalAutonomy packageDeletion :=
  ⟨package_deletion_rejects_full,package_deletion_operational_game⟩

/-- The baseline comparison is inhabited in both interpretations. It does
not establish an arbitrary-assignment equivalence. -/
theorem positive_comparison :
    AF baseline ∧ AO baseline ∧ FullAutonomy baseline ∧ OperationalAutonomy baseline :=
  ⟨baseline_AF,baseline_AO,baseline_full_autonomy,baseline_operational_autonomy⟩


theorem lineage_deletion_dependencies :
    Complete POS04GameBinding.dependencies (image lineageDeletion.assignment) := by decide

theorem lineage_deletion_rows : rows lineageDeletion = rows baseline := by
  funext r d a
  simp only [rows,if_pos lineage_deletion_dependencies,if_pos baseline_dependencies]
  rfl

theorem lineage_deletion_entries : POS04GameBinding.Entries lineageDeletion = POS04GameBinding.Entries baseline := by
  funext r
  unfold POS04GameBinding.Entries
  rw [show entries lineageDeletion = entries baseline from by decide]
  rfl

theorem lineage_deletion_withdrawal : POS04GameBinding.Withdrawal lineageDeletion = POS04GameBinding.Withdrawal baseline := by
  apply propext
  exact ⟨fun _ => ⟨baseline_dependencies,by decide⟩,fun _ => ⟨lineage_deletion_dependencies,by decide⟩⟩

theorem lineage_deletion_resources : POS04GameBinding.ResourceClosed lineageDeletion = POS04GameBinding.ResourceClosed baseline := by
  funext r
  apply propext
  simp only [POS04GameBinding.ResourceClosed,lineage_deletion_dependencies,baseline_dependencies,true_and]
  rfl

theorem lineage_deletion_legal : POS04GameBinding.Legal lineageDeletion = POS04GameBinding.Legal baseline := by
  funext r d a
  simp only [POS04GameBinding.Legal,lineage_deletion_resources]
  rfl

theorem lineage_deletion_operational_game : OperationalAutonomy lineageDeletion := by
  have hp : POS04GameBinding.OperationalAt lineageDeletion = POS04GameBinding.OperationalAt baseline := by
    funext r
    apply propext
    have hc : C8Accept (withdrawnAssignment lineageDeletion) .target ↔ C8Accept (withdrawnAssignment baseline) .target := by
      apply c8_accept_locality
      intro k hk
      cases k <;> try rfl
      case eventTable => simp [clauseScope] at hk
    simp only [POS04GameBinding.OperationalAt,hc,lineage_deletion_operational_inputs]
  change StrategyGame.GameReadout _ _ _ _ _ _ _ _
  rw [lineage_deletion_rows,lineage_deletion_entries,lineage_deletion_withdrawal,hp,
    lineage_deletion_resources,lineage_deletion_legal]
  exact baseline_operational_autonomy

/-- The package proof is recomputed on the edited assignment (C6/C7 inspect
its event cell), rather than conjoining the fixed positive package. -/
theorem lineage_deletion_run_package (r : Run) (hr : FactorContext baseline r) : PackageAt lineageDeletion r := by
  obtain ⟨s,hs⟩ := hr.2
  exact ⟨lineage_deletion_package,
    by rw [lineage_withdrawn_assignment]; exact lineage_assigned_package .target,
    ⟨s,hs,by rw [lineage_withdrawn_assignment]; unfold stateViewsCheck; decide⟩,
    fun a o => actual_update_laws6 _ _ _ _ _⟩

/-- Transport the already constructed actual-support invariant, preserving
its run contexts, choices and every actual branch. -/
def lineage_deletion_full_certificate : FullCertificate lineageDeletion where
  inside := baseline_full_certificate.inside
  withdrawn := by rw [lineage_deletion_withdrawal]; exact baseline_full_certificate.withdrawn
  entriesNonempty := by rw [lineage_deletion_entries]; exact baseline_full_certificate.entriesNonempty
  entriesInside r hr := baseline_full_certificate.entriesInside r (by rw [← lineage_deletion_entries]; exact hr)
  packageInside r hr := lineage_deletion_run_package r hr.1
  resourcesInside r hr := by rw [lineage_deletion_resources]; exact baseline_full_certificate.resourcesInside r hr
  response r hr d := by
    rw [lineage_deletion_legal,lineage_deletion_rows]
    exact baseline_full_certificate.response r hr d

theorem lineage_deletion_full_game : FullAutonomy lineageDeletion :=
  full_soundness lineageDeletion lineage_deletion_full_certificate

theorem actual_game_control_vectors :
    (¬ FullAutonomy packageDeletion ∧ OperationalAutonomy packageDeletion) ∧
    (FullAutonomy lineageDeletion ∧ OperationalAutonomy lineageDeletion) ∧
    (¬ FullAutonomy withdrawalDeletion ∧ ¬ OperationalAutonomy withdrawalDeletion) :=
  ⟨package_control_games,⟨lineage_deletion_full_game,lineage_deletion_operational_game⟩,
    withdrawal_deletion_rejects_both⟩

end CSTTT.TargetTheory.GenericHandoff.POS04ActualGame
