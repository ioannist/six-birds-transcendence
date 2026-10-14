import CSTTT.Targets.GenericHandoff.POS04CompleteLineage
import CSTTT.Targets.GenericHandoff.POS04GameAutonomyTransport

/-! Strengthened POS-04-family assembly. The lineage conclusion now includes
complete actual execution transport. The unchanged legacy soundness theorems
are not used to derive this lineage. Every lane consumes its own interpreted
subcheck. This is NOT the final polymorphic RawHandoff theorem; TTH-06 stays
conditional. C4–C7 are surrogates; nominal disturbances and all-support branch
robustness do not imply resource-shock robustness, recognition or full P05. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04CompleteFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH

/-- Only raw data, not a stored verdict or a supplied semantic conclusion. -/
structure Certificate where
  model : RawLaneModel

def Common (m : RawLaneModel) : Prop :=
  sourcePackageCheck m = true ∧ stagedPreservationCheck m = true ∧
    PackageLane m.assignment ∧ POS04CompleteLineage.Valid m

def HandoffPassF (c : Certificate) : Prop := Common c.model ∧ POS04RegisterGames.Full c.model
def HandoffPassO (c : Certificate) : Prop := Common c.model ∧ POS04RegisterGames.Operational c.model

theorem soundness_F (c : Certificate) (h : HandoffPassF c) :
    IntegratedTargetRealization c.model ∧ POS04CompleteLineage.StrictTemporalLineage c.model ∧
      PostWithdrawalFullAutonomy c.model :=
  ⟨derive_package_lane _ h.1.2.2.1,POS04CompleteLineage.soundness _ h.1.2.2.2,
    derive_full_autonomy_lane _ ((POS04RegisterGames.full_iff_af _).mp h.2)⟩

theorem soundness_O (c : Certificate) (h : HandoffPassO c) :
    IntegratedTargetRealization c.model ∧ POS04CompleteLineage.StrictTemporalLineage c.model ∧
      PostWithdrawalOperationalAutonomy c.model :=
  ⟨derive_package_lane _ h.1.2.2.1,POS04CompleteLineage.soundness _ h.1.2.2.2,
    derive_operational_autonomy_lane _ ((POS04RegisterGames.operational_iff_ao _).mp h.2)⟩

/-- The disclosed dependence is derived from a nonempty genuine entry and
package-preserving strategy, not used as the package soundness derivation. -/
theorem full_autonomy_implies_realization (m : RawLaneModel) (h : POS04RegisterGames.Full m) :
    IntegratedTargetRealization m :=
  derive_package_lane _ (fullAutonomy_implies_package m ((POS04RegisterGames.full_iff_af m).mp h))

theorem baseline_common : Common baseline :=
  ⟨baseline_source_package,baseline_staged_preservation,package_lane_positive,POS04CompleteLineage.positive_valid⟩

theorem positive_F : HandoffPassF ⟨baseline⟩ :=
  ⟨baseline_common,(POS04RegisterGames.full_iff_af baseline).mpr baseline_AF⟩

theorem positive_O : HandoffPassO ⟨baseline⟩ :=
  ⟨baseline_common,(POS04RegisterGames.operational_iff_ao baseline).mpr baseline_AO⟩

theorem positive_F_satisfiable : ∃ c, HandoffPassF c := ⟨⟨baseline⟩,positive_F⟩
theorem positive_O_satisfiable : ∃ c, HandoffPassO c := ⟨⟨baseline⟩,positive_O⟩

/-- TTH-05 transport consumes ONLY the full game component, for every actual
entry, and includes every positive-support response successor. -/
theorem full_each_entry_exact (c : Certificate) (h : HandoffPassF c) :
    ∃ cert : POS04FullGame.Certificate c.model,
      ∀ entry, POS04OperationalGame.Entries c.model entry →
        Nonempty (CSTTT.AutonomyTheory.ExactAutonomyCertificate
          (GameAutonomyTransport.projectedData (POS04GameAutonomyTransport.factor c.model) cert
            POS04GameAutonomyTransport.project entry)) :=
  POS04GameAutonomyTransport.register_game_each_entry_exact c.model h.2

theorem relabel_no_F : ¬ HandoffPassF ⟨POS04LineageFutureBoundary.proposal⟩ :=
  fun h => POS04CompleteLineage.relabel_no_lineage (soundness_F _ h).2.1

theorem relabel_no_O : ¬ HandoffPassO ⟨POS04LineageFutureBoundary.proposal⟩ :=
  fun h => POS04CompleteLineage.relabel_no_lineage (soundness_O _ h).2.1

/-- Named semantic readouts, with direct negative conclusions. -/
theorem operational_three_lane_separation :
    (∃ m, ¬ IntegratedTargetRealization m ∧ POS04CompleteLineage.StrictTemporalLineage m ∧ PostWithdrawalOperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ ¬ POS04CompleteLineage.StrictTemporalLineage m ∧ PostWithdrawalOperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ POS04CompleteLineage.StrictTemporalLineage m ∧ ¬ PostWithdrawalOperationalAutonomy m) := POS04CompleteLineage.operational_named_separation

theorem full_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ POS04CompleteLineage.StrictTemporalLineage packageDeletion ∧
      ¬ PostWithdrawalFullAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ POS04CompleteLineage.StrictTemporalLineage lineageDeletion ∧
      PostWithdrawalFullAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ POS04CompleteLineage.StrictTemporalLineage withdrawalDeletion ∧
      ¬ PostWithdrawalFullAutonomy withdrawalDeletion) := POS04CompleteLineage.F_control_vectors
theorem operational_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ POS04CompleteLineage.StrictTemporalLineage packageDeletion ∧
      PostWithdrawalOperationalAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ POS04CompleteLineage.StrictTemporalLineage lineageDeletion ∧
      PostWithdrawalOperationalAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ POS04CompleteLineage.StrictTemporalLineage withdrawalDeletion ∧
      ¬ PostWithdrawalOperationalAutonomy withdrawalDeletion) := POS04CompleteLineage.O_control_vectors

end CSTTT.TargetTheory.GenericHandoff.POS04CompleteFIACH
