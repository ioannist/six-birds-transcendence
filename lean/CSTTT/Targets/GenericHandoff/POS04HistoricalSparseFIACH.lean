import CSTTT.Targets.GenericHandoff.POS04HistoricalSparseEquivalence
import CSTTT.Targets.GenericHandoff.POS04HistoricalFIACH

/-! Format-qualified POS-04-family assembly, TTH-06 (b).
All partial assignments are included. The new autonomy interpreters require
strictly positive LISTED weights only on selected responses; the committed
support-only interpreters and frozen AF/AO are unchanged. No ordering or
unique-outcome condition is imposed.

Lineage remains the independently proved COMPLETE actual-execution readout:
funded source execution, G4 corridor, G1c bridge, typed endpoint, and the full
Indexed/Retained route comparison. Historical raw-support acquisition belongs
only to autonomy. This family adapter does not complete the polymorphic
RawHandoff binding and does not promote TTH-06. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH
open POS04HistoricalSparseEquivalence

abbrev Certificate := POS04CompleteFIACH.Certificate

def HandoffPassF (c : Certificate) : Prop :=
  POS04CompleteFIACH.Common c.model ∧ FullAutonomy c.model

def HandoffPassO (c : Certificate) : Prop :=
  POS04CompleteFIACH.Common c.model ∧ OperationalAutonomy c.model

/-- Exact family gate adapters, including protocol-failure cases. -/
theorem family_F_iff (c : Certificate) : HandoffPassF c ↔ POS04HistoricalFIACH.HandoffPassF c := by
  unfold HandoffPassF POS04HistoricalFIACH.HandoffPassF
  rw [full_iff_af]

theorem family_O_iff (c : Certificate) : HandoffPassO c ↔ POS04HistoricalFIACH.HandoffPassO c := by
  unfold HandoffPassO POS04HistoricalFIACH.HandoffPassO
  rw [operational_iff_ao]

/-- P consumes its package check, L its complete lineage check, A its own
computed protocol and actual strategy game. AF⇒P is not used to derive P. -/
theorem soundness_F (c : Certificate) (h : HandoffPassF c) :
    IntegratedTargetRealization c.model ∧ POS04CompleteLineage.StrictTemporalLineage c.model ∧
      FullAutonomy c.model :=
  ⟨derive_package_lane _ h.1.2.2.1,POS04CompleteLineage.soundness _ h.1.2.2.2,h.2⟩

theorem soundness_O (c : Certificate) (h : HandoffPassO c) :
    IntegratedTargetRealization c.model ∧ POS04CompleteLineage.StrictTemporalLineage c.model ∧
      OperationalAutonomy c.model :=
  ⟨derive_package_lane _ h.1.2.2.1,POS04CompleteLineage.soundness _ h.1.2.2.2,h.2⟩

theorem full_dependence (m : RawLaneModel) (h : FullAutonomy m) : IntegratedTargetRealization m :=
  derive_package_lane _ (fullAutonomy_implies_package m ((full_iff_af _).mp h))

theorem positive_F : HandoffPassF ⟨baseline⟩ :=
  (family_F_iff _).mpr POS04HistoricalFIACH.positive_F

theorem positive_O : HandoffPassO ⟨baseline⟩ :=
  (family_O_iff _).mpr POS04HistoricalFIACH.positive_O

/-- Direct named-readout outcomes. Negatives are semantic negations obtained
through the proved biconditionals, never inferred from gate failure. -/
theorem F_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ POS04CompleteLineage.StrictTemporalLineage packageDeletion ∧
      ¬ FullAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ POS04CompleteLineage.StrictTemporalLineage lineageDeletion ∧
      FullAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ POS04CompleteLineage.StrictTemporalLineage withdrawalDeletion ∧
      ¬ FullAutonomy withdrawalDeletion) := by
  have h := POS04CompleteLineage.F_control_vectors
  exact ⟨⟨h.1.1,h.1.2.1,fun ha => h.1.2.2 (derive_full_autonomy_lane _ ((full_iff_af _).mp ha))⟩,
    ⟨h.2.1.1,h.2.1.2.1,(full_iff_af _).mpr h.2.1.2.2.1⟩,
    ⟨h.2.2.1,h.2.2.2.1,fun ha => h.2.2.2.2 (derive_full_autonomy_lane _ ((full_iff_af _).mp ha))⟩⟩

theorem O_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ POS04CompleteLineage.StrictTemporalLineage packageDeletion ∧
      OperationalAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ POS04CompleteLineage.StrictTemporalLineage lineageDeletion ∧
      OperationalAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ POS04CompleteLineage.StrictTemporalLineage withdrawalDeletion ∧
      ¬ OperationalAutonomy withdrawalDeletion) := by
  have h := POS04CompleteLineage.O_control_vectors
  exact ⟨⟨h.1.1,h.1.2.1,(operational_iff_ao _).mpr h.1.2.2.1⟩,
    ⟨h.2.1.1,h.2.1.2.1,(operational_iff_ao _).mpr h.2.1.2.2.1⟩,
    ⟨h.2.2.1,h.2.2.2.1,fun ha => h.2.2.2.2 (derive_operational_autonomy_lane _ ((operational_iff_ao _).mp ha))⟩⟩

theorem operational_named_separation :
    (∃ m, ¬ IntegratedTargetRealization m ∧ POS04CompleteLineage.StrictTemporalLineage m ∧ OperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ ¬ POS04CompleteLineage.StrictTemporalLineage m ∧ OperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ POS04CompleteLineage.StrictTemporalLineage m ∧ ¬ OperationalAutonomy m) :=
  ⟨⟨packageDeletion,O_control_vectors.1⟩,⟨lineageDeletion,O_control_vectors.2.1⟩,
    ⟨withdrawalDeletion,O_control_vectors.2.2⟩⟩

theorem relabel_vectors :
    IntegratedTargetRealization POS04LineageFutureBoundary.proposal ∧
    ¬ POS04CompleteLineage.StrictTemporalLineage POS04LineageFutureBoundary.proposal ∧
    FullAutonomy POS04LineageFutureBoundary.proposal ∧ OperationalAutonomy POS04LineageFutureBoundary.proposal := by
  have hf := POS04HistoricalFIACH.relabel_F_vector
  have ho := POS04HistoricalFIACH.relabel_O_vector
  exact ⟨hf.1,hf.2.1,(full_iff_af _).mpr ((POS04HistoricalAutonomy.full_game_iff_af _).mp hf.2.2),
    (operational_iff_ao _).mpr ((POS04HistoricalAutonomy.operational_game_iff_ao _).mp ho.2.2)⟩

theorem relabel_no_F : ¬ HandoffPassF ⟨POS04LineageFutureBoundary.proposal⟩ :=
  fun h => relabel_vectors.2.1 (soundness_F _ h).2.1

theorem relabel_no_O : ¬ HandoffPassO ⟨POS04LineageFutureBoundary.proposal⟩ :=
  fun h => relabel_vectors.2.1 (soundness_O _ h).2.1

/-- Historical support is intentionally distinct from funded actual source
execution, even though both use the same raw assignment. -/
theorem source_recharge_diagnostic :
    IntegratedTargetRealization POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    ¬ POS04CompleteLineage.StrictTemporalLineage POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    FullAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    OperationalAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable := by
  have h := POS04HistoricalFIACH.historical_support_diagnostic_vector
  exact ⟨h.1,h.2.1,(full_iff_af _).mpr ((POS04HistoricalAutonomy.full_game_iff_af _).mp h.2.2.1),
    (operational_iff_ao _).mpr ((POS04HistoricalAutonomy.operational_game_iff_ao _).mp h.2.2.2)⟩

theorem missing_past_ticks_diagnostic :
    ¬ FullAutonomy POS04RuntimeEquivalenceBoundary.missingPastTicks ∧
    OperationalAutonomy POS04RuntimeEquivalenceBoundary.missingPastTicks :=
  ⟨fun h => POS04HistoricalAutonomy.missing_past_ticks_historical_full_rejects
    ((POS04HistoricalAutonomy.full_game_iff_af _).mpr ((full_iff_af _).mp h)),
    (operational_iff_ao _).mpr ((POS04HistoricalAutonomy.operational_game_iff_ao _).mp
      POS04HistoricalAutonomy.missing_past_ticks_historical_operational)⟩

theorem duplicate_event_operational : OperationalAutonomy POS04HistoricalDuplicateEvents.diagnostic :=
  (operational_iff_ao _).mpr POS04HistoricalDuplicateEvents.legacy_ao_accepts

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseFIACH
