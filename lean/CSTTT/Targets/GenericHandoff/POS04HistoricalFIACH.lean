import CSTTT.Targets.GenericHandoff.POS04HistoricalAutonomy
import CSTTT.Targets.GenericHandoff.POS04CompleteFIACH

/-! POS-04-family soundness with the historical-support autonomy semantics.
This is NOT the final polymorphic RawHandoff result and does not promote TTH-06.
Package construction, complete funded-source lineage, and historical-support
target autonomy consume their separate raw checks. Acquisition shares one
assignment but has TWO justified readings: raw recorded-history admissibility
for F/O autonomy; complete actual funded-source execution for strict lineage.
Their agreement requires the checked source-execution conditions proved in
POS04HistoricalAutonomy. No weaker lineage gate supplies the L conclusion.

Ceiling: finite POS-04 interface, arbitrary partial assignments, nominal
disturbances with all-support branch robustness, C4–C7 surrogate content;
no resource-shock robustness, T17-I, physical or recognition claim. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH

abbrev Certificate := POS04CompleteFIACH.Certificate
def HandoffPassF (c : Certificate) :=
  POS04CompleteFIACH.Common c.model ∧ AF c.model
def HandoffPassO (c : Certificate) :=
  POS04CompleteFIACH.Common c.model ∧ AO c.model

theorem soundness_F (c : Certificate) (h : HandoffPassF c) :
    IntegratedTargetRealization c.model ∧ POS04CompleteLineage.StrictTemporalLineage c.model ∧
      POS04HistoricalAutonomy.FullAutonomy c.model :=
  ⟨derive_package_lane _ h.1.2.2.1,POS04CompleteLineage.soundness _ h.1.2.2.2,
    (POS04HistoricalAutonomy.full_game_iff_af _).mpr h.2⟩

theorem soundness_O (c : Certificate) (h : HandoffPassO c) :
    IntegratedTargetRealization c.model ∧ POS04CompleteLineage.StrictTemporalLineage c.model ∧
      POS04HistoricalAutonomy.OperationalAutonomy c.model :=
  ⟨derive_package_lane _ h.1.2.2.1,POS04CompleteLineage.soundness _ h.1.2.2.2,
    (POS04HistoricalAutonomy.operational_game_iff_ao _).mpr h.2⟩

/-- Replacing entry interpretation does not change the committed complete
family's acceptance, for ANY partial assignment, by the exact game adapters. -/
theorem family_pass_F_iff (c : Certificate) : HandoffPassF c ↔ POS04CompleteFIACH.HandoffPassF c := by
  unfold HandoffPassF POS04CompleteFIACH.HandoffPassF
  rw [POS04RegisterGames.full_iff_af]

theorem family_pass_O_iff (c : Certificate) : HandoffPassO c ↔ POS04CompleteFIACH.HandoffPassO c := by
  unfold HandoffPassO POS04CompleteFIACH.HandoffPassO
  rw [POS04RegisterGames.operational_iff_ao]

theorem positive_F : HandoffPassF ⟨baseline⟩ := (family_pass_F_iff _).mpr POS04CompleteFIACH.positive_F
theorem positive_O : HandoffPassO ⟨baseline⟩ := (family_pass_O_iff _).mpr POS04CompleteFIACH.positive_O

theorem full_dependence (m : RawLaneModel) (h : POS04HistoricalAutonomy.FullAutonomy m) :
    IntegratedTargetRealization m :=
  derive_package_lane _ (POS04HistoricalAutonomy.full_implies_package m h)

/-- Direct named-readout controls: none is concluded merely from a failed
sufficient gate. Package and lineage negatives reuse their semantic proofs;
autonomy negatives use exact strategy-game equivalence. -/
theorem F_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ POS04CompleteLineage.StrictTemporalLineage packageDeletion ∧
      ¬ POS04HistoricalAutonomy.FullAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ POS04CompleteLineage.StrictTemporalLineage lineageDeletion ∧
      POS04HistoricalAutonomy.FullAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ POS04CompleteLineage.StrictTemporalLineage withdrawalDeletion ∧
      ¬ POS04HistoricalAutonomy.FullAutonomy withdrawalDeletion) :=
  ⟨⟨POS04CompleteLineage.F_control_vectors.1.1,POS04CompleteLineage.F_control_vectors.1.2.1,
      POS04HistoricalAutonomy.registered_game_vectors.1.1⟩,
    ⟨POS04CompleteLineage.F_control_vectors.2.1.1,POS04CompleteLineage.F_control_vectors.2.1.2.1,
      POS04HistoricalAutonomy.registered_game_vectors.2.1.1⟩,
    ⟨POS04CompleteLineage.F_control_vectors.2.2.1,POS04CompleteLineage.F_control_vectors.2.2.2.1,
      POS04HistoricalAutonomy.registered_game_vectors.2.2.1⟩⟩

theorem O_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ POS04CompleteLineage.StrictTemporalLineage packageDeletion ∧
      POS04HistoricalAutonomy.OperationalAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ POS04CompleteLineage.StrictTemporalLineage lineageDeletion ∧
      POS04HistoricalAutonomy.OperationalAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ POS04CompleteLineage.StrictTemporalLineage withdrawalDeletion ∧
      ¬ POS04HistoricalAutonomy.OperationalAutonomy withdrawalDeletion) :=
  ⟨⟨POS04CompleteLineage.O_control_vectors.1.1,POS04CompleteLineage.O_control_vectors.1.2.1,
      POS04HistoricalAutonomy.registered_game_vectors.1.2⟩,
    ⟨POS04CompleteLineage.O_control_vectors.2.1.1,POS04CompleteLineage.O_control_vectors.2.1.2.1,
      POS04HistoricalAutonomy.registered_game_vectors.2.1.2⟩,
    ⟨POS04CompleteLineage.O_control_vectors.2.2.1,POS04CompleteLineage.O_control_vectors.2.2.2.1,
      POS04HistoricalAutonomy.registered_game_vectors.2.2.2⟩⟩

theorem operational_three_lane_separation :
    (∃ m, ¬ IntegratedTargetRealization m ∧ POS04CompleteLineage.StrictTemporalLineage m ∧
      POS04HistoricalAutonomy.OperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ ¬ POS04CompleteLineage.StrictTemporalLineage m ∧
      POS04HistoricalAutonomy.OperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ POS04CompleteLineage.StrictTemporalLineage m ∧
      ¬ POS04HistoricalAutonomy.OperationalAutonomy m) :=
  ⟨⟨packageDeletion,O_control_vectors.1⟩,⟨lineageDeletion,O_control_vectors.2.1⟩,
    ⟨withdrawalDeletion,O_control_vectors.2.2⟩⟩

theorem relabel_F_vector : IntegratedTargetRealization POS04LineageFutureBoundary.proposal ∧
    ¬ POS04CompleteLineage.StrictTemporalLineage POS04LineageFutureBoundary.proposal ∧
    POS04HistoricalAutonomy.FullAutonomy POS04LineageFutureBoundary.proposal := by
  have h := temporalFIACH_sound_F _ POS04CompleteLineage.relabel_legacy_F_accepts
  have haf := (Bool.and_eq_true_iff.mp POS04CompleteLineage.relabel_legacy_F_accepts).2
  exact ⟨h.1,POS04CompleteLineage.relabel_no_lineage,(POS04HistoricalAutonomy.full_game_iff_af _).mpr haf⟩

theorem relabel_O_vector : IntegratedTargetRealization POS04LineageFutureBoundary.proposal ∧
    ¬ POS04CompleteLineage.StrictTemporalLineage POS04LineageFutureBoundary.proposal ∧
    POS04HistoricalAutonomy.OperationalAutonomy POS04LineageFutureBoundary.proposal := by
  have h := temporalFIACH_sound_O _ POS04CompleteLineage.relabel_legacy_O_accepts
  have hao := (Bool.and_eq_true_iff.mp POS04CompleteLineage.relabel_legacy_O_accepts).2
  exact ⟨h.1,POS04CompleteLineage.relabel_no_lineage,(POS04HistoricalAutonomy.operational_game_iff_ao _).mpr hao⟩

/-- Both autonomy readings accept raw-supported recorded history even when
the stronger funded-source lineage has no acquisition branch. -/
theorem historical_support_diagnostic_vector :
    IntegratedTargetRealization POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    ¬ POS04CompleteLineage.StrictTemporalLineage POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    POS04HistoricalAutonomy.FullAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    POS04HistoricalAutonomy.OperationalAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable :=
  ⟨full_dependence _ POS04HistoricalAutonomy.source_recharge_unavailable_historical_full,
    POS04HistoricalAutonomy.source_recharge_unavailable_no_complete_lineage,
    POS04HistoricalAutonomy.source_recharge_unavailable_historical_full,
    POS04HistoricalAutonomy.source_recharge_unavailable_historical_operational⟩

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalFIACH
