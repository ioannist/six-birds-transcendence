import CSTTT.Targets.GenericHandoff.POS04GameProjection

/-! Per-field operational guards and named autonomy readout transport.
Negative readouts follow necessary raw conditions or exact equivalence, not
failure of a sufficient constructor. Quantifiers include partial assignments. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH

theorem invalid_withdrawal_rejected (m : RawLaneModel) (h : withdrawalCheck m = false) : ¬ Autonomy m := by
  intro ha
  have hw := ha.1.2.1
  rw [h] at hw
  contradiction

theorem invalid_ledger_rejected (m : RawLaneModel) (h : ¬ Ledger8 (withdrawnInputs m)) : ¬ Autonomy m :=
  fun ha => h (by rw [← viability_eq]; exact (protocol_resources m ha.1).2.1)

theorem wrong_owner_rejected (m : RawLaneModel)
    (h : (withdrawnInputs m).resource.owner ≠ .target) : ¬ Autonomy m := by
  intro ha
  have hr := (protocol_resources m ha.1).1
  rw [viability_eq] at hr
  exact h (of_decide_eq_true (Bool.and_eq_true_iff.mp hr).2)

theorem wrong_tick_rejected (m : RawLaneModel) (s : KState) (a : Action)
    (hn : ((withdrawnInputs m).rows s a).isEmpty = false)
    (h : (inputs m).ticks s a ≠ 1) : ¬ Autonomy m := by
  intro ha
  exact h (protocol_tick m ha.1 s a (by rw [viability_eq]; exact hn))

theorem missing_writer_rejected (m : RawLaneModel)
    (h : ∀ residue, writer (inputs m) residue = false) : ¬ Autonomy m := by
  rintro ⟨_,⟨entry,he⟩,strategy,hs⟩
  have hw := (hs entry he entry [] StrategyGame.Play.initial).2.1.2.2.2
  rw [h] at hw
  contradiction

theorem unfunded_entry_rejected (m : RawLaneModel) (e : WithdrawalEntry) (he : e ∈ entries m)
    (h : (entryRun m e).funded = false) : ¬ Autonomy m := by
  apply StrategyGame.entry_resource_failure_no_game (entryRun m e) ⟨e,he,rfl⟩
  intro hr
  have hf := hr.2.2.1
  rw [h] at hf
  contradiction

theorem no_safe_row_rejected (m : RawLaneModel) (e : WithdrawalEntry) (he : e ∈ entries m)
    (s : KState) (hf : e.factor = .inK s)
    (h : ∀ a, rowClosed8 (inputs m).viability s a kernel = false) : ¬ Autonomy m := by
  apply StrategyGame.missing_response_no_game (entryRun m e) ⟨e,he,rfl⟩ .nominal
  rintro a ⟨_,t,ht,hr⟩
  have heq : t = s := by injection (ht.symm.trans hf)
  subst t
  rw [h] at hr
  contradiction

theorem capped_record_differs (m : RawLaneModel) (hp : Protocol m) (r : Run)
    (hr : ResourceClosed m r) (s : KState) (hs : r.factor = .inK s) (a : Action)
    (hn : ((inputs m).viability.rows s a).isEmpty = false) (o : Ambient) (cap : Nat)
    (hc : r.counter ≥ cap) :
    min (record m (update m r .nominal a o)) cap ≠ record m (update m r .nominal a o) := by
  have hnxt := (step_preserves m hp r hr s hs .nominal a hn o).2.2.2.2.1
  have hrec : record m r = r.counter := by simp [record,hr.2.2.1,hr.2.2.2]
  rw [hnxt,hrec]
  omega

/-- Exact named O readout, including greatest-set viability. -/
theorem game_iff_named_readout (m : RawLaneModel) : Autonomy m ↔ PostWithdrawalOperationalAutonomy m :=
  ⟨fun h => derive_operational_autonomy_lane m ((game_iff_ao m).mp h),
    fun h => (game_iff_ao m).mpr h.1⟩
end CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame

namespace CSTTT.TargetTheory.GenericHandoff.POS04FullGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.AutonomyTheory

/-- Every derived entry obtains TTH-05; no reset and no lucky support branch. -/
theorem game_each_entry_exact_autonomy (m : RawLaneModel) (h : Autonomy m) :
    ∀ e ∈ entries m, ∃ s, e.factor = .inK s ∧
      Nonempty (ExactAutonomyCertificate (computedExactAutonomy m s)) :=
  AF_each_entry_exact_autonomy m ((game_iff_af m).mp h)

theorem game_iff_named_readout (m : RawLaneModel) : Autonomy m ↔ PostWithdrawalFullAutonomy m :=
  ⟨fun h => derive_full_autonomy_lane m ((game_iff_af m).mp h),
    fun h => (game_iff_af m).mpr h.1⟩

end CSTTT.TargetTheory.GenericHandoff.POS04FullGame
