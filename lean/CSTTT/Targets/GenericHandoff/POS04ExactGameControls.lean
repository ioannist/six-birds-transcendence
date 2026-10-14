import CSTTT.Targets.GenericHandoff.POS04FullGameEquivalence
import CSTTT.Targets.ComputedFIACH.Guards

/-! Semantic controls after the O dependency correction. Both equivalences
quantify over every partial assignment; controls transfer through equivalence,
not through failure of a merely sufficient check. Old overstrict full-C6 O
schema results are retained with their original namespace and meaning. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ExactGames
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH

/-- F has the same raw acquisition/response interpreter, and strengthens only
package preservation. No unselected-action safety is added. -/
theorem full_implies_operational (m : RawLaneModel) (h : POS04FullGame.Autonomy m) : POS04OperationalGame.Autonomy m := by
  obtain ⟨cert⟩ := StrategyGame.game_invariant_completeness h
  apply POS04OperationalGame.soundness m
  exact {
    inside := cert.inside
    withdrawn := cert.withdrawn
    entriesNonempty := cert.entriesNonempty
    entriesInside := cert.entriesInside
    packageInside := fun r hr => by obtain ⟨_,s,hs,_⟩ := cert.packageInside r hr; exact ⟨s,hs⟩
    resourcesInside := cert.resourcesInside
    response := cert.response }

theorem af_implies_ao (m : RawLaneModel) (h : AF m) : AO m :=
  (POS04OperationalGame.game_iff_ao m).mp (full_implies_operational m ((POS04FullGame.game_iff_af m).mpr h))

theorem positive_games : POS04FullGame.Autonomy baseline ∧ POS04OperationalGame.Autonomy baseline :=
  ⟨(POS04FullGame.game_iff_af _).mpr baseline_AF,(POS04OperationalGame.game_iff_ao _).mpr baseline_AO⟩

theorem registered_game_vectors :
    (¬ POS04FullGame.Autonomy packageDeletion ∧ POS04OperationalGame.Autonomy packageDeletion) ∧
    (POS04FullGame.Autonomy lineageDeletion ∧ POS04OperationalGame.Autonomy lineageDeletion) ∧
    (¬ POS04FullGame.Autonomy withdrawalDeletion ∧ ¬ POS04OperationalGame.Autonomy withdrawalDeletion) := by
  constructor
  · exact ⟨fun h => package_deletion_not_AF ((POS04FullGame.game_iff_af _).mp h),
      (POS04OperationalGame.game_iff_ao _).mpr package_deletion_AO⟩
  constructor
  · exact ⟨(POS04FullGame.game_iff_af _).mpr lineage_deletion_AF,(POS04OperationalGame.game_iff_ao _).mpr lineage_deletion_AO⟩
  · exact ⟨fun h => withdrawal_deletion_not_AF ((POS04FullGame.game_iff_af _).mp h),
      fun h => withdrawal_deletion_not_AO ((POS04OperationalGame.game_iff_ao _).mp h)⟩

/-- The review counterexample now has a genuine O strategy. -/
theorem missing_hazard_game : POS04OperationalGame.Autonomy POS04ActualGame.missingHazard :=
  (POS04OperationalGame.game_iff_ao _).mpr POS04ActualGame.missing_hazard_legacy_AO

/-- The same deletion still rejects F because F preserves the package.
O's smaller scope does not silently weaken package completeness. -/
theorem missing_hazard_full_rejected : ¬ POS04FullGame.Autonomy POS04ActualGame.missingHazard :=
  fun h => package_lane_missing .hazards (POS04FullGame.full_implies_arrival _ h)

theorem missing_input_rejects_both (m : RawLaneModel) (k : Cell) (hk : k ∈ POS04OperationalGame.dependencies)
    (hm : image m.assignment k = none) : ¬ POS04FullGame.Autonomy m ∧ ¬ POS04OperationalGame.Autonomy m :=
  ⟨fun h => POS04OperationalGame.missing_dependency_rejects m k hk hm (full_implies_operational m h),
    POS04OperationalGame.missing_dependency_rejects m k hk hm⟩

theorem source_absent_rejects_both (m : RawLaneModel)
    (h : (arrivalInputs m).base.receiver.sourcePresent = false) :
    ¬ POS04FullGame.Autonomy m ∧ ¬ POS04OperationalGame.Autonomy m := by
  have he : entries m = [] := phase2_unavailable_no_entries m (fun r _ => no_source_rejects_phase2 m h r)
  have empty : ∀ r, ¬ POS04OperationalGame.Entries m r := by simp [POS04OperationalGame.Entries,he]
  exact ⟨StrategyGame.no_entries_no_game empty,StrategyGame.no_entries_no_game empty⟩

/-- Each operational evolving field is defined by the updater. These laws
apply to every run, hence every generated play; strict advancement follows
from the separately checked assigned ledger/tick/writer conditions. -/
theorem run_readout_laws (m : RawLaneModel) (r : POS04OperationalGame.Run) (d : POS04OperationalGame.Disturbance)
    (a : Action) (o : Ambient) :
    (POS04OperationalGame.update m r d a o).factor = o ∧
    (POS04OperationalGame.update m r d a o).counter = r.counter+1 ∧
    (POS04OperationalGame.update m r d a o).ticks = r.ticks+POS04OperationalGame.tick (POS04OperationalGame.inputs m) r.factor a ∧
    (POS04OperationalGame.update m r d a o).residue = r.residue ∧
    (POS04OperationalGame.update m r d a o).funded = (r.funded && decide (
      (POS04OperationalGame.inputs m).viability.budget.initialBudget - (POS04OperationalGame.inputs m).viability.budget.actionCost +
        (POS04OperationalGame.inputs m).viability.budget.rechargePerAction > 0)) := ⟨rfl,rfl,rfl,rfl,rfl⟩

end CSTTT.TargetTheory.GenericHandoff.POS04ExactGames
