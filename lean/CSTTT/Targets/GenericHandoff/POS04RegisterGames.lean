import CSTTT.Targets.GenericHandoff.POS04RegisterOperational
import CSTTT.Targets.GenericHandoff.GameReindex

/-! Exact family game binding through the polymorphic register component.
The acquisition protocol/entries and full graded package are still the
ComputedFIACH family interpreters. They are DEFINED from m, never arguments
or raw Prop fields. Their broader polymorphic extraction remains G6d-3/4.
No candidate dynamics or semantic predicate is supplied to either family gate.
The readiness evidence is derived from the raw protocol, not assumed beside it.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RegisterGames
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04RegisterDynamics
open POS04RegisterOperational

abbrev State := Registers Register RegisterValue

def reindex : StrategyGame.RunReindex Run6 State :=
  ⟨encode,decodeRun,decode_encode,encode_decode⟩

/-- Internal interpretation lemma; p is instantiated with a computed package
or operational-factor predicate at the public family boundary below. -/
theorem kernel_iff (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (p : Run6 → Prop) :
    StrategyGame.GameReadout
      (RegisterOperational.rows schema raw (withdrawnAssignment m))
      (RegisterOperational.update raw (withdrawnAssignment m)
        (ready_of_complete _ (complete_of_protocol m hp)))
      (fun y => POS04OperationalGame.Entries m (decodeRun y)) (POS04OperationalGame.Protocol m)
      (fun y => p (decodeRun y))
      (RegisterOperational.ResourceClosed schema raw (withdrawnAssignment m))
      (RegisterOperational.Legal schema raw (withdrawnAssignment m))
      (RegisterOperational.StepLaw schema raw (withdrawnAssignment m)
        (ready_of_complete _ (complete_of_protocol m hp))) ↔
    StrategyGame.GameReadout (POS04OperationalGame.rows m) (POS04OperationalGame.update m)
      (POS04OperationalGame.Entries m) (POS04OperationalGame.Protocol m) p
      (POS04OperationalGame.ResourceClosed m) (POS04OperationalGame.Legal m) (POS04OperationalGame.StepLaw m) := by
  have hr : RegisterOperational.rows schema raw (withdrawnAssignment m) =
      reindex.rows (POS04OperationalGame.rows m) := by
    funext y d act
    simpa only [encode_decode] using rows_eq m hp (decodeRun y) d act
  have hn : RegisterOperational.update raw (withdrawnAssignment m)
      (ready_of_complete _ (complete_of_protocol m hp)) = reindex.update (POS04OperationalGame.update m) := by
    funext y d act o
    simpa only [encode_decode] using update_eq m hp (decodeRun y) d act o
  have hres : RegisterOperational.ResourceClosed schema raw (withdrawnAssignment m) =
      (fun y => POS04OperationalGame.ResourceClosed m (decodeRun y)) := by
    funext y
    exact propext (by simpa only [encode_decode] using resource_iff m hp (decodeRun y))
  have hl : RegisterOperational.Legal schema raw (withdrawnAssignment m) =
      (fun y => POS04OperationalGame.Legal m (decodeRun y)) := by
    funext y d act
    exact propext (by simpa only [encode_decode] using legal_iff m hp (decodeRun y) d act)
  have hs : RegisterOperational.StepLaw schema raw (withdrawnAssignment m)
      (ready_of_complete _ (complete_of_protocol m hp)) =
      (fun y => POS04OperationalGame.StepLaw m (decodeRun y)) := by
    funext y d act o
    exact propext (by simpa only [encode_decode] using step_iff m hp (decodeRun y) d act o)
  rw [hr,hn,hres,hl,hs]
  exact reindex.game_iff

def Operational (m : RawLaneModel) : Prop :=
  ∃ hp : POS04OperationalGame.Protocol m,
    RegisterOperational.OperationalReadout schema raw (withdrawnAssignment m)
      (ready_of_complete _ (complete_of_protocol m hp))
      (fun y => POS04OperationalGame.Entries m (decodeRun y)) (POS04OperationalGame.Protocol m)

def Full (m : RawLaneModel) : Prop :=
  ∃ hp : POS04OperationalGame.Protocol m,
    StrategyGame.GameReadout
      (RegisterOperational.rows schema raw (withdrawnAssignment m))
      (RegisterOperational.update raw (withdrawnAssignment m)
        (ready_of_complete _ (complete_of_protocol m hp)))
      (fun y => POS04OperationalGame.Entries m (decodeRun y)) (POS04OperationalGame.Protocol m)
      (fun y => POS04FullGame.PackageAt m (decodeRun y))
      (RegisterOperational.ResourceClosed schema raw (withdrawnAssignment m))
      (RegisterOperational.Legal schema raw (withdrawnAssignment m))
      (RegisterOperational.StepLaw schema raw (withdrawnAssignment m)
        (ready_of_complete _ (complete_of_protocol m hp)))

theorem operational_iff_game (m : RawLaneModel) : Operational m ↔ POS04OperationalGame.Autonomy m := by
  have hi : RegisterOperational.Inside schema raw (withdrawnAssignment m) =
      (fun y => POS04OperationalGame.Inside m (decodeRun y)) := by
    funext y
    exact propext (by simpa only [encode_decode] using inside_iff m (decodeRun y))
  unfold Operational RegisterOperational.OperationalReadout
  rw [hi]
  constructor
  · rintro ⟨hp,_,h⟩
    exact (kernel_iff m hp (POS04OperationalGame.Inside m)).mp h
  · intro h
    exact ⟨h.1,by decide,(kernel_iff m h.1 (POS04OperationalGame.Inside m)).mpr h⟩

theorem full_iff_game (m : RawLaneModel) : Full m ↔ POS04FullGame.Autonomy m := by
  constructor
  · rintro ⟨hp,h⟩
    exact (kernel_iff m hp (POS04FullGame.PackageAt m)).mp h
  · intro h
    exact ⟨h.1,(kernel_iff m h.1 (POS04FullGame.PackageAt m)).mpr h⟩

/-- Exact arbitrary-partial equivalences; legacy gates remain unchanged. -/
theorem operational_iff_ao (m : RawLaneModel) : Operational m ↔ AO m :=
  (operational_iff_game m).trans (POS04OperationalGame.game_iff_ao m)
theorem full_iff_af (m : RawLaneModel) : Full m ↔ AF m :=
  (full_iff_game m).trans (POS04FullGame.game_iff_af m)

theorem full_implies_package (m : RawLaneModel) (h : Full m) : PackageLane m.assignment :=
  fullAutonomy_implies_package m ((full_iff_af m).mp h)

theorem positive : Full baseline ∧ Operational baseline :=
  ⟨(full_iff_game _).mpr POS04ExactGames.positive_games.1,
    (operational_iff_game _).mpr POS04ExactGames.positive_games.2⟩

theorem control_vectors :
    (¬ Full packageDeletion ∧ Operational packageDeletion) ∧
    (Full lineageDeletion ∧ Operational lineageDeletion) ∧
    (¬ Full withdrawalDeletion ∧ ¬ Operational withdrawalDeletion) := by
  simp only [full_iff_game,operational_iff_game]
  exact POS04ExactGames.registered_game_vectors

theorem missing_hazard_operational : Operational POS04ActualGame.missingHazard :=
  (operational_iff_game _).mpr POS04ExactGames.missing_hazard_game

theorem missing_hazard_full : ¬ Full POS04ActualGame.missingHazard :=
  fun h => POS04ExactGames.missing_hazard_full_rejected ((full_iff_game _).mp h)

/-- Direct negative readout: every consumed acquisition/operational primitive
rejects before any missing-value totalization can support a response. -/
theorem missing_dependency_rejected (m : RawLaneModel) (k : Cell)
    (hk : k ∈ POS04OperationalGame.dependencies) (hm : image m.assignment k = none) :
    ¬ Operational m :=
  fun h => POS04OperationalGame.missing_dependency_rejects m k hk hm ((operational_iff_game m).mp h)

theorem operational_iff_named (m : RawLaneModel) :
    Operational m ↔ PostWithdrawalOperationalAutonomy m :=
  (operational_iff_game m).trans (POS04OperationalGame.game_iff_named_readout m)

theorem full_iff_named (m : RawLaneModel) : Full m ↔ PostWithdrawalFullAutonomy m :=
  (full_iff_game m).trans (POS04FullGame.game_iff_named_readout m)

/-- Existing genuine TTH-05 transport remains accessible after register
reindexing. This is the FAMILY theorem, not the pending generic extraction. -/
theorem full_each_entry_exact_autonomy (m : RawLaneModel) (h : Full m) :
    ∀ e ∈ entries m, ∃ s, e.factor = .inK s ∧
      Nonempty (CSTTT.AutonomyTheory.ExactAutonomyCertificate (computedExactAutonomy m s)) :=
  POS04FullGame.game_each_entry_exact_autonomy m ((full_iff_game m).mp h)

end CSTTT.TargetTheory.GenericHandoff.POS04RegisterGames
