import CSTTT.Targets.GenericHandoff.POS04MultiResourceGames

/-! G6d runtime-equivalence obstruction, TTH-06.
The diagnostic deletes precisely the pre-stage target tick cell. Staging sends
that absence to the source tick cell. Frozen operational autonomy does not read
that cell: source history admissibility uses action support, and reception resets
the probe-local ticks. The shared actual acquisition updater nevertheless reads
source ticks and its completeness gate rejects the proposal.

This is a raw cell deletion, not a new model declaration or a changed prediction.
It establishes that the CURRENT multi-resource O game is not equivalent to
frozen AO on arbitrary partial assignments. It does not change AO, relax missing
input rejection, or invalidate the positive runtime games. The O acquisition
interpreter must be repaired by a proved observational projection, not by filling
absent ticks with defaults or by adding source-tick completeness to frozen AO.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RuntimeEquivalenceBoundary
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Delete ONE primitive; no receiver, support row, resource or result changes. -/
def missingPastTicks : RawLaneModel :=
  {baseline with assignment := Assigned.put canonical (.ticks .target) none}

theorem staged_source_ticks_missing :
    image missingPastTicks.assignment (.ticks .source) = none :=
  image_delete_cell canonical (.ticks .source)

/-- The frozen computation is definitionally unchanged, not merely recomputed
as a successful boolean with an unexplained dependency omission. -/
theorem legacy_operational_check_unchanged :
    operationalAutonomyCheck missingPastTicks = operationalAutonomyCheck baseline := rfl

theorem legacy_operational_accepts : AO missingPastTicks := by
  change operationalAutonomyCheck missingPastTicks = true
  rw [legacy_operational_check_unchanged]
  exact baseline_AO

/-- The committed named semantic readout holds by its existing exact game/GFP
adapter. This avoids presenting only a passing sufficient check. -/
theorem legacy_operational_game_accepts : POS04OperationalGame.Autonomy missingPastTicks :=
  (POS04OperationalGame.game_iff_ao _).mpr legacy_operational_accepts

theorem legacy_named_operational_accepts :
    ComputedFIACH.PostWithdrawalOperationalAutonomy missingPastTicks :=
  derive_operational_autonomy_lane _ legacy_operational_accepts

/-- The field really occurs in the shared updater; it is not a declared scope
added merely to force the negative. -/
theorem source_tick_is_consumed :
    Cell.ticks Tag.source ∈
      ((POS04ResourceRuntime.model (POS04ResourceRuntime.protocol missingPastTicks)).runtime.execution.program ()).dependencies := by
  simp [POS04ResourceRuntime.model,POS04DispatchedStage.bind,POS04ResourceRuntime.runtime,
    POS04RouteExecution.acquisition,POS04RouteExecution.updateProgram,POS04RouteExecution.nextExpression,
    POS04RouteExecution.lift,RunFrame.dependencies,POS04RegisterDynamics.program,
    RegisterInterpreter.Expr.dependencies]

/-- Reject BOTH semantic games from actual missing input, not from a failed
sufficient check, and without assuming readiness beside incompatible absence. -/
theorem runtime_games_reject :
    ¬ PackageRuntime.PostWithdrawalFullAutonomy
      (POS04ResourceRuntime.model (POS04ResourceRuntime.protocol missingPastTicks)) missingPastTicks.assignment ∧
    ¬ PackageRuntime.PostWithdrawalOperationalAutonomy
      (POS04ResourceRuntime.model (POS04ResourceRuntime.protocol missingPastTicks)) missingPastTicks.assignment := by
  apply PackageRuntime.missing_update_no_games _ _ () (.ticks .source) source_tick_is_consumed
  rw [POS04ResourceRuntime.target_eq]
  exact staged_source_ticks_missing

/-- A direct existential counterexample to the requested arbitrary-partial O
adapter, with the SAME raw metadata on both sides. -/
theorem operational_equivalence_counterexample :
    ∃ m : RawLaneModel, AO m ∧
      ¬ PackageRuntime.PostWithdrawalOperationalAutonomy
        (POS04ResourceRuntime.model (POS04ResourceRuntime.protocol m)) m.assignment :=
  ⟨missingPastTicks,legacy_operational_accepts,runtime_games_reject.2⟩

theorem not_arbitrary_partial_operational_equivalence :
    ¬ (∀ m : RawLaneModel,
      PackageRuntime.PostWithdrawalOperationalAutonomy
        (POS04ResourceRuntime.model (POS04ResourceRuntime.protocol m)) m.assignment ↔ AO m) := by
  intro h
  exact runtime_games_reject.2 ((h missingPastTicks).mpr legacy_operational_accepts)

/-- F also rejects the diagnostic: its package requires every primitive.
Thus this witness disproves O equivalence only; it does not disprove F. -/
theorem legacy_full_rejects : ¬ AF missingPastTicks := by
  intro h
  have hp := fullAutonomy_implies_package missingPastTicks h
  exact package_lane_missing (.ticks .target) hp

end CSTTT.TargetTheory.GenericHandoff.POS04RuntimeEquivalenceBoundary
