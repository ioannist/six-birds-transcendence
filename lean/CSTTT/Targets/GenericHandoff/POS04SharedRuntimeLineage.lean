import CSTTT.Targets.GenericHandoff.POS04RuntimeExecutionLink
import CSTTT.Targets.GenericHandoff.POS04HistoricalSparseFIACH

/-! Shared-runtime specialization of the complete semantic lineage, TTH-06.
The route component now derives acquisition, register and owner from the same
runtime as the resource interpreter. Five-register G1c execution is linked to
that runtime on ALL runs and actual branches by ExecutionLink, not merely by
equal endpoint classes. The independent semantic bridge remains mandatory.

This is exact for every partial POS-04 assignment; it does NOT identify the
weaker legacy lineage predicate with complete lineage. It is a family instance
and representation boundary for the remaining polymorphic RawHandoff assembly,
not that final assembly or a promotion theorem. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04SharedRuntimeLineage
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH
open RegisterInterpreter POS04ResourceRuntime

abbrev staged (m : RawLaneModel) := image m.assignment

/-- Defined independently of the legacy gate. Full actual execution transport
and full Indexed/Retained comparison are separate semantic obligations. -/
def StrictTemporalLineage (m : RawLaneModel) : Prop :=
  POS04CompleteLineage.CorridorReadout (staged m) ∧
  POS04CompleteLineage.SeedReadout (staged m) ∧
  POS04CompleteLineage.FactorReadout m ∧
  POS04CompleteLineage.RecordReadout (staged m) ∧
  TypedAcquisitionEndpointPass m ∧
  RuntimeComponents.RetainedRouteReadout cfg (runtime (protocol m))
    POS04RuntimeRoute.instructions (staged m) ∧
  ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw (staged m)

/-- Both directions, for arbitrary partial assignments, not canonical truth
alone and never an implication from the weaker legacy acceptance gate. -/
theorem whole_iff (m : RawLaneModel) : StrictTemporalLineage m ↔
    POS04CompleteLineage.StrictTemporalLineage m := by
  unfold StrictTemporalLineage POS04CompleteLineage.StrictTemporalLineage
  rw [POS04RuntimeRoute.semantic_iff]

theorem soundness (m : RawLaneModel) (h : POS04CompleteLineage.Valid m) :
    StrictTemporalLineage m :=
  (whole_iff m).mpr (POS04CompleteLineage.soundness m h)

/-- Source/receiver execution links are DERIVED representation facts. They
are not additional bookkeeping inserted into the semantic lineage readout. -/
theorem actual_runtime_links (m : RawLaneModel) (h : StrictTemporalLineage m) :
    ExecutionLink.Pass (POS04RuntimeExecutionLink.raw .source) (staged m) ∧
      ExecutionLink.Pass (POS04RuntimeExecutionLink.raw .target) (staged m) := by
  have hc := (POS04RuntimeRoute.semantic_iff _ _).mp h.2.2.2.2.2.1 |>.1
  exact ⟨POS04RuntimeExecutionLink.checked _ hc .source,
    POS04RuntimeExecutionLink.checked _ hc .target⟩

/-- The autonomy target program shares the actual target updates without
funding source history. This target link consumes no source dependencies. -/
theorem historical_runtime_link (m : RawLaneModel) (h : StrictTemporalLineage m) :
    ExecutionLink.Pass POS04RuntimeExecutionLink.historicalRaw (staged m) := by
  have hc := (POS04RuntimeRoute.semantic_iff _ _).mp h.2.2.2.2.2.1 |>.1
  apply POS04RuntimeExecutionLink.historical_checked
  intro k hk
  apply hc k
  simp [POS04RuntimeExecutionLink.targetDependencies] at hk
  rcases hk with hk | hk | hk | hk
  all_goals subst k; simp [POS04RouteExecution.dependencies]

theorem retained_status (m : RawLaneModel) (h : StrictTemporalLineage m) :
    RuntimeComponents.retainedRouteStatus cfg (runtime (protocol m))
      POS04RuntimeRoute.instructions (staged m) = .routeIndexed :=
  (RuntimeComponents.retained_route_status_iff _ _ _ _).mpr h.2.2.2.2.2.1

theorem positive : StrictTemporalLineage baseline :=
  (whole_iff baseline).mpr POS04CompleteLineage.positive

theorem relabel_no_lineage : ¬ StrictTemporalLineage POS04LineageFutureBoundary.proposal :=
  fun h => POS04CompleteLineage.relabel_no_lineage ((whole_iff _).mp h)

theorem missing_atomic_no_lineage (m : RawLaneModel) :
    ¬ StrictTemporalLineage {m with assignment := Assigned.put m.assignment .eventTable none} :=
  fun h => POS04CompleteLineage.missing_atomic_no_lineage m ((whole_iff _).mp h)

/-- Regression against accidentally returning to the old named readout. -/
theorem legacy_not_sufficient :
    ¬ (∀ m, ComputedFIACH.StrictTemporalLineage m → StrictTemporalLineage m) := by
  intro h
  exact relabel_no_lineage (h _ POS04LineageFutureBoundary.legacy_named_readout_accepts)

/-- Direct named semantic outcomes; negative clauses are transported by
biconditional, not inferred from failure of a sufficient certification check. -/
theorem O_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ StrictTemporalLineage packageDeletion ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ StrictTemporalLineage lineageDeletion ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ StrictTemporalLineage withdrawalDeletion ∧
      ¬ POS04HistoricalSparseEquivalence.OperationalAutonomy withdrawalDeletion) := by
  have h := POS04HistoricalSparseFIACH.O_control_vectors
  exact ⟨⟨h.1.1,(whole_iff _).mpr h.1.2.1,h.1.2.2⟩,
    ⟨h.2.1.1,fun hl => h.2.1.2.1 ((whole_iff _).mp hl),h.2.1.2.2⟩,
    ⟨h.2.2.1,(whole_iff _).mpr h.2.2.2.1,h.2.2.2.2⟩⟩

theorem F_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ StrictTemporalLineage packageDeletion ∧
      ¬ POS04HistoricalSparseEquivalence.FullAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ StrictTemporalLineage lineageDeletion ∧
      POS04HistoricalSparseEquivalence.FullAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ StrictTemporalLineage withdrawalDeletion ∧
      ¬ POS04HistoricalSparseEquivalence.FullAutonomy withdrawalDeletion) := by
  have h := POS04HistoricalSparseFIACH.F_control_vectors
  exact ⟨⟨h.1.1,(whole_iff _).mpr h.1.2.1,h.1.2.2⟩,
    ⟨h.2.1.1,fun hl => h.2.1.2.1 ((whole_iff _).mp hl),h.2.1.2.2⟩,
    ⟨h.2.2.1,(whole_iff _).mpr h.2.2.2.1,h.2.2.2.2⟩⟩

theorem operational_named_separation :
    (∃ m, ¬ IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ ¬ StrictTemporalLineage m ∧
      POS04HistoricalSparseEquivalence.OperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
      ¬ POS04HistoricalSparseEquivalence.OperationalAutonomy m) :=
  ⟨⟨packageDeletion,O_control_vectors.1⟩,⟨lineageDeletion,O_control_vectors.2.1⟩,
    ⟨withdrawalDeletion,O_control_vectors.2.2⟩⟩

theorem relabel_vector : IntegratedTargetRealization POS04LineageFutureBoundary.proposal ∧
    ¬ StrictTemporalLineage POS04LineageFutureBoundary.proposal ∧
    POS04HistoricalSparseEquivalence.FullAutonomy POS04LineageFutureBoundary.proposal ∧
    POS04HistoricalSparseEquivalence.OperationalAutonomy POS04LineageFutureBoundary.proposal := by
  have h := POS04HistoricalSparseFIACH.relabel_vectors
  exact ⟨h.1,relabel_no_lineage,h.2.2⟩

theorem source_recharge_diagnostic :
    IntegratedTargetRealization POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    ¬ StrictTemporalLineage POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    POS04HistoricalSparseEquivalence.FullAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable ∧
    POS04HistoricalSparseEquivalence.OperationalAutonomy POS04ReceiverResetProjection.sourceRechargeUnavailable := by
  have h := POS04HistoricalSparseFIACH.source_recharge_diagnostic
  exact ⟨h.1,fun hl => h.2.1 ((whole_iff _).mp hl),h.2.2⟩

/-- The actual source execution consumes its tick table. The historical
target reset does not; absence is not silently supplied by a decoder default. -/
theorem missing_source_ticks_no_lineage :
    ¬ StrictTemporalLineage POS04RuntimeEquivalenceBoundary.missingPastTicks := by
  intro h
  have hc := (POS04RuntimeRoute.semantic_iff _ _).mp h.2.2.2.2.2.1 |>.1
  have ht := hc (.ticks .source) (by simp [POS04RouteExecution.dependencies])
  dsimp only [staged] at ht
  rw [POS04RuntimeEquivalenceBoundary.staged_source_ticks_missing] at ht
  contradiction

theorem missing_source_ticks_historical_link :
    ExecutionLink.Pass POS04RuntimeExecutionLink.historicalRaw
      (staged POS04RuntimeEquivalenceBoundary.missingPastTicks) :=
  (POS04RuntimeExecutionLink.historical_pass_iff _).mpr (by
    intro k hk
    simp only [POS04RuntimeExecutionLink.targetDependencies,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with hk | hk | hk | hk
    all_goals subst k; decide +kernel)

theorem missing_source_ticks_operational :
    ¬ StrictTemporalLineage POS04RuntimeEquivalenceBoundary.missingPastTicks ∧
    POS04HistoricalSparseEquivalence.OperationalAutonomy POS04RuntimeEquivalenceBoundary.missingPastTicks :=
  ⟨missing_source_ticks_no_lineage,POS04HistoricalSparseFIACH.missing_past_ticks_diagnostic.2⟩

end CSTTT.TargetTheory.GenericHandoff.POS04SharedRuntimeLineage
