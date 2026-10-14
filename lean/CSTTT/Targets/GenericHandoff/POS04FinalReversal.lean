import CSTTT.Targets.GenericHandoff.POS04FinalCorrespondence
/-! Reversed raw-history regression through complete actual lineage and
both final handoff gates. Source and target execute their own interpreted
programs; the unbounded readout laws use the accepted C6 invariant. The
route outputs are recomputed as 1/0, never relabeled to canonical 0/1. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04FinalReversal
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open RegisterInterpreter POS04RegisterDynamics CSTTT.TargetTheory.ComputedFIACH
open CSTTT.TransportTheory CSTTT.RecordTheory
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
abbrev a := image reversedHistories.assignment
theorem complete (xs : List Cell) : Complete xs a := by
  intro k _
  cases k
  all_goals try (rename_i t; cases t)
  all_goals rfl
theorem accept (t : Tag) : C6Accept a t := by cases t <;> decide +kernel

namespace Source
open POS04ExecutionFrontier
theorem revReady : ExecutionFrontier.Ready raw a := ready a (complete _)
theorem rev_audit : ExecutionFrontier.AuditCheck raw a revReady := by
  refine ⟨by decide,?_,?_,?_,?_⟩
  · exact fun r =>
      let path := ComputedFIACH.acquisitionHistory a .source r
      (path.zip (path.drop 1)).map (fun e => (ComputedFIACH.LaneDisturbance.nominal,
        (runInputs6 a .source).base.base.policy e.1, Ambient.inK e.2))
  · exact word_eq a (complete _)
  · rintro ⟨r,n⟩ hi
    have hn : n = 1 ∨ n = 2 := by cases r <;> simpa [raw,audit,ComputedFIACH.acquisitionSnapshotIndices,routeIds,snapshotPositions,snapshotOccurrence] using hi
    rcases hn with rfl | rfl
    all_goals refine ⟨by omega,?_,?_⟩
    all_goals try (cases r <;> decide)
    all_goals
      rw [initial_eq a (complete _),prefix_check_iff a (complete _)]
      simp only [ExecutionFrontier.historyPrefix]
      cases r <;> decide +kernel
  · intro hist hh
    exact ⟨(hist,2),by cases hist <;> decide,rfl,by cases hist <;> decide⟩

theorem rev_paths : ExecutionFrontier.PathsAvailable raw a := by
  refine ⟨(routeView.read a).getD (fun r => ⟨r,[]⟩),
    (eventView.read a).getD (fun _ => ⟨.sourceLive,.sourceLive,false,false,false,false,0⟩),
    realizedStages,(receiverView.read a).getD ⟨false,false,false,false⟩,
    rfl,rfl,rfl,rfl,?_⟩
  rintro ⟨r,n⟩ hi
  dsimp only [raw]
  have hr : r ∈ routeIds := by cases r <;> decide
  refine ⟨hr,rfl,?_,?_⟩
  · cases r
    all_goals refine ⟨.mix1,[.mix2,.exit],rfl,rfl,?_,by decide,.exit,rfl,rfl,rfl,rfl⟩
    all_goals intro id hid; cases id <;> decide
  · cases r <;> refine ⟨rfl,rfl,rfl,?_⟩ <;> intro _
    all_goals exact ⟨.mix1,by decide,by decide,by decide,rfl,rfl,rfl⟩

theorem rev_roots_subset (x : Registers Register RegisterValue)
    (hx : x ∈ ExecutionFrontier.roots raw a revReady) :
    x ∈ POS04RegisterReadoutLaws.roots a .source := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hx
  subst x
  rw [initial_eq a (complete _)]
  apply List.mem_map.mpr
  refine ⟨ComputedFIACH.acquisitionInitialRun a .source i.1,?_,rfl⟩
  rcases i with ⟨r,n⟩
  cases r
  all_goals dsimp only [Prod.fst]; decide +kernel

theorem rev_readout_laws :
    RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal raw) raw.recipes a revReady.2
      (ExecutionFrontier.roots raw a revReady) := by
  apply RegisterFuture.restrict_readout_gate (POS04RegisterFuture.raw .source)
    (POS04RegisterReadoutLaws.recipes .source) a revReady.2
    (POS04RegisterReadoutLaws.roots a .source) _
    (POS04RegisterReadoutLaws.readout_gate (accept .source))
  · intro hn
    have ht := congrArg List.length hn
    change (raw.audit.map _).length = 0 at ht
    simp only [List.length_map] at ht
    have hp : raw.audit.length = 4 := by decide
    omega
  · intro r hr; exact FutureClosure.root _ (rev_roots_subset r hr)

theorem rev_rows (x : Run6) (act : Action) :
    (∀ e ∈ actualRows6 (runInputs6 a .source) x act, 0 ≤ e.2) ∧
    (((actualRows6 (runInputs6 a .source) x act).map Prod.snd).sum = 0 ∨
    ((actualRows6 (runInputs6 a .source) x act).map Prod.snd).sum = 1) := by
  have hr : actualRows6 (runInputs6 a .source) x act =
      actualRows6 (runInputs6 a .source) ⟨x.factor,0,0,([],[]),x.funded⟩ act := rfl
  rw [hr]
  cases hf : x.funded <;> cases ho : x.factor <;> cases act
  all_goals try (rename_i s; cases s)
  all_goals constructor
  all_goals first | decide +kernel | (intro e he; simp_all [actualRows6,enabled6])

theorem rev_row_laws : ExecutionFrontier.RowLawGate raw a revReady := by
  intro x hx d hd act ha
  rw [show AcquisitionExecution.rows raw.acquisition a x d act =
      actualRows6 (runInputs6 a .source) (decodeRun x) act from by
      simpa only [encode_decode] using actual_rows a (complete _) (decodeRun x) d act]
  exact rev_rows (decodeRun x) act

theorem rev_positive : ExecutionFrontier.Valid raw a :=
  ⟨revReady,rev_audit,canonical_domain.1,canonical_domain.2,rev_paths,
    POS04RegisterFuture.one_step a .source (complete _) (accept .source).2.1,rev_readout_laws,rev_row_laws⟩

end Source

namespace Target
open POS04ReceiverFrontier
theorem revReady : ExecutionFrontier.Ready raw a := ready a (complete _)
theorem rev_audit : ExecutionFrontier.AuditCheck raw a revReady := by
  refine ⟨by decide,?_,?_,?_,?_⟩
  · exact fun r =>
      let path := acquisitionHistory a .target r
      (path.zip (path.drop 1)).map (fun e => (LaneDisturbance.nominal,
        (runInputs6 a .target).base.base.policy e.1, Ambient.inK e.2))
  · exact word_equation a (complete _)
  · rintro ⟨r,n⟩ hi
    have hn : n = 1 ∨ n = 2 := by cases r <;> simpa [raw,POS04ExecutionFrontier.audit,
      acquisitionSnapshotIndices,routeIds,snapshotPositions,snapshotOccurrence] using hi
    rcases hn with rfl | rfl
    all_goals refine ⟨by omega,?_,?_⟩
    all_goals try (cases r <;> decide)
    all_goals
      rw [initial_equation a (complete _),prefix_check_iff a (complete _)]
      simp only [ExecutionFrontier.historyPrefix]
      cases r <;> decide +kernel
  · intro hist hh
    exact ⟨(hist,2),by cases hist <;> decide,rfl,by cases hist <;> decide⟩

theorem rev_roots_subset (x : Registers Register RegisterValue)
    (hx : x ∈ ExecutionFrontier.roots raw a revReady) :
    x ∈ POS04RegisterReadoutLaws.roots a .target := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hx
  subst x
  rw [initial_equation a (complete _)]
  apply List.mem_map.mpr
  refine ⟨acquisitionInitialRun a .target i.1,?_,rfl⟩
  rcases i with ⟨r,n⟩
  cases r
  all_goals dsimp only [Prod.fst]; decide +kernel

theorem rev_readout_laws :
    RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal raw) raw.recipes a revReady.2
      (ExecutionFrontier.roots raw a revReady) := by
  apply RegisterFuture.restrict_readout_gate (POS04RegisterFuture.raw .target)
    (POS04RegisterReadoutLaws.recipes .target) a revReady.2
    (POS04RegisterReadoutLaws.roots a .target) _
    (POS04RegisterReadoutLaws.readout_gate (accept .target))
  · intro hn
    have ht := congrArg List.length hn
    change (raw.audit.map _).length = 0 at ht
    simp only [List.length_map] at ht
    have hp : raw.audit.length = 4 := by decide
    omega
  · intro r hr; exact FutureClosure.root _ (rev_roots_subset r hr)

theorem rev_row_laws : ExecutionFrontier.RowLawGate raw a revReady := by
  intro x hx d hd act ha
  rw [show AcquisitionExecution.rows raw.acquisition a x d act =
      actualRows6 (runInputs6 a .target) (decodeRun x) act from by
      simpa only [encode_decode] using actual_rows a (complete _) (decodeRun x) d act]
  have he : actualRows6 (runInputs6 a .target) (decodeRun x) act =
      actualRows6 (runInputs6 a .source) (decodeRun x) act := rfl
  rw [he]
  exact Source.rev_rows (decodeRun x) act

theorem rev_positive : ExecutionFrontier.Valid raw a :=
  ⟨revReady,rev_audit,canonical_domain.1,canonical_domain.2,Source.rev_paths,
    POS04RegisterFuture.one_step a .target (complete _) ((accept .target).2.1),
    rev_readout_laws,rev_row_laws⟩

end Target

namespace Bridge
open POS04ExecutionBridge
theorem bridge_laws
    (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) :
    ExecutionBridge.Laws raw a hs ht (translation_ready a) := by
  constructor
  · rfl
  · rfl
  · change POS04ReceiverFrontier.acquisition.histories.read a = POS04ExecutionFrontier.acquisition.histories.read a
    rw [POS04ReceiverFrontier.word_equation a (complete _),
      POS04ExecutionFrontier.word_eq a (complete _)]
    apply congrArg some
    funext r
    cases r <;> decide +kernel
  · intro r
    rw [translate_eq]
    change ExecutionFrontier.initial POS04ExecutionFrontier.raw a _ r =
      ExecutionFrontier.initial POS04ReceiverFrontier.raw a _ r
    rw [POS04ExecutionFrontier.initial_eq a (complete _),
      POS04ReceiverFrontier.initial_equation a (complete _)]
    cases r <;> rfl
  · intro x hx da o
    rw [translate_eq]
    change RegisterFuture.weight (POS04RegisterFuture.raw .target) a _ x da o =
      RegisterFuture.weight (POS04RegisterFuture.raw .source) a _ x da o
    rw [← encode_decode x,POS04RegisterFuture.weight_eq a .target (complete _),
      POS04RegisterFuture.weight_eq a .source (complete _)]
    rfl
  · intro x hx d hd act ha o ho
    rw [translate_eq,translate_eq]
    change AcquisitionExecution.update POS04ExecutionFrontier.acquisition a _ x d act o =
      AcquisitionExecution.update POS04ReceiverFrontier.acquisition a _ x d act o
    rw [← encode_decode x,POS04ExecutionFrontier.actual_update a (complete _),
      POS04ReceiverFrontier.actual_update a (complete _)]
    rfl
  · intro x hx
    rw [translate_eq]
    change mapSnapshotReadout acquisitionSnapshotMaps
      (RegisterFuture.observation (POS04RegisterFuture.raw .source) a _ x) =
      RegisterFuture.observation (POS04RegisterFuture.raw .target) a _ x
    rw [← encode_decode x,POS04RegisterFuture.observation_eq a .source (complete _),
      POS04RegisterFuture.observation_eq a .target (complete _)]
    rfl

theorem valid : ExecutionBridge.Valid raw a :=
  ⟨Source.rev_positive,Target.rev_positive,translation_ready a,bridge_laws⟩
end Bridge

theorem seed_equations : POS04CompleteLineage.SeedEquations a := by
  refine ⟨POS04ExecutedCorridor.canonicalCoordinate,rfl,?_,?_⟩
  · intro i j he
    rcases POS04ExecutedCorridor.audited_values i with hi | hi | hi | hi
    all_goals rcases POS04ExecutedCorridor.audited_values j with hj | hj | hj | hj
    all_goals simp only [hi,hj] at he ⊢
    all_goals exact (by decide +kernel :
      POS04ExecutedCorridor.canonicalCoordinate (POS04ExecutedCorridor.observed a _).predictive =
        POS04ExecutedCorridor.canonicalCoordinate (POS04ExecutedCorridor.observed a _).predictive →
      (POS04ExecutedCorridor.observed a _).predictive = (POS04ExecutedCorridor.observed a _).predictive) he
  · intro histories he i hi hend
    have hhist := Option.some.inj (he.symm.trans (POS04ExecutionFrontier.word_eq a (complete _)))
    subst histories
    rcases i with ⟨r,n⟩
    have hn : n = 2 := by cases r <;> simpa using hend
    subst n
    cases r <;> decide +kernel

theorem corridor_check : AcquisitionCorridor.ViewCheck POS04AcquisitionCorridor.raw (POS04AcquisitionCorridor.view a) := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,?_⟩
  intro r hr
  refine ⟨by cases r <;> decide,by cases r <;> unfold AcquisitionExecution.PathCheck <;>
      refine ⟨.mix1,[.mix2,.exit],rfl,rfl,by decide,by decide,.exit,rfl,rfl,rfl,rfl⟩,
    by cases r <;> unfold AcquisitionExecution.Activated AcquisitionExecution.Mixed <;>
      refine ⟨rfl,rfl,rfl,fun _ => ⟨.mix1,by decide,by decide,by decide,rfl,rfl,rfl⟩⟩,
    by cases r <;> decide,by cases r <;> decide,?_⟩
  cases r <;> unfold CSTTT.CorridorTheory.AtomicChain.AtomicLegPass <;> decide +kernel

theorem lineage_valid : POS04CompleteLineage.Valid reversedHistories := by
  refine ⟨(POS04AcquisitionCorridor.pass_iff a (complete _)).mpr corridor_check,
    (POS04CompleteLineage.seed_readout_iff a).mpr ⟨complete _,seed_equations⟩,?_,?_,?_,
    POS04RouteReadout.reversed_pass,Bridge.valid⟩
  · apply (POS04FactorTransport.pass_iff reversedHistories).mpr
    refine ⟨complete _,complete _,?_⟩
    apply (POS04FactorTransport.factor_equations_iff reversedHistories).mp
    exact POS04FactorTransport.canonical_equations
  · exact ⟨complete _,POS04CompleteLineage.baseline_record.2⟩
  · exact (lineage_checked_parts reversedHistories reversed_histories_lineage_lane).2.2

theorem legacy_full : validF ⟨reversedHistories⟩ = true := by decide +kernel

theorem full : FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories))
    reversedHistories.assignment := by
  apply (POS04FinalCorrespondence.final_full_iff reversedHistories).mpr
  have h := validF_source_and_staging ⟨reversedHistories⟩ legacy_full
  exact ⟨⟨h.1,h.2,by change packageLaneCheck reversedHistories.assignment = true; decide +kernel,lineage_valid⟩,
    by change fullAutonomyCheck reversedHistories = true; decide +kernel⟩

theorem operational : FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories))
    reversedHistories.assignment := by
  apply (POS04FinalCorrespondence.final_operational_iff reversedHistories).mpr
  have h := (POS04FinalCorrespondence.final_full_iff reversedHistories).mp full
  exact ⟨h.1,by change operationalAutonomyCheck reversedHistories = true; decide +kernel⟩

theorem readouts :
    FinalHandoff.IntegratedTargetRealization (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment ∧
    FinalHandoff.StrictTemporalLineage (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment ∧
    FinalHandoff.PostWithdrawalFullAutonomy (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment :=
  FinalHandoff.temporalFIACHCertificateSoundness_generic_F _ _ full

theorem operational_readouts :
    FinalHandoff.IntegratedTargetRealization (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment ∧
    FinalHandoff.StrictTemporalLineage (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment ∧
    FinalHandoff.PostWithdrawalOperationalAutonomy (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment :=
  FinalHandoff.temporalFIACHCertificateSoundness_generic_O _ _ operational

theorem receiver_readout : FinalHandoff.ReceiverReadout
    (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment :=
  FinalHandoff.receiver_soundness_F _ _ full

theorem outputs_and_certificates :
    acquisitionRouteOutput reversedHistories .a = some 1 ∧ acquisitionRouteOutput reversedHistories .b = some 0 ∧
    FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment ∧
    FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment :=
  ⟨reversed_histories_outputs.1,reversed_histories_outputs.2,full,operational⟩
end CSTTT.TargetTheory.GenericHandoff.POS04FinalReversal
