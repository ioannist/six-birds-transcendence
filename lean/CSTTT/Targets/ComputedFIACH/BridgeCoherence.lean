import CSTTT.Targets.ComputedFIACH.BridgeReadouts

/-! Assignment-indexed normalized row certificates for the bridge's real
run dynamics. The finite checks are raw equations; the universal counter,
tick and representative conclusions are derived, not enumerated at a horizon. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192

def RunRowCheck (m : RawLaneModel) : Prop :=
  ∀ tag : Tag, ∀ s u : KState, ∀ act : Action,
    let d := runInputs6 (image m.assignment) tag
    mass6 d (.inK s) act (predictive6 d (.inK u)) =
      (kernel.map fun v => if predictive6 d (.inK v) = predictive6 d (.inK u)
        then rowWeight (d.base.base.rows s act) v else 0).sum

def RunRepresentativeCheck (m : RawLaneModel) : Prop :=
  ∀ tag : Tag, ∀ s : KState, let d := runInputs6 (image m.assignment) tag
    ∃ u ∈ kernel, representative6 d (predictive6 d (.inK s)) = .inK u ∧
      predictive6 d (.inK u) = predictive6 d (.inK s)

def RunTickCheck (m : RawLaneModel) : Prop :=
  ∀ tag : Tag, ∀ s : KState, ∀ act : Action,
    let d := runInputs6 (image m.assignment) tag
    d.ticks s act = d.ticks s (d.base.base.policy s)

instance (m : RawLaneModel) : Decidable (RunRowCheck m) := by unfold RunRowCheck; infer_instance
instance (m : RawLaneModel) : Decidable (RunRepresentativeCheck m) := by unfold RunRepresentativeCheck; infer_instance
instance (m : RawLaneModel) : Decidable (RunTickCheck m) := by unfold RunTickCheck; infer_instance

theorem bridge_outcome_union (m : RawLaneModel) (tag : Tag) (o : CSTTT.POS04.PredictiveNow)
    (ho : o ∈ outcomes6 (runInputs6 (image m.assignment) tag)) :
    o ∈ (assignmentRawBridge m).runOutcomes := by
  cases tag
  · exact List.mem_append.mpr (Or.inl ho)
  · by_cases hs : o ∈ outcomes6 (runInputs6 (image m.assignment) .source)
    · exact List.mem_append.mpr (Or.inl hs)
    · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨ho,by simp [hs]⟩))

theorem bridge_outcome_mem (m : RawLaneModel) (tag : Tag) (s : Ambient) :
    predictive6 (runInputs6 (image m.assignment) tag) s ∈ (assignmentRawBridge m).runOutcomes :=
  bridge_outcome_union m tag _ (outcomes6_cover _ s)

theorem bridge_positive_outcome_mem (m : RawLaneModel) (x : AcquisitionRun)
    (act : Action) (o : CSTTT.POS04.PredictiveNow)
    (h : 0 < (assignmentRawBridge m).runNumerator x act o) :
    o ∈ (assignmentRawBridge m).runOutcomes := by
  have hm : 0 < mass6 (runInputs6 (image m.assignment) x.1) x.2.factor act o := by
    change 0 < (if enabled6 (runInputs6 (image m.assignment) x.1) x.2 then _ else 0) at h
    split at h
    · exact h
    · omega
  by_cases ho : o ∈ outcomes6 (runInputs6 (image m.assignment) x.1)
  · exact bridge_outcome_union m x.1 o ho
  · rw [mass6_absent _ _ _ _ ho] at hm
    omega

theorem bridge_mass_core (m : RawLaneModel) (hr : RunRowCheck m) (tag : Tag)
    (s : KState) (x : Run6) (hx : x.factor = .inK s)
    (hen : enabled6 (runInputs6 (image m.assignment) tag) x = true)
    (act : Action) (o : CSTTT.POS04.PredictiveNow)
    (ho : ∃ u ∈ kernel, predictive6 (runInputs6 (image m.assignment) tag) (.inK u) = o) :
    (if enabled6 (runInputs6 (image m.assignment) tag) x then
      mass6 (runInputs6 (image m.assignment) tag) x.factor act o else 0) =
      (kernel.map fun v => if predictive6 (runInputs6 (image m.assignment) tag) (.inK v) = o then
        assignedActionStep (image m.assignment) tag s (actions.idxOf act) v else 0).sum := by
  obtain ⟨u,_,hu⟩ := ho
  have ha : actions[actions.idxOf act]? = some act := by cases act <;> decide
  simp only [hen,↓reduceIte,hx,← hu,assignedActionStep,ha]
  exact hr tag s u act

theorem source_factor_iff (m : RawLaneModel) (tag : Tag) (x : Run6) (s : KState) :
    (assignmentRawBridge m).runSourceFactor (tag,x) = some s ↔ tag = .source ∧ x.factor = .inK s := by
  cases tag <;> cases hf : x.factor <;> simp [assignmentRawBridge,hf]

theorem target_factor_iff (m : RawLaneModel) (tag : Tag) (x : Run6) (s : KState) :
    (assignmentRawBridge m).runTargetFactor (tag,x) = some s ↔ tag = .target ∧ x.factor = .inK s := by
  cases tag <;> cases hf : x.factor <;> simp [assignmentRawBridge,hf]

theorem bridge_representative_factor (m : RawLaneModel) (hrep : RunRepresentativeCheck m)
    (tag : Tag) (x : Run6) (act : Action) (o : CSTTT.POS04.PredictiveNow)
    (hout : ∃ v ∈ kernel, predictive6 (runInputs6 (image m.assignment) tag) (.inK v) = o) :
    ∃ u ∈ kernel, (update6 (runInputs6 (image m.assignment) tag) x act o).factor = .inK u ∧
      predictive6 (runInputs6 (image m.assignment) tag) (.inK u) = o := by
  obtain ⟨v,_,he⟩ := hout
  obtain ⟨u,hu,hfactor,hpredict⟩ := hrep tag v
  exact ⟨u,hu,by simpa only [update6,← he] using hfactor,hpredict.trans he⟩

theorem assignment_bridge_coherence (m : RawLaneModel)
    (hr : RunRowCheck m) (hrep : RunRepresentativeCheck m) (htick : RunTickCheck m) :
    BridgeRunCoherence (assignmentRawBridge m) := by
  refine ⟨by change 0 < 4; decide,?_,?_,bridge_positive_outcome_mem m,?_⟩
  · intro s _; exact bridge_outcome_mem m .source (.inK s)
  · intro s _; exact bridge_outcome_mem m .target (.inK s)
  · rintro ⟨tag,x⟩ act o
    refine ⟨?_,?_,rfl,?_,?_,?_,?_⟩
    · intro s hs hen hout
      obtain ⟨ht,hf⟩ := (source_factor_iff m tag x s).mp hs
      subst tag
      exact bridge_mass_core m hr .source s x hf hen act o hout
    · intro s hs hen hout
      obtain ⟨ht,hf⟩ := (target_factor_iff m tag x s).mp hs
      subst tag
      exact bridge_mass_core m hr .target s x hf hen act o hout
    · intro s hs
      obtain ⟨ht,hf⟩ := (source_factor_iff m tag x s).mp hs
      subst tag
      simpa only [assignmentRawBridge,update6,delta6,hf] using congrArg (x.ticks + ·) (htick .source s act)
    · intro s hs
      obtain ⟨ht,hf⟩ := (target_factor_iff m tag x s).mp hs
      subst tag
      simpa only [assignmentRawBridge,update6,delta6,hf] using congrArg (x.ticks + ·) (htick .target s act)
    · intro s hs hout
      obtain ⟨ht,_⟩ := (source_factor_iff m tag x s).mp hs
      subst tag
      obtain ⟨u,hu,hfactor,hpredict⟩ := bridge_representative_factor m hrep .source x act o hout
      exact ⟨u,hu,(source_factor_iff m .source _ u).mpr ⟨rfl,hfactor⟩,hpredict⟩
    · intro s hs hout
      obtain ⟨ht,_⟩ := (target_factor_iff m tag x s).mp hs
      subst tag
      obtain ⟨u,hu,hfactor,hpredict⟩ := bridge_representative_factor m hrep .target x act o hout
      exact ⟨u,hu,(target_factor_iff m .target _ u).mpr ⟨rfl,hfactor⟩,hpredict⟩

instance : AuditEnum SnapshotIndex := ⟨acquisitionSnapshotIndices,by
  rintro ⟨r,p⟩; cases r <;> cases p <;> decide⟩
instance (m : RawLaneModel) : DecidableEq (BridgeRunObservation (assignmentRawBridge m)) :=
  bridgeRunObservationDecEq _
instance (m : RawLaneModel) : Decidable (SnapshotAuditCheck (assignmentRawBridge m)
    (bridgeSnapshotAudit (assignmentRawBridge m))) := by
  unfold SnapshotAuditCheck
  dsimp only [assignmentRawBridge,bridgeSnapshotAudit]
  infer_instance
instance (m : RawLaneModel) : Decidable (SnapshotRunCheck (assignmentRawBridge m)) := by
  unfold SnapshotRunCheck
  dsimp only [assignmentRawBridge]
  infer_instance

def FiniteSnapshotReadouts (m : RawLaneModel) : Prop :=
  let b := assignmentRawBridge m
  ∀ i : SnapshotIndex, i ∈ b.auditFrontier →
    bridgeRunObservation b (bridgeSourceRun b i) =
      liftRunSnapshot b.sourcePredictiveMap (sourceSnapshotReadout b (bridgeSnapshotAudit b) i) ∧
    bridgeRunObservation b (bridgeTargetRun b i) =
      liftRunSnapshot b.targetPredictiveMap (targetSnapshotReadout b (bridgeSnapshotAudit b) i)
instance (m : RawLaneModel) : Decidable (FiniteSnapshotReadouts m) := by
  unfold FiniteSnapshotReadouts; infer_instance

def SnapshotExecutionEquations (m : RawLaneModel) : Prop :=
  let b := assignmentRawBridge m
  ∀ i : SnapshotIndex, i ∈ acquisitionSnapshotIndices →
    bridgeSourceRun b i = (.source,acquisitionSnapshotRun (image m.assignment) .source i) ∧
    bridgeTargetRun b i = (.target,acquisitionSnapshotRun (image m.assignment) .target i)
instance (m : RawLaneModel) : Decidable (SnapshotExecutionEquations m) := by
  unfold SnapshotExecutionEquations
  dsimp only [assignmentRawBridge]
  infer_instance

instance (m : RawLaneModel) : Decidable (AcquisitionFactorBridgePass m) := by
  unfold AcquisitionFactorBridgePass; infer_instance
instance (m : RawLaneModel) : Decidable (AcquisitionExecutionPass m) := by
  unfold AcquisitionExecutionPass; infer_instance
instance (m : RawLaneModel) : Decidable (AcquisitionSnapshotPass m) := by
  unfold AcquisitionSnapshotPass; infer_instance

def acquisitionBridgeCheck (m : RawLaneModel) : Bool :=
  match checkedAcquisition m with
  | none => false
  | some _ => decide (AcquisitionFactorBridgePass m ∧ AcquisitionExecutionPass m ∧
      AcquisitionSnapshotPass m ∧ RunRowCheck m ∧ RunRepresentativeCheck m ∧ RunTickCheck m ∧
      SnapshotAuditCheck (assignmentRawBridge m) (bridgeSnapshotAudit (assignmentRawBridge m)) ∧
      SnapshotRunCheck (assignmentRawBridge m) ∧ FiniteSnapshotReadouts m ∧
      SnapshotExecutionEquations m ∧ ∀ t : Tag, C6Accept (image m.assignment) t)

def AcquisitionBridgePass (m : RawLaneModel) := acquisitionBridgeCheck m = true

theorem acquisition_bridge_checked_parts (m : RawLaneModel) (h : AcquisitionBridgePass m) :
    AcquisitionFactorBridgePass m ∧ AcquisitionExecutionPass m ∧ AcquisitionSnapshotPass m ∧
    RunRowCheck m ∧ RunRepresentativeCheck m ∧ RunTickCheck m ∧
    SnapshotAuditCheck (assignmentRawBridge m) (bridgeSnapshotAudit (assignmentRawBridge m)) ∧
    SnapshotRunCheck (assignmentRawBridge m) ∧ FiniteSnapshotReadouts m ∧
    SnapshotExecutionEquations m ∧ ∀ t : Tag, C6Accept (image m.assignment) t := by
  unfold AcquisitionBridgePass acquisitionBridgeCheck at h
  split at h
  · contradiction
  · exact of_decide_eq_true h

theorem acquisition_bridge_frozen (m : RawLaneModel) (h : AcquisitionBridgePass m) :
    ∃ ha : BridgeAdmissible (assignmentRawBridge m),
      ∃ hl : BridgePrimitiveLaws (assignmentRawBridge m),
        ∃ hd : SnapshotAuditCheck (assignmentRawBridge m) (bridgeSnapshotAudit (assignmentRawBridge m)),
          ∀ i : Audited (assignmentRawBridge m).auditFrontier,
            FrozenBridgeSnapshotResult (assignmentRawBridge m) ha hl hd i := by
  obtain ⟨hfactor,_,_,hrows,hrep,hticks,hd,hroots,hreads,_,hc6⟩ := acquisition_bridge_checked_parts m h
  obtain ⟨ha,hl⟩ := acquisition_factor_bridge_laws m hfactor
  have hread : BridgeSnapshotReadoutCheck (assignmentRawBridge m) :=
    ⟨fun _ _ he => CSTTT.POS04.PredictiveNow.active.inj he,
      fun _ _ he => CSTTT.POS04.PredictiveNow.active.inj he,hreads⟩
  have hlaws : BridgeRunReadoutLaws (assignmentRawBridge m) :=
    ⟨hroots,hread,fun x _ act o _ => assignment_bridge_readout_updates m hc6 x act o⟩
  refine ⟨ha,hl,hd,?_⟩
  exact (bundledHeterogeneousTemporalTransport_frozen _ ha hl hd
    (assignment_bridge_coherence m hrows hrep hticks) hroots hread hlaws
    (assignment_bridge_full_bisim m hc6)).2.2.2.2

theorem acquisition_bridge_missing_dependency (m : RawLaneModel) (k : Cell)
    (hk : k ∈ acquisitionDependencies) :
    ¬ AcquisitionBridgePass {m with assignment := put m.assignment (swapCell k) none} := by
  simp [AcquisitionBridgePass,acquisitionBridgeCheck,acquisition_missing_dependency m k hk]

theorem baseline_full_assignment_bridge : AcquisitionBridgePass baseline := by
  unfold AcquisitionBridgePass acquisitionBridgeCheck
  rw [baseline_acquisition]
  decide +kernel

theorem package_deletion_full_assignment_bridge : AcquisitionBridgePass packageDeletion := by
  unfold AcquisitionBridgePass acquisitionBridgeCheck
  rw [package_deletion_acquisition]
  decide +kernel

theorem lineage_deletion_no_full_assignment_bridge : ¬ AcquisitionBridgePass lineageDeletion := by
  unfold AcquisitionBridgePass acquisitionBridgeCheck
  have hc : checkedAcquisition lineageDeletion = some (image lineageDeletion.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image lineageDeletion.assignment) := by decide
    simp [h]
  rw [hc]
  decide +kernel

theorem withdrawal_deletion_full_assignment_bridge : AcquisitionBridgePass withdrawalDeletion := by
  unfold AcquisitionBridgePass acquisitionBridgeCheck
  rw [withdrawal_deletion_acquisition]
  decide +kernel

theorem reversed_histories_full_assignment_bridge : AcquisitionBridgePass reversedHistories := by
  unfold AcquisitionBridgePass acquisitionBridgeCheck
  have hc : checkedAcquisition reversedHistories = some (image reversedHistories.assignment) := by
    unfold checkedAcquisition
    have h : Complete acquisitionDependencies (image reversedHistories.assignment) := by decide
    simp [h]
  rw [hc]
  decide +kernel

end CSTTT.TargetTheory.ComputedFIACH
