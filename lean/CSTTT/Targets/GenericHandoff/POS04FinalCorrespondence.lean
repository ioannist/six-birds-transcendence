import CSTTT.Targets.GenericHandoff.POS04FinalHandoff
/-! Exact final whole-gate adapters for every partial POS04 assignment.
All frozen source/staging/package and nominal F/O conditions are retained.
Complete actual lineage replaces the proven-insufficient legacy lineage;
that gate change is kernel-adjudicated by the same raw relabeling proposal.
No positive adapter, supplied verdict or hidden completeness premise occurs. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04FinalCorrespondence
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH POS04ResourceRuntime
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

theorem complete_pass_iff_valid (m : RawLaneModel) :
    RuntimeLineage.CompletePass (POS04RuntimeLineage.raw (protocol m)) (image m.assignment) ↔
      POS04CompleteLineage.Valid m := by
  constructor
  · rintro ⟨⟨hc,hs,hf,hr,hrt,hx,_⟩,he⟩
    exact ⟨hc,hs,(POS04FactorTransport.pass_iff m).mpr ((POS04RuntimeLineage.factor_iff m).mp hf),
      (POS04RuntimeLineage.record_iff _ _).mp hr,(POS04AcquisitionEndpoint.pass_iff m).mp he,
      (POS04RuntimeRoute.pass_iff _ _).mp hrt,hx⟩
  · rintro ⟨hc,hs,hf,hr,he,hrt,hx⟩
    have retained := (POS04RuntimeRoute.pass_iff (protocol m) (image m.assignment)).mpr hrt
    exact ⟨⟨hc,hs,(POS04RuntimeLineage.factor_iff m).mpr ((POS04FactorTransport.pass_iff m).mp hf),
      (POS04RuntimeLineage.record_iff _ _).mpr hr,retained,hx,
      POS04RuntimeLineage.shared_from_route _ _ retained⟩,(POS04AcquisitionEndpoint.pass_iff m).mpr he⟩
theorem source_gate (m : RawLaneModel) (hp : PackageLane m.assignment) :
    OwningHandoff.SourcePackagePass (POS04RawHandoff.raw (protocol m)) m.assignment ↔ sourcePackageCheck m = true := by
  have hc := (package_lane_iff _).mp hp |>.1
  change (POS04Dispatcher.package .source).accept m.assignment ↔ _
  rw [POS04Dispatcher.package_accept_iff]
  simp only [sourcePackageCheck,Bool.and_eq_true,decide_eq_true_eq,package_check_iff]
  exact (and_iff_right hc).symm

theorem staging_gate (m : RawLaneModel) (hp : PackageLane m.assignment) (hs : sourcePackageCheck m = true) :
    stagedPreservationCheck m = true := by
  have hc := (package_lane_iff _).mp hp |>.1
  have accepted : AssignedPackagePass m.assignment .source := by
    simp only [sourcePackageCheck,Bool.and_eq_true,package_check_iff] at hs
    exact hs.2
  simp only [stagedPreservationCheck,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨hc,accepted⟩,hp⟩

def Common (m : RawLaneModel) : Prop := sourcePackageCheck m = true ∧ stagedPreservationCheck m = true ∧
  PackageLane m.assignment ∧ POS04CompleteLineage.Valid m

theorem nominal_full_iff (m : RawLaneModel) :
    NominalHandoff.HandoffPass_F (POS04RawHandoff.raw (protocol m)) (POS04NominalHandoff.instructions (protocol m)) m.assignment ↔
      Common m ∧ AF m := by
  constructor
  · intro h
    have hp := (POS04DispatchedStage.valid_iff _).mp h.2.2.2.2.1
    have source := (source_gate m hp).mp h.2.2.1
    have lineage := h.2.2.2.2.2.1
    rw [POS04RawHandoff.target_eq,POS04RawHandoff.lineage_pass_iff] at lineage
    have full : NominalHandoff.FullAutonomy (POS04RawHandoff.raw (protocol m))
        (POS04NominalHandoff.instructions (protocol m)) m.assignment :=
      (NominalHandoff.full_subcheck_iff _ _ _).mp ⟨h.2.1,h.2.2.2.2.2.2⟩
    exact ⟨⟨source,staging_gate m hp source,hp,(complete_pass_iff_valid _).mp lineage⟩,
      (POS04NominalHandoff.full_iff_af _).mp full⟩
  · rintro ⟨⟨source,_,hp,hl⟩,full⟩
    have realization := (POS04NominalHandoff.full_iff_af m).mpr full
    refine ⟨POS04NominalHandoff.laws _ _,realization.1,(source_gate m hp).mpr source,
      POS04RawHandoff.coherence_of_lineage m (POS04CompleteLineage.soundness m hl),
      (POS04DispatchedStage.valid_iff _).mpr hp,?_,?_⟩
    · rw [POS04RawHandoff.target_eq,POS04RawHandoff.lineage_pass_iff]
      exact (complete_pass_iff_valid m).mpr hl
    · exact (OwningHandoff.full_subcheck_iff _ _).mpr realization.2

theorem nominal_operational_iff (m : RawLaneModel) :
    NominalHandoff.HandoffPass_O (POS04RawHandoff.raw (protocol m)) (POS04NominalHandoff.instructions (protocol m)) m.assignment ↔
      Common m ∧ AO m := by
  constructor
  · intro h
    have hp := (POS04DispatchedStage.valid_iff _).mp h.2.2.2.2.1
    have source := (source_gate m hp).mp h.2.2.1
    have lineage := h.2.2.2.2.2.1
    rw [POS04RawHandoff.target_eq,POS04RawHandoff.lineage_pass_iff] at lineage
    have operational : NominalHandoff.OperationalAutonomy (POS04RawHandoff.raw (protocol m))
        (POS04NominalHandoff.instructions (protocol m)) m.assignment :=
      (NominalHandoff.operational_subcheck_iff _ _ _).mp ⟨h.2.1,h.2.2.2.2.2.2⟩
    exact ⟨⟨source,staging_gate m hp source,hp,(complete_pass_iff_valid _).mp lineage⟩,
      (POS04NominalHandoff.operational_iff_ao _).mp operational⟩
  · rintro ⟨⟨source,_,hp,hl⟩,operational⟩
    have realization := (POS04NominalHandoff.operational_iff_ao m).mpr operational
    refine ⟨POS04NominalHandoff.laws _ _,realization.1,(source_gate m hp).mpr source,
      POS04RawHandoff.coherence_of_lineage m (POS04CompleteLineage.soundness m hl),
      (POS04DispatchedStage.valid_iff _).mpr hp,?_,?_⟩
    · rw [POS04RawHandoff.target_eq,POS04RawHandoff.lineage_pass_iff]
      exact (complete_pass_iff_valid m).mpr hl
    · exact (OwningHandoff.operational_subcheck_iff _ _).mpr realization.2

theorem final_full_iff (m : RawLaneModel) :
    FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (protocol m)) m.assignment ↔ Common m ∧ AF m :=
  (POS04FinalHandoff.full_gate_iff_nominal m).trans (nominal_full_iff m)

theorem final_operational_iff (m : RawLaneModel) :
    FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (protocol m)) m.assignment ↔ Common m ∧ AO m :=
  (POS04FinalHandoff.operational_gate_iff_nominal m).trans (nominal_operational_iff m)

theorem final_full_iff_complete (m : RawLaneModel) :
    FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (protocol m)) m.assignment ↔ POS04CompleteFIACH.HandoffPassF ⟨m⟩ := by
  rw [final_full_iff]
  change (Common m ∧ AF m) ↔ POS04CompleteFIACH.Common m ∧ POS04RegisterGames.Full m
  rw [POS04RegisterGames.full_iff_af]
  rfl

theorem final_operational_iff_complete (m : RawLaneModel) :
    FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (protocol m)) m.assignment ↔ POS04CompleteFIACH.HandoffPassO ⟨m⟩ := by
  rw [final_operational_iff]
  change (Common m ∧ AO m) ↔ POS04CompleteFIACH.Common m ∧ POS04RegisterGames.Operational m
  rw [POS04RegisterGames.operational_iff_ao]
  rfl

theorem relabel_source_check : sourcePackageCheck POS04LineageFutureBoundary.proposal = true :=
  (validF_source_and_staging _ POS04CompleteLineage.relabel_legacy_F_accepts).1

theorem relabel_stage_check : stagedPreservationCheck POS04LineageFutureBoundary.proposal = true :=
  (validF_source_and_staging _ POS04CompleteLineage.relabel_legacy_F_accepts).2

theorem relabel_legacy_F : validF ⟨POS04LineageFutureBoundary.proposal⟩ = true :=
  POS04CompleteLineage.relabel_legacy_F_accepts

theorem relabel_legacy_O : validO ⟨POS04LineageFutureBoundary.proposal⟩ = true :=
  POS04CompleteLineage.relabel_legacy_O_accepts

theorem relabel_no_final_F : ¬ FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (protocol POS04LineageFutureBoundary.proposal))
    POS04LineageFutureBoundary.proposal.assignment := by
  intro h
  exact POS04HistoricalSparseFIACH.relabel_vectors.2.1
    ((POS04FinalHandoff.lineage_iff _).mp (FinalHandoff.temporalFIACHCertificateSoundness_generic_F _ _ h).2.1)

theorem relabel_no_final_O : ¬ FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (protocol POS04LineageFutureBoundary.proposal))
    POS04LineageFutureBoundary.proposal.assignment := by
  intro h
  exact POS04HistoricalSparseFIACH.relabel_vectors.2.1
    ((POS04FinalHandoff.lineage_iff _).mp (FinalHandoff.temporalFIACHCertificateSoundness_generic_O _ _ h).2.1)

/-- The weaker frozen legacy gate cannot be identified with the completed gate. -/
theorem legacy_full_gate_not_equivalent :
    ¬ (∀ m : RawLaneModel, FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (protocol m)) m.assignment ↔ validF ⟨m⟩ = true) :=
  fun equivalence => relabel_no_final_F ((equivalence _).mpr relabel_legacy_F)

theorem legacy_operational_gate_not_equivalent :
    ¬ (∀ m : RawLaneModel, FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (protocol m)) m.assignment ↔ validO ⟨m⟩ = true) :=
  fun equivalence => relabel_no_final_O ((equivalence _).mpr relabel_legacy_O)

end CSTTT.TargetTheory.GenericHandoff.POS04FinalCorrespondence
