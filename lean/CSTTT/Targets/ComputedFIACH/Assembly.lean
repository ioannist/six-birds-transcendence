import CSTTT.Targets.ComputedFIACH.Endpoint

/-! G6: generic over raw assignments in the declared typed finite POS-04
primitive namespace. No verdict, invariant, entry, observer, signature or
label is supplied. F uses package-preserving autonomy; AF→P is disclosed.
“None inferred” is proof-structural for F. O is the supplementary N3 operational
notion and has the three genuine independence controls. C4–C7 are surrogates;
The fixed carrier/cell/action/event/route, stage/cover and audit interface
is not the broader G0 RawHandoff contract; TTH-06 remains conditional pending
that generalization. This is not full P05, T17-I, recognition, or a physical-system claim. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory CSTTT.AutonomyTheory CSTTT.CorridorTheory.AtomicChain
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Only raw data; validity is an external computed check, not a proof field. -/
structure FiniteFIACHCertificate where
  model : RawLaneModel

def sourcePackageCheck (m : RawLaneModel) : Bool :=
  decide (Complete primitiveCells m.assignment) && packageCheck m.assignment .source

/-- The declared stage/cover is fixed, and maps are cell-independent.
These raw equations are verified by G2c for every assignment, including partial
ones. Totality is checked independently by completeness. -/
def stagedPreservationCheck (m : RawLaneModel) : Bool :=
  decide (Complete primitiveCells m.assignment) &&
    decide (AssignedPackagePass m.assignment .source) && packageLaneCheck m.assignment

def validF (c : FiniteFIACHCertificate) : Bool :=
  sourcePackageCheck c.model && stagedPreservationCheck c.model &&
    packageLaneCheck c.model.assignment && lineageLaneCheck c.model && fullAutonomyCheck c.model

def validO (c : FiniteFIACHCertificate) : Bool :=
  sourcePackageCheck c.model && stagedPreservationCheck c.model &&
    packageLaneCheck c.model.assignment && lineageLaneCheck c.model && operationalAutonomyCheck c.model

def recognitionStatusOf (_c : FiniteFIACHCertificate) : RecognitionStatus := .notAddressed

def IntegratedTargetRealization (m : RawLaneModel) : Prop :=
  MapTotal m.assignment canonicalStage (arrivalCover .target) ∧
  ValuePreserving m.assignment canonicalStage (arrivalCover .target) ∧
  EdgeCompatible m.assignment canonicalStage (arrivalCover .target) ∧
  (∀ c k, k ∈ (arrivalCover .target).scopes c →
    image m.assignment k = mappedLocal m.assignment canonicalStage (arrivalCover .target) c k) ∧
  AssignedPackagePass (assembledAssignment m.assignment canonicalStage (arrivalCover .target)
    .target (arrival_cover_check .target)) .target

def StrictTemporalLineage (m : RawLaneModel) : Prop :=
  (∀ r ∈ routeIds, ∃ a, checkedAcquisition m = some a ∧ StrictCorridorWitness [acquisitionAtomicLeg m a r]) ∧
  (∃ ha : BridgeAdmissible (assignmentRawBridge m), ∃ hl : BridgePrimitiveLaws (assignmentRawBridge m),
    ∃ hd : SnapshotAuditCheck (assignmentRawBridge m) (bridgeSnapshotAudit (assignmentRawBridge m)),
      ∀ i : Audited (assignmentRawBridge m).auditFrontier,
        FrozenBridgeSnapshotResult (assignmentRawBridge m) ha hl hd i) ∧
  TypedAcquisitionEndpointPass m ∧ routeStatusOfRaw (assignmentRawBridge m) = .routeIndexed

def PostWithdrawalFullAutonomy (m : RawLaneModel) : Prop :=
  AF m ∧ ∀ e ∈ entries m, ∃ s, e.factor = .inK s ∧
    Nonempty (ExactAutonomyCertificate (computedExactAutonomy m s))

def PostWithdrawalOperationalAutonomy (m : RawLaneModel) : Prop :=
  AO m ∧ Viable8 (withdrawnInputs m) .target (greatestO m)

theorem derive_package_lane (m : RawLaneModel) (h : PackageLane m.assignment) :
    IntegratedTargetRealization m := package_lane_assembles h

theorem derive_lineage_lane (m : RawLaneModel) (h : LineageLane m) : StrictTemporalLineage m := by
  obtain ⟨hc,hb,he⟩ := lineage_checked_parts m h
  exact ⟨fun r hr => acquisition_corridor_constructs m hc r hr,
    acquisition_bridge_frozen m hb,he,lineage_route_status m h⟩

theorem derive_full_autonomy_lane (m : RawLaneModel) (h : AF m) : PostWithdrawalFullAutonomy m :=
  ⟨h,AF_each_entry_exact_autonomy m h⟩

theorem derive_operational_autonomy_lane (m : RawLaneModel) (h : AO m) :
    PostWithdrawalOperationalAutonomy m := ⟨h,greatest8_viable _ _⟩

/-- Each conclusion consumes its own computed subcheck. The separate theorem
AF→P is not used to supply the P field. -/
theorem temporalFIACH_sound_F (c : FiniteFIACHCertificate) (h : validF c = true) :
    IntegratedTargetRealization c.model ∧ StrictTemporalLineage c.model ∧
      PostWithdrawalFullAutonomy c.model := by
  obtain ⟨hrest,ha⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hrest,hl⟩ := Bool.and_eq_true_iff.mp hrest
  have hp := (Bool.and_eq_true_iff.mp hrest).2
  exact ⟨derive_package_lane _ hp,derive_lineage_lane _ hl,derive_full_autonomy_lane _ ha⟩

theorem temporalFIACH_sound_O (c : FiniteFIACHCertificate) (h : validO c = true) :
    IntegratedTargetRealization c.model ∧ StrictTemporalLineage c.model ∧
      PostWithdrawalOperationalAutonomy c.model := by
  obtain ⟨hrest,ha⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hrest,hl⟩ := Bool.and_eq_true_iff.mp hrest
  have hp := (Bool.and_eq_true_iff.mp hrest).2
  exact ⟨derive_package_lane _ hp,derive_lineage_lane _ hl,derive_operational_autonomy_lane _ ha⟩

theorem baseline_source_package : sourcePackageCheck baseline = true := by decide +kernel
theorem baseline_staged_preservation : stagedPreservationCheck baseline = true := by decide +kernel

theorem baseline_valid_F : validF ⟨baseline⟩ = true := by
  simp only [validF,baseline_source_package,baseline_staged_preservation,
    show packageLaneCheck baseline.assignment = true from package_lane_positive,
    show lineageLaneCheck baseline = true from baseline_lineage_lane,
    show fullAutonomyCheck baseline = true from baseline_AF]
  rfl

theorem baseline_valid_O : validO ⟨baseline⟩ = true := by
  simp only [validO,baseline_source_package,baseline_staged_preservation,
    show packageLaneCheck baseline.assignment = true from package_lane_positive,
    show lineageLaneCheck baseline = true from baseline_lineage_lane,
    show operationalAutonomyCheck baseline = true from baseline_AO]
  rfl

/-- Registered controls are raw cell/retention edits, never outcome labels. -/
theorem F_control_vectors :
    (¬ PackageLane packageDeletion.assignment ∧ LineageLane packageDeletion ∧ ¬ AF packageDeletion) ∧
    (PackageLane lineageDeletion.assignment ∧ ¬ LineageLane lineageDeletion ∧ AF lineageDeletion) ∧
    (PackageLane withdrawalDeletion.assignment ∧ LineageLane withdrawalDeletion ∧ ¬ AF withdrawalDeletion) := by
  exact ⟨⟨package_lane_missing .publishedC,package_deletion_lineage_lane,package_deletion_not_AF⟩,
    ⟨lineage_deletion_package,lineage_deletion_not_lineage_lane,lineage_deletion_AF⟩,
    package_lane_positive,withdrawal_deletion_lineage_lane,withdrawal_deletion_not_AF⟩

theorem O_control_vectors :
    (¬ PackageLane packageDeletion.assignment ∧ LineageLane packageDeletion ∧ AO packageDeletion) ∧
    (PackageLane lineageDeletion.assignment ∧ ¬ LineageLane lineageDeletion ∧ AO lineageDeletion) ∧
    (PackageLane withdrawalDeletion.assignment ∧ LineageLane withdrawalDeletion ∧ ¬ AO withdrawalDeletion) := by
  exact ⟨⟨package_lane_missing .publishedC,package_deletion_lineage_lane,package_deletion_AO⟩,
    ⟨lineage_deletion_package,lineage_deletion_not_lineage_lane,lineage_deletion_AO⟩,
    package_lane_positive,withdrawal_deletion_lineage_lane,withdrawal_deletion_not_AO⟩

theorem operational_lanes_logically_independent :
    (∃ m, ¬ PackageLane m.assignment ∧ LineageLane m ∧ AO m) ∧
    (∃ m, PackageLane m.assignment ∧ ¬ LineageLane m ∧ AO m) ∧
    (∃ m, PackageLane m.assignment ∧ LineageLane m ∧ ¬ AO m) :=
  ⟨⟨packageDeletion,O_control_vectors.1⟩,⟨lineageDeletion,O_control_vectors.2.1⟩,
    ⟨withdrawalDeletion,O_control_vectors.2.2⟩⟩

/-- Direct failure of the named package readout: the deleted C1 input has
no value for the required total stage map. No converse of a sufficient check
is assumed. -/
theorem package_deletion_no_realization : ¬ IntegratedTargetRealization packageDeletion := by
  intro h
  obtain ⟨arrow,_,hsource,hpresent,_⟩ :=
    h.1 .c1 .publishedC (primitive_cells_complete .publishedC)
  rw [hsource] at hpresent
  change false = true at hpresent
  contradiction

/-- Direct failure of the named lineage readout: its constructed corridor
would require the missing source audit vertex. -/
theorem lineage_deletion_no_strict_lineage : ¬ StrictTemporalLineage lineageDeletion := by
  intro h
  obtain ⟨a,ha,hw⟩ := h.1 .a (by decide)
  have hc : checkedAcquisition lineageDeletion = some (image lineageDeletion.assignment) := by
    unfold checkedAcquisition
    have hcomplete : Complete acquisitionDependencies (image lineageDeletion.assignment) := by decide
    simp [hcomplete]
  have he : a = image lineageDeletion.assignment := Option.some.inj (ha.symm.trans hc)
  subst a
  have hp := hw.pass
  simp only [CSTTT.CorridorTheory.AtomicChain.CorridorPass,chainCheck] at hp
  have hbad := lineage_deletion_atomic_audit .a
  simp [AtomicLegCheck,interventionCheck,hbad] at hp

/-- The F/O readouts include the autonomy obligation itself, so these are
negative readout proofs, not failure-of-a-sufficient-test arguments. -/
theorem package_deletion_no_full_readout : ¬ PostWithdrawalFullAutonomy packageDeletion :=
  fun h => package_deletion_not_AF h.1

theorem withdrawal_deletion_no_full_readout : ¬ PostWithdrawalFullAutonomy withdrawalDeletion :=
  fun h => withdrawal_deletion_not_AF h.1

theorem withdrawal_deletion_no_operational_readout :
    ¬ PostWithdrawalOperationalAutonomy withdrawalDeletion :=
  fun h => withdrawal_deletion_not_AO h.1

theorem F_readout_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ StrictTemporalLineage packageDeletion ∧
      ¬ PostWithdrawalFullAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ StrictTemporalLineage lineageDeletion ∧
      PostWithdrawalFullAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ StrictTemporalLineage withdrawalDeletion ∧
      ¬ PostWithdrawalFullAutonomy withdrawalDeletion) :=
  ⟨⟨package_deletion_no_realization,derive_lineage_lane _ package_deletion_lineage_lane,
      package_deletion_no_full_readout⟩,
   ⟨derive_package_lane _ lineage_deletion_package,lineage_deletion_no_strict_lineage,
      derive_full_autonomy_lane _ lineage_deletion_AF⟩,
   ⟨derive_package_lane _ package_lane_positive,derive_lineage_lane _ withdrawal_deletion_lineage_lane,
      withdrawal_deletion_no_full_readout⟩⟩

theorem O_readout_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ StrictTemporalLineage packageDeletion ∧
      PostWithdrawalOperationalAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ StrictTemporalLineage lineageDeletion ∧
      PostWithdrawalOperationalAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ StrictTemporalLineage withdrawalDeletion ∧
      ¬ PostWithdrawalOperationalAutonomy withdrawalDeletion) :=
  ⟨⟨package_deletion_no_realization,derive_lineage_lane _ package_deletion_lineage_lane,
      derive_operational_autonomy_lane _ package_deletion_AO⟩,
   ⟨derive_package_lane _ lineage_deletion_package,lineage_deletion_no_strict_lineage,
      derive_operational_autonomy_lane _ lineage_deletion_AO⟩,
   ⟨derive_package_lane _ package_lane_positive,derive_lineage_lane _ withdrawal_deletion_lineage_lane,
      withdrawal_deletion_no_operational_readout⟩⟩

theorem operational_readouts_logically_independent :
    (∃ m, ¬ IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
      PostWithdrawalOperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ ¬ StrictTemporalLineage m ∧
      PostWithdrawalOperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
      ¬ PostWithdrawalOperationalAutonomy m) :=
  ⟨⟨packageDeletion,O_readout_control_vectors.1⟩,
   ⟨lineageDeletion,O_readout_control_vectors.2.1⟩,
   ⟨withdrawalDeletion,O_readout_control_vectors.2.2⟩⟩

/-- Positive certificates are raw data whose validity is independently computed. -/
theorem full_certificate_satisfiable : ∃ c : FiniteFIACHCertificate, validF c = true :=
  ⟨⟨baseline⟩,baseline_valid_F⟩
theorem operational_certificate_satisfiable : ∃ c : FiniteFIACHCertificate, validO c = true :=
  ⟨⟨baseline⟩,baseline_valid_O⟩

/-- Read out the additional source/staging obligations independently of the lanes. -/
theorem validF_source_and_staging (c : FiniteFIACHCertificate) (h : validF c = true) :
    sourcePackageCheck c.model = true ∧ stagedPreservationCheck c.model = true := by
  obtain ⟨hrest,_⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hrest,_⟩ := Bool.and_eq_true_iff.mp hrest
  obtain ⟨hrest,_⟩ := Bool.and_eq_true_iff.mp hrest
  exact Bool.and_eq_true_iff.mp hrest

/-- TTH-05 transport for arbitrary nominal words from EVERY derived entry.
All-support safety belongs to AF_exact_certificate, not an existential lucky branch. -/
theorem temporalFIACH_full_nominal_words (c : FiniteFIACHCertificate) (h : validF c = true)
    (e : WithdrawalEntry) (he : e ∈ entries c.model) (word : List LaneDisturbance) :
    ∃ s, e.factor = .inK s ∧ ∃ y,
      ControlledRun (computedExactAutonomy c.model s) s word y ∧
        packageAtCheck c.model y = true :=
  AF_each_entry_nominal_words c.model (Bool.and_eq_true_iff.mp h).2 e he word

theorem certificate_recognition_not_addressed (c : FiniteFIACHCertificate) :
    recognitionStatusOf c = .notAddressed := rfl

end CSTTT.TargetTheory.ComputedFIACH
