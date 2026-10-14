import CSTTT.Targets.GenericHandoff.FinalHandoff
import CSTTT.Targets.GenericHandoff.POS04ReceiverGate

/-! Owning final raw recipe specialization. Component/readout adapters and the
receiver addition quantify over all partial assignments. The separate frozen
whole-gate faithfulness audit is still required before TTH-06 promotion. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04FinalHandoff
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH POS04ResourceRuntime
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

abbrev Model := FinalHandoff.Raw Cell Cell Value Value Unit POS04RegisterDynamics.Register POS04RegisterDynamics.Register
  POS04RouteExecution.FrameValue POS04RegisterDynamics.RegisterValue POS04RegisterDynamics.RegisterValue
  KState Action Ambient RouteId HistoryId RouteId CSTTT.POS04.Stage EventId Tag LaneDisturbance
  CSTTT.POS04.PredictiveNow CSTTT.POS04.PredictiveNow KState Resource (Tag × Ambient)

def raw (p : POS04ResourceRuntime.Protocol) : Model :=
  ⟨POS04RawHandoff.raw p,POS04NominalHandoff.instructions p,POS04ReceiverGate.instructions p⟩

theorem package_iff (m : RawLaneModel) :
    FinalHandoff.IntegratedTargetRealization (raw (protocol m)) m.assignment ↔ IntegratedTargetRealization m :=
  POS04RawHandoff.package_iff m

theorem lineage_iff (m : RawLaneModel) :
    FinalHandoff.StrictTemporalLineage (raw (protocol m)) m.assignment ↔ POS04CompleteLineage.StrictTemporalLineage m :=
  POS04RawHandoff.lineage_iff m

theorem full_iff_af (m : RawLaneModel) :
    FinalHandoff.PostWithdrawalFullAutonomy (raw (protocol m)) m.assignment ↔ AF m :=
  POS04NominalHandoff.full_iff_af m

theorem operational_iff_ao (m : RawLaneModel) :
    FinalHandoff.PostWithdrawalOperationalAutonomy (raw (protocol m)) m.assignment ↔ AO m :=
  POS04NominalHandoff.operational_iff_ao m

theorem scope_of_lineage (m : RawLaneModel)
    (hl : OwningHandoff.StrictTemporalLineage (POS04RawHandoff.raw (protocol m)) m.assignment) :
    FinalHandoff.ScopeCheck (raw (protocol m)) m.assignment :=
  ⟨OwningHandoff.route_status _ _ hl,rfl⟩

theorem full_gate_iff_nominal (m : RawLaneModel) :
    FinalHandoff.HandoffPass_F (raw (protocol m)) m.assignment ↔
      NominalHandoff.HandoffPass_F (POS04RawHandoff.raw (protocol m)) (POS04NominalHandoff.instructions (protocol m)) m.assignment := by
  constructor
  · exact And.left
  · intro h
    have hl := (OwningHandoff.temporalFIACHCertificateSoundness_generic_F _ _ h.2.2).2.1
    refine ⟨h,?_,scope_of_lineage m hl⟩
    dsimp only [raw]
    rw [POS04RawHandoff.target_eq]
    exact POS04ReceiverGate.checked_of_package_lineage m h.2.2.2.2.1 hl

theorem operational_gate_iff_nominal (m : RawLaneModel) :
    FinalHandoff.HandoffPass_O (raw (protocol m)) m.assignment ↔
      NominalHandoff.HandoffPass_O (POS04RawHandoff.raw (protocol m)) (POS04NominalHandoff.instructions (protocol m)) m.assignment := by
  constructor
  · exact And.left
  · intro h
    have hl := (OwningHandoff.temporalFIACHCertificateSoundness_generic_O _ _ h.2.2).2.1
    refine ⟨h,?_,scope_of_lineage m hl⟩
    dsimp only [raw]
    rw [POS04RawHandoff.target_eq]
    exact POS04ReceiverGate.checked_of_package_lineage m h.2.2.2.2.1 hl

theorem positive_F : FinalHandoff.HandoffPass_F (raw (protocol baseline)) baseline.assignment := by
  apply (full_gate_iff_nominal _).mpr
  refine ⟨POS04NominalHandoff.laws _ _,?_,POS04RawHandoff.positive_F⟩
  exact (POS04NominalHandoff.protocol_iff _).mpr POS04ExactGames.positive_games.2.1

theorem positive_O : FinalHandoff.HandoffPass_O (raw (protocol baseline)) baseline.assignment := by
  apply (operational_gate_iff_nominal _).mpr
  refine ⟨POS04NominalHandoff.laws _ _,?_,POS04RawHandoff.positive_O⟩
  exact (POS04NominalHandoff.protocol_iff _).mpr POS04ExactGames.positive_games.2.1

theorem positive_receiver : FinalHandoff.ReceiverReadout (raw (protocol baseline)) baseline.assignment :=
  FinalHandoff.receiver_soundness_F _ _ positive_F

theorem O_control_vectors :
    (¬ FinalHandoff.IntegratedTargetRealization (raw (protocol packageDeletion)) packageDeletion.assignment ∧
      FinalHandoff.StrictTemporalLineage (raw (protocol packageDeletion)) packageDeletion.assignment ∧
      FinalHandoff.PostWithdrawalOperationalAutonomy (raw (protocol packageDeletion)) packageDeletion.assignment) ∧
    (FinalHandoff.IntegratedTargetRealization (raw (protocol lineageDeletion)) lineageDeletion.assignment ∧
      ¬ FinalHandoff.StrictTemporalLineage (raw (protocol lineageDeletion)) lineageDeletion.assignment ∧
      FinalHandoff.PostWithdrawalOperationalAutonomy (raw (protocol lineageDeletion)) lineageDeletion.assignment) ∧
    (FinalHandoff.IntegratedTargetRealization (raw (protocol withdrawalDeletion)) withdrawalDeletion.assignment ∧
      FinalHandoff.StrictTemporalLineage (raw (protocol withdrawalDeletion)) withdrawalDeletion.assignment ∧
      ¬ FinalHandoff.PostWithdrawalOperationalAutonomy (raw (protocol withdrawalDeletion)) withdrawalDeletion.assignment) := by
  simp only [package_iff,lineage_iff,operational_iff_ao]
  have controls := POS04CompleteLineage.O_control_vectors
  exact ⟨⟨controls.1.1,controls.1.2.1,controls.1.2.2.1⟩,
    ⟨controls.2.1.1,controls.2.1.2.1,controls.2.1.2.2.1⟩,
    ⟨controls.2.2.1,controls.2.2.2.1,fun h => controls.2.2.2.2 ⟨h,greatest8_viable _ _⟩⟩⟩

theorem F_control_vectors :
    (¬ FinalHandoff.IntegratedTargetRealization (raw (protocol packageDeletion)) packageDeletion.assignment ∧
      FinalHandoff.StrictTemporalLineage (raw (protocol packageDeletion)) packageDeletion.assignment ∧
      ¬ FinalHandoff.PostWithdrawalFullAutonomy (raw (protocol packageDeletion)) packageDeletion.assignment) ∧
    (FinalHandoff.IntegratedTargetRealization (raw (protocol lineageDeletion)) lineageDeletion.assignment ∧
      ¬ FinalHandoff.StrictTemporalLineage (raw (protocol lineageDeletion)) lineageDeletion.assignment ∧
      FinalHandoff.PostWithdrawalFullAutonomy (raw (protocol lineageDeletion)) lineageDeletion.assignment) ∧
    (FinalHandoff.IntegratedTargetRealization (raw (protocol withdrawalDeletion)) withdrawalDeletion.assignment ∧
      FinalHandoff.StrictTemporalLineage (raw (protocol withdrawalDeletion)) withdrawalDeletion.assignment ∧
      ¬ FinalHandoff.PostWithdrawalFullAutonomy (raw (protocol withdrawalDeletion)) withdrawalDeletion.assignment) := by
  simp only [package_iff,lineage_iff,full_iff_af]
  have controls := POS04CompleteLineage.F_control_vectors
  exact ⟨⟨controls.1.1,controls.1.2.1,package_deletion_not_AF⟩,
    ⟨controls.2.1.1,controls.2.1.2.1,controls.2.1.2.2.1⟩,
    ⟨controls.2.2.1,controls.2.2.2.1,withdrawal_deletion_not_AF⟩⟩

theorem temporalFIACH_three_lane_separation :
    (∃ m : Model, ∃ a, ¬ FinalHandoff.IntegratedTargetRealization m a ∧
      FinalHandoff.StrictTemporalLineage m a ∧ FinalHandoff.PostWithdrawalOperationalAutonomy m a) ∧
    (∃ m : Model, ∃ a, FinalHandoff.IntegratedTargetRealization m a ∧
      ¬ FinalHandoff.StrictTemporalLineage m a ∧ FinalHandoff.PostWithdrawalOperationalAutonomy m a) ∧
    (∃ m : Model, ∃ a, FinalHandoff.IntegratedTargetRealization m a ∧
      FinalHandoff.StrictTemporalLineage m a ∧ ¬ FinalHandoff.PostWithdrawalOperationalAutonomy m a) :=
  ⟨⟨raw (protocol packageDeletion),packageDeletion.assignment,O_control_vectors.1⟩,
    ⟨raw (protocol lineageDeletion),lineageDeletion.assignment,O_control_vectors.2.1⟩,
    ⟨raw (protocol withdrawalDeletion),withdrawalDeletion.assignment,O_control_vectors.2.2⟩⟩

def constant : Model :=
  {raw (protocol baseline) with receiver := ⟨POS04ReceiverContent.constant,POS04ReceiverIntervention.erase⟩}

theorem constant_other_readouts : FinalHandoff.IntegratedTargetRealization constant canonical ∧
    FinalHandoff.StrictTemporalLineage constant canonical ∧
    FinalHandoff.PostWithdrawalFullAutonomy constant canonical ∧
    FinalHandoff.PostWithdrawalOperationalAutonomy constant canonical :=
  ⟨POS04RawHandoff.positive_readouts.1,POS04RawHandoff.positive_readouts.2.1,
    POS04NominalHandoff.baseline_readouts.1,POS04NominalHandoff.baseline_readouts.2⟩

theorem constant_no_receiver_readout : ¬ FinalHandoff.ReceiverReadout constant canonical := by
  rintro ⟨hi,ht,faithful,_⟩
  simp only [constant,raw,POS04RawHandoff.target_eq,image_canonical] at hi ht faithful
  exact POS04ReceiverContent.constant_not_faithful (protocol baseline) faithful

theorem constant_no_handoff : ¬ FinalHandoff.HandoffPass_F constant canonical ∧ ¬ FinalHandoff.HandoffPass_O constant canonical :=
  FinalHandoff.receiver_failure_no_handoff _ _ constant_no_receiver_readout

end CSTTT.TargetTheory.GenericHandoff.POS04FinalHandoff
