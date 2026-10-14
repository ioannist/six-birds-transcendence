import CSTTT.Corridor.RawDirectControl
import CSTTT.Corridor.RawDirectSeparation
import CSTTT.Corridor.RawDirectValidity
import CSTTT.Corridor.GlobalTokenUse
import CSTTT.Corridor.RawEventPaths
import CSTTT.Corridor.ModelBoundPath
import CSTTT.Strengthening.ContinuityClass
import CSTTT.Targets.RawDirectSuccessorControls

/-! Kernel returns for the separately committed evaluation packet14a0283.
All declarations are new(b). Every finite verdict is recomputed by the kernel
from actual raw tables. Computation artifacts supply no proof assumptions. -/
namespace CSTTT.TargetTheory.RawDirectSuccessorReturn
open CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor
open CSTTT.CorridorTheory.RawDirectControl CSTTT.CorridorTheory.RawDirectSeparation
open CSTTT.TargetTheory.RawDirectSuccessorControls

theorem dsPos01_direct : DirectMode dsPos01 :=
  (control_readout_iff dsPos01).mpr (by decide)

theorem dsPos02A_direct : DirectMode dsPos02A :=
  (control_readout_iff dsPos02A).mpr (by decide)

theorem dsPos02B_direct : DirectMode dsPos02B :=
  (control_readout_iff dsPos02B).mpr (by decide)

theorem gapPrimitive_not_direct : ¬ DirectMode gapPrimitive := by
  intro direct
  have checked := (control_readout_iff gapPrimitive).mp direct
  have rejected : controlCheck gapPrimitive=false := by decide
  rw [rejected] at checked
  contradiction

theorem alternative_not_direct : ¬ DirectMode alternative := by
  intro direct
  have checked := (control_readout_iff alternative).mp direct
  have rejected : controlCheck alternative=false := by decide
  rw [rejected] at checked
  contradiction

theorem store_not_direct : ¬ DirectMode store := by
  intro direct
  have checked := (control_readout_iff store).mp direct
  have rejected : controlCheck store=false := by decide
  rw [rejected] at checked
  contradiction

theorem directOnly_direct : DirectMode directOnly :=
  (control_readout_iff directOnly).mpr (by decide)

theorem dataOnly_not_direct : ¬ DirectMode dataOnly := by
  intro direct
  have checked := (control_readout_iff dataOnly).mp direct
  have rejected : controlCheck dataOnly=false := by decide
  rw [rejected] at checked
  contradiction

theorem directWithData_direct : DirectMode directWithData :=
  (control_readout_iff directWithData).mpr (by decide)

theorem detached_not_direct : ¬ DirectMode detached := by
  intro direct
  have checked := (control_readout_iff detached).mp direct
  have rejected : controlCheck detached=false := by decide
  rw [rejected] at checked
  contradiction

theorem archive_not_direct : ¬ DirectMode archive := by
  intro direct
  have checked := (control_readout_iff archive).mp direct
  have rejected : controlCheck archive=false := by decide
  rw [rejected] at checked
  contradiction

theorem missingSource_not_direct : ¬ DirectMode missingSource := by
  intro direct
  have checked := (control_readout_iff missingSource).mp direct
  have rejected : controlCheck missingSource=false := by decide
  rw [rejected] at checked
  contradiction

theorem missingPayload_not_direct : ¬ DirectMode missingPayload := by
  intro direct
  have checked := (control_readout_iff missingPayload).mp direct
  have rejected : controlCheck missingPayload=false := by decide
  rw [rejected] at checked
  contradiction

theorem missingToken_not_direct : ¬ DirectMode missingToken := by
  intro direct
  have checked := (control_readout_iff missingToken).mp direct
  have rejected : controlCheck missingToken=false := by decide
  rw [rejected] at checked
  contradiction

theorem usedToken_not_direct : ¬ DirectMode usedToken := by
  intro direct
  have checked := (control_readout_iff usedToken).mp direct
  have rejected : controlCheck usedToken=false := by decide
  rw [rejected] at checked
  contradiction

theorem sourceAbsent_not_direct : ¬ DirectMode sourceAbsent := by
  intro direct
  have checked := (control_readout_iff sourceAbsent).mp direct
  have rejected : controlCheck sourceAbsent=false := by decide
  rw [rejected] at checked
  contradiction

theorem payloadDrift_not_direct : ¬ DirectMode payloadDrift := by
  intro direct
  have checked := (control_readout_iff payloadDrift).mp direct
  have rejected : controlCheck payloadDrift=false := by decide
  rw [rejected] at checked
  contradiction

theorem duplicateEvent_not_direct : ¬ DirectMode duplicateEvent := by
  intro direct
  have checked := (control_readout_iff duplicateEvent).mp direct
  have rejected : controlCheck duplicateEvent=false := by decide
  rw [rejected] at checked
  contradiction

theorem gap_not_direct : ¬ DirectMode gap := by
  intro direct
  have checked := (control_readout_iff gap).mp direct
  have rejected : controlCheck gap=false := by decide
  rw [rejected] at checked
  contradiction

theorem alternativeParent_not_direct : ¬ DirectMode alternativeParent := by
  intro direct
  have checked := (control_readout_iff alternativeParent).mp direct
  have rejected : controlCheck alternativeParent=false := by decide
  rw [rejected] at checked
  contradiction

theorem storage_not_direct : ¬ DirectMode storage := by
  intro direct
  have checked := (control_readout_iff storage).mp direct
  have rejected : controlCheck storage=false := by decide
  rw [rejected] at checked
  contradiction

theorem overlapOnly_not_direct : ¬ DirectMode overlapOnly := by
  intro direct
  have checked := (control_readout_iff overlapOnly).mp direct
  have rejected : controlCheck overlapOnly=false := by decide
  rw [rejected] at checked
  contradiction

theorem mixedDirect_direct : DirectMode mixedDirect :=
  (control_readout_iff mixedDirect).mpr (by decide)

theorem overlapOnly_overlap : OverlapMode overlapOnly := by
  change AtomicLegCheck overlapOnly.episode=true
  decide

theorem directOnly_not_overlap : ¬ OverlapMode directOnly :=
  direct_not_overlap directOnly directOnly_direct

/-- Whole inputs and payloads are extracted with checked presence proofs;
no absent input receives a default value. -/
def dataOnlyInput : SourceEvent :=
  (dataOnly.input dataOnly.episode.sourceAudit).get (by decide)
def dataOnlyPayload : Frontier := dataOnlyInput.payload.get (by decide)
def coexistInput : SourceEvent :=
  (directWithData.input directWithData.episode.sourceAudit).get (by decide)
def coexistPayload : Frontier := coexistInput.payload.get (by decide)

theorem dataOnly_data : DataReachable dataOnly := by
  refine ⟨dataOnlyInput,dataOnlyPayload,rfl,rfl,?_⟩
  exact .one ⟨dataOnly.episode.sourceAudit,dataOnly.episode.targetAudit,dataOnlyPayload⟩
    (by decide) rfl

theorem directWithData_data : DataReachable directWithData := by
  refine ⟨coexistInput,coexistPayload,rfl,rfl,?_⟩
  exact .one ⟨directWithData.episode.sourceAudit,directWithData.episode.targetAudit,coexistPayload⟩
    (by decide) rfl

/-- The original literal data-exclusion reading is false in the exact shared
raw domain. Both witnesses are kernel theorems, not evaluated verdict flags. -/
theorem literal_data_exclusion_false :
    ¬ (∀ m : ControlModel, DirectMode m → ¬ DataReachable m) := by
  intro excludes
  exact excludes directWithData directWithData_direct directWithData_data

theorem data_reachability_does_not_license_direct :
    ¬ (∀ m : ControlModel, DataReachable m → DirectMode m) := by
  intro licenses
  exact dataOnly_not_direct (licenses dataOnly dataOnly_data)

theorem actual_modes_incomparable :
    CSTTT.StrengtheningTheory.EvidenceModesIncomparable OverlapMode DirectMode := by
  exact ⟨⟨overlapOnly,overlapOnly_overlap,overlapOnly_not_direct⟩,
    ⟨directOnly,directOnly_direct,directOnly_not_overlap⟩⟩

theorem actual_generalized_broader_than_overlap :
    (∀ m : ControlModel, OverlapMode m → GeneralizedMode m) ∧
    (∃ m : ControlModel, GeneralizedMode m ∧ ¬ OverlapMode m) := by
  exact ⟨overlap_embedding,⟨directOnly,direct_embedding directOnly directOnly_direct,
    directOnly_not_overlap⟩⟩

/-- Every legacy certificate field is supplied by actual raw computations.
The certificate adapter's immediateEdge field is the imported actual readout;
this return is not a new independent definition of directness. -/
theorem actual_validity_return (m : ControlModel) (direct : DirectMode m) :
    ∃ raw b, directProjection m=some (raw,b) ∧
      Nonempty (CSTTT.DirectSuccessorTheory.AtomicDirectSuccessorCertificate
        (CSTTT.CorridorTheory.RawDirectValidity.data raw b m.input)) := by
  obtain ⟨raw,b,projection,readout⟩ := direct
  exact ⟨raw,b,projection,
    ⟨CSTTT.CorridorTheory.RawDirectValidity.raw_constructs_old_certificate raw b m.input readout⟩⟩

theorem actual_frozen_validity (m : ControlModel) (direct : DirectMode m) :
    ¬ BadOperationalPattern m ∧
    ∃ raw b, directProjection m=some (raw,b) ∧
      Nonempty (CSTTT.DirectSuccessorTheory.AtomicDirectSuccessorCertificate
        (CSTTT.CorridorTheory.RawDirectValidity.data raw b m.input)) :=
  ⟨control_excludes_patterns m direct,actual_validity_return m direct⟩

theorem actual_mediator_free_validity (m : ControlModel) (direct : DirectMode m) :
    ¬ BadOperationalPattern m ∧
    (∀ n : Nat, 2≤n → ¬ CSTTT.CorridorTheory.RawEventPaths.EventPath
      m.episode.dependencies n m.episode.sourceAudit m.episode.targetAudit) ∧
    ∃ raw b, directProjection m=some (raw,b) ∧
      Nonempty (CSTTT.DirectSuccessorTheory.AtomicDirectSuccessorCertificate
        (CSTTT.CorridorTheory.RawDirectValidity.data raw b m.input)) :=
  ⟨control_excludes_patterns m direct,
    CSTTT.CorridorTheory.RawEventPaths.direct_excludes_every_mediated_generation_path m direct,
    actual_validity_return m direct⟩

theorem actual_validity_nonempty :
    ∃ m : ControlModel, DirectMode m ∧ ¬ BadOperationalPattern m ∧
      ∃ raw b, directProjection m=some (raw,b) ∧
        Nonempty (CSTTT.DirectSuccessorTheory.AtomicDirectSuccessorCertificate
          (CSTTT.CorridorTheory.RawDirectValidity.data raw b m.input)) :=
  ⟨dsPos01,dsPos01_direct,actual_frozen_validity dsPos01 dsPos01_direct⟩

theorem dataOnly_not_overlap : ¬ OverlapMode dataOnly := by
  intro overlap
  change AtomicLegCheck dataOnly.episode=true at overlap
  have rejected : AtomicLegCheck dataOnly.episode=false := by decide
  rw [rejected] at overlap
  contradiction

/-- Positive data carriage cannot provide an operational generalized leg or
path on the declared data-only model, even though unrelated models may use the
same endpoint carrier names. This uses the exact model sequence index. -/
theorem dataOnly_no_model_path (source target : Signature) :
    ¬ Nonempty (CSTTT.CorridorTheory.ModelBoundPath.ModelPath [dataOnly] source target) := by
  rintro ⟨path⟩
  rcases CSTTT.CorridorTheory.ModelBoundPath.every_model_actual path dataOnly (by simp) with
    overlap | direct
  · exact dataOnly_not_overlap overlap
  · exact dataOnly_not_direct direct

end CSTTT.TargetTheory.RawDirectSuccessorReturn
