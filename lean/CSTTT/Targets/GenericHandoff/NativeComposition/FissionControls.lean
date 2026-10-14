import CSTTT.Targets.GenericHandoff.NativeComposition.FissionSymmetry

/-! Native controls refute the actual readout. Credit and joint ablations
change primitive source instructions before running publication. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
open RegisterInterpreter PublicationReplay CSTTT.TransportTheory

def cutRaw (branch : Bool) : Raw :=
  ⟨canonicalRaw.initial,fun b => decide (b=branch)⟩
theorem cut_raw_no_readout (branch : Bool) : ¬Readout (cutRaw branch) :=
  cut_current_no_readout _ branch (by simp [cutRaw])
theorem cut_raw_whole_source (branch cell : Bool) :
    (assignment (cutRaw branch) branch cell).map Prod.snd=(assignment canonicalRaw branch cell).map Prod.snd :=
  whole_copied_source_preserved _ _ _

def missingRaw (branch : Bool) : Raw :=
  ⟨fun b o => if b=branch ∧ o=false then none else canonicalRaw.initial b o,fun _ => false⟩
theorem missing_raw_no_readout (branch : Bool) : ¬Readout (missingRaw branch) :=
  missing_no_readout _ branch (by simp [missingRaw])
theorem missing_raw_decoded (branch : Bool) : decoded (missingRaw branch)=none := by
  unfold decoded
  have hc : consumed (missingRaw branch)=false := by cases branch <;> rfl
  rw [hc]
  rfl

def brokenCreditRaw : Raw :=
  ⟨fun _ => NativeClosedPackage.mapCurrent NativeCreditCells.cutSelfEdges false NativePackageBundle.initial,
    fun _ => false⟩
theorem broken_credit_decoded :
    ProtocolCreditRules.decoded (NativeCreditCells.bindings true false) (assignment brokenCreditRaw false)=
      some (NativeCreditCells.data (NativeCreditCells.cutSelfEdges
        ⟨AvailabilityPublication.selected true false,NativePackagePrimitives.supplement⟩)) := by
  unfold assignment brokenCreditRaw
  rw [PublicationMaps.exposure_equation]
  rfl
theorem broken_credit_no_readout : ¬Readout brokenCreditRaw := by
  rintro ⟨_,hc,_⟩
  obtain ⟨_,hp,_⟩ := (hc false).parent
  obtain ⟨d,hd,ha⟩ := hp true false .c5
  rw [broken_credit_decoded] at hd
  have he := Option.some.inj hd
  subst d
  exact NativeCreditCells.cut_actual_c5_rejected _ _ ha

def brokenJointRaw : Raw :=
  ⟨fun _ => NativeClosedPackage.mapCurrent NativeJointCells.eraseObservable false NativePackageBundle.initial,
    fun _ => false⟩
theorem broken_joint_decoded :
    JointRules.decoded (NativeJointCells.bindings true false) (assignment brokenJointRaw false)=
      some (NativeJointCells.data (NativeJointCells.eraseObservable
        ⟨AvailabilityPublication.selected true false,NativePackagePrimitives.supplement⟩)) := by
  unfold assignment brokenJointRaw
  rw [PublicationMaps.exposure_equation]
  rfl
theorem broken_joint_no_readout : ¬Readout brokenJointRaw := by
  rintro ⟨_,hc,_⟩
  obtain ⟨_,hp,_⟩ := (hc false).parent
  obtain ⟨d,hd,ha⟩ := hp true false .c7
  rw [broken_joint_decoded] at hd
  have he := Option.some.inj hd
  subst d
  exact NativeJointCells.erased_actual_c7_rejected _ ha

theorem broken_credit_no_continuation (source target : CarrierId) : ¬Continuation brokenCreditRaw source target := by
  intro h
  exact broken_credit_no_readout ((continuation_iff _ _ _).mp h).2.1
theorem broken_joint_no_continuation (source target : CarrierId) : ¬Continuation brokenJointRaw source target := by
  intro h
  exact broken_joint_no_readout ((continuation_iff _ _ _).mp h).2.1
theorem source_cut_no_continuation (branch : Bool) (source target : CarrierId) : ¬Continuation (cutRaw branch) source target := by
  intro h
  exact cut_raw_no_readout branch ((continuation_iff _ _ _).mp h).2.1
theorem missing_no_continuation (branch : Bool) (source target : CarrierId) : ¬Continuation (missingRaw branch) source target := by
  intro h
  exact missing_raw_no_readout branch ((continuation_iff _ _ _).mp h).2.1

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
