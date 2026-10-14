import CSTTT.Targets.GenericHandoff.RawCorridorSequenceModels

/-! Kernel obstruction to compressing a physical three-carrier chain into
the existing single-leg two-endpoint support projection. Preserve the chain. -/
namespace CSTTT.TargetTheory.GenericHandoff.AcquisitionSupportRange
open RegisterInterpreter
variable {Cell R D A O Stage Id History RouteId : Type} {Value : Cell → Type} {RV : R → Type}
  [DecidableEq Stage]

theorem endpoints_only
    (raw : AcquisitionCorridor.Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : AcquisitionCorridor.View Stage Id History RouteId) (rid : RouteId) (i : Nat) (s : Stage) (owner : Nat) :
    owner ∈ AcquisitionCorridor.support raw v rid i s →
      owner = raw.schema.source.code ∨ owner = raw.schema.target.code := by
  unfold AcquisitionCorridor.support
  split
  · intro h; exact Or.inl (List.mem_singleton.mp h)
  · dsimp only
    intro h
    rcases List.mem_append.mp h with h | h
    · left
      split at h
      · exact List.mem_singleton.mp h
      · simp at h
    · right
      split at h
      · exact List.mem_singleton.mp h
      · simp at h

theorem middle_absent
    (raw : AcquisitionCorridor.Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : AcquisitionCorridor.View Stage Id History RouteId) (rid : RouteId) (i : Nat) (s : Stage) (owner : Nat)
    (hs : owner ≠ raw.schema.source.code) (ht : owner ≠ raw.schema.target.code) :
    owner ∉ AcquisitionCorridor.support raw v rid i s := by
  intro h
  exact (endpoints_only raw v rid i s owner h).elim hs ht

theorem stage_middle_absent
    (raw : AcquisitionCorridor.Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : AcquisitionCorridor.View Stage Id History RouteId) (rid : RouteId)
    (stage : CSTTT.CorridorTheory.AtomicChain.RawStage) (hstage : stage ∈ AcquisitionCorridor.stages raw v rid)
    (owner : Nat) (hs : owner ≠ raw.schema.source.code) (ht : owner ≠ raw.schema.target.code) :
    owner ∉ stage.support := by
  obtain ⟨i,hi,he⟩ := List.mem_mapIdx.mp hstage
  rw [← he]
  exact middle_absent raw v rid i _ owner hs ht

theorem no_single_outer_representation
    (raw : AcquisitionCorridor.Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : AcquisitionCorridor.View Stage Id History RouteId) (rid : RouteId)
    (hs : raw.schema.source.code = 17) (ht : raw.schema.target.code = 101) :
    AcquisitionCorridor.stages raw v rid ≠
      CSTTT.CorridorTheory.AtomicChain.chainStages RawCorridorSequenceModels.actualLegs := by
  intro he
  obtain ⟨s,hmem,howner⟩ := RawCorridorSequenceModels.actual_middle_support
  rw [← he] at hmem
  exact stage_middle_absent raw v rid s hmem 55 (by omega) (by omega) howner

end CSTTT.TargetTheory.GenericHandoff.AcquisitionSupportRange
