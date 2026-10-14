import CSTTT.Targets.GenericHandoff.CorridorCellReindex

/-! Two heterogeneous raw corridor requests read the two actual stage globals.
Every leg/seam equation is exact on partial assignments. Parent corridor gates,
complete decoded adjacency and raw outer carrier inequality derive the chain. -/
namespace CSTTT.TargetTheory.GenericHandoff.StagedCorridorSequence
open RegisterInterpreter CellReindex
variable {SC MC TC LI RI : Type} {SV : SC → Type} {MV : MC → Type} {TV : TC → Type}
  [DecidableEq MC] [DecidableEq TC]
variable (left : TranslationLanguage SC MC SV MV) (right : TranslationLanguage MC TC MV TV)
  (first : Stage (Index := LI) left) (second : Stage (Index := RI) right)
  (middleCover : RawCover LI MC) (targetCover : RawCover RI TC)

def requests (q : RawCorridorSequence.Request MC MV) (r : RawCorridorSequence.Request TC TV) :
    List (RawCorridorSequence.Request (Sum MC TC) (StagedAssignmentSpan.JointValue MV TV)) :=
  [CorridorCellReindex.request Sum.inl (fun _ x => x) q,
   CorridorCellReindex.request Sum.inr (fun _ x => x) r]

theorem middle_leg (q : RawCorridorSequence.Request MC MV) (a : Assignment SC SV) :
    RawCorridorSequence.leg (CorridorCellReindex.request Sum.inl (fun _ x => x) q)
      (StagedAssignmentSpan.span left right first second middleCover targetCover a) =
      RawCorridorSequence.leg q (PackageEngine.global left a first middleCover) := by
  rw [CorridorCellReindex.request_leg,StagedAssignmentSpan.middle_equation]
theorem final_leg (r : RawCorridorSequence.Request TC TV) (a : Assignment SC SV) :
    RawCorridorSequence.leg (CorridorCellReindex.request Sum.inr (fun _ x => x) r)
      (StagedAssignmentSpan.span left right first second middleCover targetCover a) =
      RawCorridorSequence.leg r (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover) := by
  rw [CorridorCellReindex.request_leg,StagedAssignmentSpan.final_equation]

theorem chain_equation (q : RawCorridorSequence.Request MC MV) (r : RawCorridorSequence.Request TC TV)
    (a : Assignment SC SV) :
    RawCorridorSequence.chain (StagedAssignmentSpan.span left right first second middleCover targetCover a) (requests q r) =
      (RawCorridorSequence.leg q (PackageEngine.global left a first middleCover)).bind (fun l =>
        (RawCorridorSequence.leg r (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover)).map
          (fun last => [l,last])) := by
  simp only [requests,RawCorridorSequence.chain,middle_leg,final_leg]
  cases RawCorridorSequence.leg q (PackageEngine.global left a first middleCover) <;>
    cases RawCorridorSequence.leg r (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover) <;> simp

theorem seam_equation (q : RawCorridorSequence.Request MC MV) (r : RawCorridorSequence.Request TC TV)
    (a : Assignment SC SV) :
    RawCorridorSequence.seams (StagedAssignmentSpan.span left right first second middleCover targetCover a) (requests q r) =
      (RawCorridorSequence.leg q (PackageEngine.global left a first middleCover)).bind (fun l =>
        (RawCorridorSequence.leg r (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover)).map
          (fun last => CSTTT.CorridorTheory.AtomicChain.AdjacentFrontierCheck l last)) := by
  simp only [requests,RawCorridorSequence.seams,RawCorridorSequence.seam,middle_leg,final_leg]
  cases RawCorridorSequence.leg q (PackageEngine.global left a first middleCover) <;>
    cases RawCorridorSequence.leg r (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover) <;> simp

theorem middle_parent_iff (q : RawCorridorSequence.Request MC MV) (a : Assignment SC SV) :
    RawCorridorSequence.Parent (CorridorCellReindex.request Sum.inl (fun _ x => x) q)
      (StagedAssignmentSpan.span left right first second middleCover targetCover a) ↔
      RawCorridorSequence.Parent q (PackageEngine.global left a first middleCover) := by
  rw [CorridorCellReindex.request_parent_iff,StagedAssignmentSpan.middle_equation]
theorem final_parent_iff (r : RawCorridorSequence.Request TC TV) (a : Assignment SC SV) :
    RawCorridorSequence.Parent (CorridorCellReindex.request Sum.inr (fun _ x => x) r)
      (StagedAssignmentSpan.span left right first second middleCover targetCover a) ↔
      RawCorridorSequence.Parent r
        (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover) := by
  rw [CorridorCellReindex.request_parent_iff,StagedAssignmentSpan.final_equation]

theorem constructs (q : RawCorridorSequence.Request MC MV) (r : RawCorridorSequence.Request TC TV)
    (a : Assignment SC SV)
    (hq : RawCorridorSequence.Parent q (PackageEngine.global left a first middleCover))
    (hr : RawCorridorSequence.Parent r
      (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover))
    (hj : (RawCorridorSequence.leg q (PackageEngine.global left a first middleCover)).bind (fun l =>
      (RawCorridorSequence.leg r (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover)).map
        (fun last => CSTTT.CorridorTheory.AtomicChain.AdjacentFrontierCheck l last)) = some true)
    (hd : RawCorridorSequence.source q ≠ RawCorridorSequence.target r) :
    RawCorridorSequence.Readout (StagedAssignmentSpan.span left right first second middleCover targetCover a) (requests q r) := by
  apply RawCorridorSequence.constructs
  refine ⟨by simp [requests],?_,?_,?_⟩
  · intro x hx
    simp only [requests,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with he | he
    · subst x
      exact (middle_parent_iff left right first second middleCover targetCover q a).mpr hq
    · subst x
      exact (final_parent_iff left right first second middleCover targetCover r a).mpr hr
  · rw [seam_equation]
    exact hj
  · change some (RawCorridorSequence.source q) ≠ some (RawCorridorSequence.target r)
    exact fun he => hd (Option.some.inj he)

end CSTTT.TargetTheory.GenericHandoff.StagedCorridorSequence
