import CSTTT.Targets.GenericHandoff.StagedCorridorSequence
import CSTTT.Targets.GenericHandoff.RawCorridorSequenceModels

/-! An actual changed primitive context is necessary at the raw corridor seam.
The correct final branch contains the generated prior-path residue; reusing
the middle branch directly refutes the constructed corridor readout. -/
namespace CSTTT.TargetTheory.GenericHandoff.StagedCorridorSequenceModels
open RegisterInterpreter CellReindex RawCorridorSequenceModels
def identity : TranslationLanguage Bool Bool Value Value where
  Instruction _ _ := Unit
  execute _ v := some v
def appendNames : List String := ["left-mix","left-exit"]
def append : TranslationLanguage Bool Bool Value Value where
  Instruction _ _ := Unit
  execute := fun {_ t} _ v => some (if t then {v with seeds := {v.seeds with history := fun h => v.seeds.history h ++ appendNames}} else v)
def first : Stage (Index := Unit) identity := fun _ k => some ⟨k,()⟩
def second : Stage (Index := Unit) append := fun _ k => some ⟨k,()⟩
def cover : RawCover Unit Bool := ⟨[()],fun _ => [false,true],fun _ _ => true⟩
def original : Assignment Bool Value := fun _ => some leftInput
def middle (a : Assignment Bool Value) := PackageEngine.global identity a first cover
def finalCells (a : Assignment Bool Value) := PackageEngine.global append (middle a) second cover
def span (a : Assignment Bool Value) := StagedAssignmentSpan.span identity append first second cover cover a
def requests := StagedCorridorSequence.requests (RawCorridorSequenceModels.request RawCorridorSequenceModels.left)
  (RawCorridorSequenceModels.request RawCorridorSequenceModels.right)
def reusedRequests : List (RawCorridorSequence.Request (Sum Bool Bool) (StagedAssignmentSpan.JointValue Value Value)) :=
  [CorridorCellReindex.request Sum.inl (fun _ x => x) (RawCorridorSequenceModels.request RawCorridorSequenceModels.left),
   CorridorCellReindex.request Sum.inl (fun _ x => x) (RawCorridorSequenceModels.request RawCorridorSequenceModels.right)]

theorem middle_equation (a : Assignment Bool Value) : middle a = a := by
  funext k
  cases k <;> simp [middle,PackageEngine.global,glued,firstCover,mappedLocal,first,cover,identity]
theorem final_equation (a : Assignment Bool Value) :
    finalCells a = fun k => (a k).map (fun v => if k then
      {v with seeds := {v.seeds with history := fun h => v.seeds.history h ++ appendNames}} else v) := by
  rw [finalCells,middle_equation]
  funext k
  cases k <;> simp [PackageEngine.global,glued,firstCover,mappedLocal,second,cover,append]
  cases a true <;> rfl
theorem actual_middle : middle original = original := middle_equation original
theorem actual_final : finalCells original = canonical := by
  rw [final_equation]
  funext k
  cases k <;> rfl
theorem positive : RawCorridorSequence.Readout (span original) requests := by
  apply StagedCorridorSequence.constructs identity append first second cover cover _ _ original
  · change RawCorridorSequence.Parent (RawCorridorSequenceModels.request RawCorridorSequenceModels.left) (middle original)
    rw [middle_equation]
    exact ⟨⟨ready false original rfl,leftInput,by change AcquisitionCorridor.read (raw false leftSource middleCarrier 0) original = _; rw [read_equation]; rfl,left_view_check⟩,by change () ∈ [()]; simp⟩
  · change RawCorridorSequence.Parent (RawCorridorSequenceModels.request RawCorridorSequenceModels.right) (finalCells original)
    rw [actual_final]
    exact right_parent
  · change (RawCorridorSequence.leg (RawCorridorSequenceModels.request RawCorridorSequenceModels.left) (middle original)).bind
      (fun l => (RawCorridorSequence.leg (RawCorridorSequenceModels.request RawCorridorSequenceModels.right) (finalCells original)).map
        (fun r => CSTTT.CorridorTheory.AtomicChain.AdjacentFrontierCheck l r)) = some true
    rw [actual_middle,actual_final]
    decide +kernel
  · change 17 ≠ 101
    decide +kernel

theorem reused_no_readout : ¬ RawCorridorSequence.Readout (span original) reusedRequests := by
  have hleft : RawCorridorSequence.leg (CorridorCellReindex.request Sum.inl (fun _ x => x)
      (RawCorridorSequenceModels.request RawCorridorSequenceModels.left)) (span original) =
      some (AcquisitionCorridor.leg RawCorridorSequenceModels.left leftInput ()) := by
    rw [CorridorCellReindex.request_leg]
    change RawCorridorSequence.leg _ (pullback Sum.inl (fun _ x => x)
      (StagedAssignmentSpan.span identity append first second cover cover original)) = _
    rw [StagedAssignmentSpan.middle_equation]
    rw [← actual_middle]
    rw [actual_middle]
    rw [left_leg_equation]
    rfl
  have hright : RawCorridorSequence.leg (CorridorCellReindex.request Sum.inl (fun _ x => x)
      (RawCorridorSequenceModels.request RawCorridorSequenceModels.right)) (span original) =
      some (AcquisitionCorridor.leg RawCorridorSequenceModels.right leftInput ()) := by
    rw [CorridorCellReindex.request_leg]
    change RawCorridorSequence.leg _ (pullback Sum.inl (fun _ x => x)
      (StagedAssignmentSpan.span identity append first second cover cover original)) = _
    rw [StagedAssignmentSpan.middle_equation,← actual_middle,actual_middle,right_leg_equation]
    rfl
  exact RawCorridorSequence.bad_first_seam_no_readout _ _ _ [] _ _ hleft hright (by decide +kernel)

end CSTTT.TargetTheory.GenericHandoff.StagedCorridorSequenceModels
