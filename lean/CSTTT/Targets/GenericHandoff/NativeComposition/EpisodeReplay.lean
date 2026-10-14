import CSTTT.Targets.GenericHandoff.NativeComposition.EpisodeMap

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.EpisodeMap
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence ModeExecution

abbrev arrived (x : Frame.State) := received (episodePair 0) false (stepState x x.factor,false)

/-- Select replay by the actual current factor, while preserving the actual
incoming residue. This is NOT Arrival away from the independent initializer. -/
theorem from_start_actual (hf : Ready firstAcquisition nativeAssignment)
    (x : Frame.State) (hx : x.funded=true) :
    fromStart firstAcquisition nativeAssignment hf (ModeExecution.pack (x,false)) x.factor =
      some (ModeExecution.pack (arrived x)) := by
  have hr := native_routes true false 0 1 0 nativeAssignment rfl
  have hh : firstAcquisition.histories.read nativeAssignment=some (fun h => [((),false,h)]) := rfl
  have hc := episode_step_check true false 0 1 nativeAssignment 0 rfl (ModeExecution.pack (x,false)) hx
  change stepCheck firstAcquisition nativeAssignment (ModeExecution.pack (x,false)) () false x.factor=true at hc
  have hu := episode_update true false 0 1 nativeAssignment hf 0 rfl (ModeExecution.pack (x,false)) () false x.factor
  simp only [fromStart,hr,hh,bind,Option.bind_some,supportedFold,hc,ite_true,hu]
  rw [acquisition_receive true false 0 1 nativeAssignment hf (episodePair 0) rfl]
  rfl

theorem arrived_funded (x : Frame.State) (hx : x.funded=true) : (arrived x).1.funded=true := by
  simp [received,stepState,hx,episodePair,roundInput,publish,canonicalInput,factorData]

theorem program_as_actual_steps (x : Frame.State) : program (episodePair 0) x = stepState (arrived x).1 x.factor := by
  have hw : assignedWord (episodePair 0) x.factor=[((),false,x.factor)] := rfl
  simp only [program,sourceFold]
  rw [hw]
  simp only [List.foldl_cons,List.foldl_nil,episodePair,round_update]
  rfl

theorem interpreted_episode (hf : Ready firstAcquisition nativeAssignment)
    (x : Frame.State) (hx : x.funded=true) :
    postExit firstAcquisition nativeAssignment hf x.factor x.factor
      (fromStart firstAcquisition nativeAssignment hf (ModeExecution.pack (x,false)) x.factor) =
      some (ModeExecution.pack (program (episodePair 0) x,true)) := by
  have hr := native_routes true false 0 1 0 nativeAssignment rfl
  rw [from_start_actual hf x hx]
  simp only [postExit,hr,bind,Option.bind_some]
  change (some ((),false)).bind (fun da => if stepCheck firstAcquisition nativeAssignment
    (ModeExecution.pack (arrived x)) da.1 da.2 x.factor then
      some (update firstAcquisition nativeAssignment hf (ModeExecution.pack (arrived x)) da.1 da.2 x.factor) else none) = _
  have hc := episode_step_check true false 0 1 nativeAssignment 0 rfl (ModeExecution.pack (arrived x)) (arrived_funded x hx)
  change stepCheck firstAcquisition nativeAssignment (ModeExecution.pack (arrived x)) () false x.factor=true at hc
  have hu := episode_update true false 0 1 nativeAssignment hf 0 rfl (ModeExecution.pack (arrived x)) () false x.factor
  simp only [Option.bind_some,hc,ite_true,hu,program_as_actual_steps]
  rfl

/-- The middle raw translation is bound to interpreted supported replay on
funded inputs; both the dynamic replay selector and retained past are explicit. -/
theorem translation_from_interpreted_episode (hf : Ready firstAcquisition nativeAssignment)
    (h : RegisterSubstitution.Ready translation nativeAssignment)
    (x : Frame.Registers) (hx : (x ()).funded=true) :
    postExit firstAcquisition nativeAssignment hf (x ()).factor (x ()).factor
      (fromStart firstAcquisition nativeAssignment hf
        (ModeExecution.pack (halfPast (x ()),false)) (x ()).factor) =
      some (ModeExecution.pack
        (RegisterSubstitution.translate translation nativeAssignment h x () (),true)) := by
  rw [native_translation]
  exact interpreted_episode hf (halfPast (x ())) hx

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.EpisodeMap
