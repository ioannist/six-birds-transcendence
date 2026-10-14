import CSTTT.Targets.GenericHandoff.NativeComposition.MiddleTrace

/-! The whole-closure replay is genuinely initialized acquisition at roots.
This strengthens root attribution without claiming Arrival off the roots. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence ModeExecution EpisodeMap

theorem half_root_is_actual_initializer (h : Factor) :
    ModeExecution.pack (halfPast (sourceRoot h ()),false)=
      initial firstAcquisition nativeAssignment native_first_ready h := by
  rw [source_root,first_initializer]
  funext r
  cases r
  simp [halfPast,Frame.pack,middleState,snapshot,ModeExecution.pack]

theorem root_translation_from_actual_entry (h : Factor) :
    firstEntry firstAcquisition nativeAssignment native_first_ready h h=
      some (ModeExecution.pack (translate (sourceRoot h) (),true)) := by
  have he := translation_is_supported_episode (sourceRoot h)
    (CSTTT.TransportTheory.FutureClosure.root _ (List.mem_map.mpr ⟨h,factor_mem h,rfl⟩))
  rw [half_root_is_actual_initializer,source_root] at he
  change postExit firstAcquisition nativeAssignment native_first_ready h h
    (fromStart firstAcquisition nativeAssignment native_first_ready
      (initial firstAcquisition nativeAssignment native_first_ready h) h)=_ at he
  have hr := native_routes true false 0 1 0 nativeAssignment rfl
  simpa only [firstEntry,firstArrival,hr,bind,Option.bind_some,translate,source_root] using he

theorem root_translation_is_actual_semantic_entry (h : Factor) :
    Entry firstSchema firstAcquisition nativeAssignment native_first_ready
      (ModeExecution.pack (translate (sourceRoot h) (),true)) := by
  have he := Option.some.inj ((first_entry native_first_ready h).symm.trans
    (root_translation_from_actual_entry h))
  rw [← he]
  exact first_semantic_entry native_first_ready h

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
