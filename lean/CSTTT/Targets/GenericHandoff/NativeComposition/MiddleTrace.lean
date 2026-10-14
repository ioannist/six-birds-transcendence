import CSTTT.Targets.GenericHandoff.NativeComposition.MiddleObservation
import CSTTT.Targets.GenericHandoff.NativeComposition.PublishedFactor

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
open RegisterInterpreter ModeExecution EpisodeMap CSTTT.TransportTheory

local instance : DecidableEq Observation := instDecidableEqTemporalSnapshotReadout

noncomputable def sourceFuture := RegisterFuture.future source nativeAssignment source_ready
noncomputable def targetFuture := RegisterFuture.future target nativeAssignment target_ready
noncomputable def translate (x : Frame.Registers) :=
  RegisterSubstitution.translate translation nativeAssignment map_ready x ()
abbrev image := mapSnapshotReadout maps

theorem image_eq_iff (x y : Observation) : image x=image y ↔ x=y :=
  ⟨fun h => maps_injective h,congrArg image⟩

theorem future_observation (x : Frame.Registers) (hx : SourceClosure x) :
    targetFuture.observe (translate x)=image (sourceFuture.observe x) :=
  (translated_observation x hx).symm
theorem future_weight (x : Frame.Registers) (hx : SourceClosure x) (a : Unit × Bool) (o : Factor) :
    targetFuture.weight (translate x) a o=sourceFuture.weight x a o :=
  translated_weight x hx a o
theorem future_next (x : Frame.Registers) (hx : SourceClosure x) (a : Unit × Bool) (o : Factor) :
    targetFuture.next (translate x) a o=translate (sourceFuture.next x a o) :=
  (translated_successor x hx a o).symm
theorem future_closure_next (x : Frame.Registers) (hx : SourceClosure x) (a : Unit × Bool) (o : Factor) :
    SourceClosure (sourceFuture.next x a o) := FutureClosure.step hx a o (factor_mem o)

/-- Exact transport of full eight-field trace probabilities, for all finite
words without a horizon bound, from every zero-weight-inclusive closure state.
The target trace is the injective +2 image of the actual source trace. -/
theorem all_word_trace_transport (x : Frame.Registers) (hx : SourceClosure x)
    (word : List (Unit × Bool)) (trace : List Observation) :
    fullFuture targetFuture (translate x) word (trace.map image)=
      fullFuture sourceFuture x word trace := by
  induction word generalizing x trace with
  | nil =>
    simp only [fullFuture,future_observation x hx]
    have hi : trace.map image=[image (sourceFuture.observe x)] ↔ trace=[sourceFuture.observe x] :=
      by simpa only [List.map_cons,List.map_nil] using
        (List.map_inj_right (l := trace) (l' := [sourceFuture.observe x]) (fun _ _ h => maps_injective h))
    simp only [hi]
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      simp only [List.map_cons,fullFuture,future_observation x hx,image_eq_iff]
      by_cases hf : first=sourceFuture.observe x
      · simp only [hf,ite_true]
        change (factors.map (fun o => targetFuture.weight (translate x) a o *
          fullFuture targetFuture (targetFuture.next (translate x) a o) rest (tail.map image))).sum =
          (factors.map (fun o => sourceFuture.weight x a o *
          fullFuture sourceFuture (sourceFuture.next x a o) rest tail)).sum
        apply congrArg List.sum
        apply List.map_congr_left
        intro o ho
        rw [future_weight x hx,future_next x hx,ih _ (future_closure_next x hx a o)]
      · simp only [hf,ite_false]

/-- Each interpreted retrospective future separately satisfies full-word
sufficiency. This proof is independent of the comparison theorem above. -/
theorem both_full_future_sufficient : FullFutureSufficient sourceFuture ∧ FullFutureSufficient targetFuture := by
  have ha : TemporalFactorRules.Accept (factorSchema true) (roundInput 1).temporal :=
    published_factor_accept false
  obtain ⟨hs,hfs⟩ := Frame.all_unbounded_words true false true firstNames (by intro x y he; cases x <;> cases y <;> simp_all [firstNames])
    (MemoryFrames.inputs false nativeAssignment) (roundInput 1) rfl ha
  obtain ⟨ht,hft⟩ := Frame.all_unbounded_words false false true secondNames (by intro x y he; cases x <;> cases y <;> simp_all [secondNames])
    (MemoryFrames.inputs true nativeAssignment) (roundInput 1) rfl ha
  have se := FutureCellReindex.future_equation (SV := Value) (TV := MemoryValue)
    id (fun (_ : Owner) (p : Input × Input) => MemoryFrames.selectInput false p)
    (Frame.raw true false true firstNames) nativeAssignment source_ready hs.2.1
  have te := FutureCellReindex.future_equation (SV := Value) (TV := MemoryValue)
    id (fun (_ : Owner) (p : Input × Input) => MemoryFrames.selectInput true p)
    (Frame.raw false false true secondNames) nativeAssignment target_ready ht.2.1
  constructor
  · change FullFutureSufficient (RegisterFuture.future source nativeAssignment source_ready)
    rw [se]
    exact hfs
  · change FullFutureSufficient (RegisterFuture.future target nativeAssignment target_ready)
    rw [te]
    exact hft

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
