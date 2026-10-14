import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationObservation

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationFuture
open RegisterInterpreter CSTTT.TransportTheory PublicationReplay
local instance : DecidableEq Observation := instDecidableEqTemporalSnapshotReadout

noncomputable def sourceFuture (cell : Owner) :=
  RegisterFuture.future (source cell) NativePackageBundle.canonical (frameReady cell true)
noncomputable def targetFuture (cell : Owner) :=
  RegisterFuture.future (target cell) NativePackageBundle.canonical (frameReady cell false)

theorem image_eq_iff (cell : Owner) (x y : Observation) : image cell x=image cell y ↔ x=y :=
  ⟨fun h => image_injective cell h,congrArg (image cell)⟩
theorem future_observation (cell : Owner) (x : Frame.Registers) (hx : SourceClosure cell x) :
    (targetFuture cell).observe (translate cell x)=image cell ((sourceFuture cell).observe x) :=
  translated_observation cell x hx
theorem future_weight (cell : Owner) (x : Frame.Registers) (a : Unit × Bool) (o : Factor) :
    (targetFuture cell).weight (translate cell x) a o=(sourceFuture cell).weight x a o :=
  translated_weight cell x a o
theorem future_next (cell : Owner) (x : Frame.Registers) (a : Unit × Bool) (o : Factor) :
    (targetFuture cell).next (translate cell x) a o=translate cell ((sourceFuture cell).next x a o) :=
  (translated_successor cell x a o).symm
theorem future_closure_next (cell : Owner) (x : Frame.Registers) (hx : SourceClosure cell x) (a : Unit × Bool) (o : Factor) :
    SourceClosure cell ((sourceFuture cell).next x a o) := FutureClosure.step hx a o (factor_mem o)

/-- All finite words and complete eight-field traces, from every source closure
state. There is no horizon limit and the induction includes all eight outcomes. -/
theorem all_word_trace_transport (cell : Owner) (x : Frame.Registers) (hx : SourceClosure cell x)
    (word : List (Unit × Bool)) (trace : List Observation) :
    fullFuture (targetFuture cell) (translate cell x) word (trace.map (image cell))=
      fullFuture (sourceFuture cell) x word trace := by
  induction word generalizing x trace with
  | nil =>
    simp only [fullFuture,future_observation cell x hx]
    have hi : trace.map (image cell)=[image cell ((sourceFuture cell).observe x)] ↔
        trace=[(sourceFuture cell).observe x] := by
      simpa only [List.map_cons,List.map_nil] using
        (List.map_inj_right (l := trace) (l' := [(sourceFuture cell).observe x])
          (fun _ _ h => image_injective cell h))
    simp only [hi]
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      simp only [List.map_cons,fullFuture,future_observation cell x hx,image_eq_iff]
      by_cases hf : first=(sourceFuture cell).observe x
      · simp only [hf,ite_true]
        change (factors.map (fun o => (targetFuture cell).weight (translate cell x) a o *
          fullFuture (targetFuture cell) ((targetFuture cell).next (translate cell x) a o) rest (tail.map (image cell)))).sum =
          (factors.map (fun o => (sourceFuture cell).weight x a o *
          fullFuture (sourceFuture cell) ((sourceFuture cell).next x a o) rest tail)).sum
        apply congrArg List.sum
        apply List.map_congr_left
        intro o ho
        rw [future_weight,future_next,ih _ (future_closure_next cell x hx a o)]
      · simp only [hf,ite_false]

theorem names_injective (cell : Owner) : Function.Injective (names cell) := by
  intro x y h
  cases cell <;> cases x <;> cases y <;> simp_all [names,ModeExecution.firstNames,ModeExecution.secondNames]
theorem independently_sufficient (cell : Owner) (copy : Bool) :
    FullFutureSufficient (RegisterFuture.future (frame cell copy) NativePackageBundle.canonical (frameReady cell copy)) := by
  obtain ⟨h,hs⟩ := NativePackageFuture.all_unbounded_words cell copy (names cell) (names_injective cell)
  exact hs

theorem middle_bundle :
    (NativePackageBundle.canonical true).map (NativePackageBundle.select false)=
      (NativePackageBundle.canonical false).map (NativePackageBundle.select true) := rfl
theorem middle_root (h : Factor) : targetRoot true h=sourceRoot false h := by
  simp only [targetRoot,interpreted_translation,source_root]
  rfl
theorem middle_observation (x : Frame.Registers) :
    RegisterFuture.observation (target true) NativePackageBundle.canonical (frameReady true false) x=
      RegisterFuture.observation (source false) NativePackageBundle.canonical (frameReady false true) x := by
  rw [observation_equation,observation_equation]
  rfl
theorem middle_future : targetFuture true=sourceFuture false := by
  rfl

theorem middle_closure (x : Frame.Registers) (hx : TargetClosure true x) : SourceClosure false x := by
  induction hx with
  | root x hm =>
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hm
    rw [middle_root]
    exact FutureClosure.root _ (List.mem_map.mpr ⟨h,hh,rfl⟩)
  | step hx da o ho ih =>
    change SourceClosure false (RegisterFuture.next (target true) NativePackageBundle.canonical
      (frameReady true false) _ da o)
    rw [next_equation]
    have hn := FutureClosure.step ih da o ho
    change SourceClosure false (RegisterFuture.next (source false) NativePackageBundle.canonical
      (frameReady false true) _ da o) at hn
    rw [next_equation] at hn
    exact hn

theorem composed_program (x : Frame.Registers) : translate false (translate true x)=
    Frame.pack (⟨(x ()).factor,(x ()).counter+6,(x ()).ticks+6,
      (((x ()).residue.1++(x ()).residue.1)++((x ()).residue.1++(x ()).residue.1),(x ()).residue.2),
      (x ()).funded⟩ : Frame.State) := by
  simp only [translate,interpreted_translation]
  simp [shifted,jump,Frame.pack,Nat.add_assoc]

/-- The first target is literally the second source in both primitive bundle
and interpreted whole future; hence full trace transport composes. -/
theorem composed_all_word_transport (x : Frame.Registers) (hx : SourceClosure true x)
    (word : List (Unit × Bool)) (trace : List Observation) :
    fullFuture (targetFuture false) (translate false (translate true x)) word
      ((trace.map (image true)).map (image false))=fullFuture (sourceFuture true) x word trace := by
  rw [all_word_trace_transport false (translate true x) (middle_closure _ (translated_closure true x hx)),
    ← middle_future,all_word_trace_transport true x hx]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationFuture
