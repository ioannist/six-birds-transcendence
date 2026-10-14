import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationReplay
import CSTTT.Targets.GenericHandoff.NativeComposition.PackageFuture

/-! Full futures on the actual source and publication of each handoff. Roots
come from the independent acquisition initializer. Closure admits all declared
outcomes, including those with zero weight, with no time or word bound. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationFuture
open RegisterInterpreter CSTTT.TransportTheory PublicationReplay

abbrev frame (cell : Owner) (copy : Bool) := NativePackageFuture.raw cell copy
  (AvailabilityPublication.dataOwner cell copy) (names cell)
abbrev source (cell : Owner) := frame cell true
abbrev target (cell : Owner) := frame cell false
abbrev frameReady (cell : Owner) (copy : Bool) :=
  (NativePackageFuture.ready_iff cell copy (AvailabilityPublication.dataOwner cell copy) (names cell)
    NativePackageBundle.canonical).mpr (by cases cell <;> rfl)

theorem selected_round (cell : Owner) (copy : Bool) :
    AvailabilityPublication.selected cell copy=
      PublicationExecution.roundInput (if copy then round cell else round cell+1) := by
  cases cell <;> cases copy <;> rfl

theorem next_equation (cell : Owner) (copy : Bool) (x : Frame.Registers) (da : Unit × Bool) (o : Factor) :
    RegisterFuture.next (frame cell copy) NativePackageBundle.canonical (frameReady cell copy) x da o=
      Frame.pack (ModeExecution.stepState (x ()) o) := by
  unfold frame NativePackageFuture.raw
  have h := (FutureCellReindex.ready_iff (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
    id (NativePackageFuture.value copy)
    (Frame.raw cell false (AvailabilityPublication.dataOwner cell copy) (names cell)) NativePackageBundle.canonical).mp
      (frameReady cell copy)
  rw [FutureCellReindex.next_equation (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
    id (NativePackageFuture.value copy)
    (Frame.raw cell false (AvailabilityPublication.dataOwner cell copy) (names cell)) NativePackageBundle.canonical
      (frameReady cell copy) h]
  simpa only [Bool.false_eq_true,ite_false,selected_round,PublicationExecution.round_update] using
    Frame.next_equation cell false (AvailabilityPublication.dataOwner cell copy) (names cell)
    (NativePackageFuture.inputs copy NativePackageBundle.canonical) h (AvailabilityPublication.selected cell copy)
    (NativePackageFuture.selected_input cell copy) x da o

theorem row_equation (cell : Owner) (copy : Bool) (x : Frame.Registers) (da : Unit × Bool) :
    RegisterFuture.row (frame cell copy) NativePackageBundle.canonical (frameReady cell copy) x da=
      if (x ()).funded then
        (if da.2 && !(x ()).factor.2.1 then [] else [(destination (x ()).factor da.2,(1:Rat))]) else [] := by
  unfold frame NativePackageFuture.raw
  have h := (FutureCellReindex.ready_iff (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
    id (NativePackageFuture.value copy)
    (Frame.raw cell false (AvailabilityPublication.dataOwner cell copy) (names cell)) NativePackageBundle.canonical).mp
      (frameReady cell copy)
  rw [FutureCellReindex.row_equation (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
    id (NativePackageFuture.value copy)
    (Frame.raw cell false (AvailabilityPublication.dataOwner cell copy) (names cell)) NativePackageBundle.canonical
      (frameReady cell copy) h]
  simpa only [Bool.false_eq_true,ite_false,selected_round,PublicationExecution.round_rows] using
    Frame.row_equation cell false (AvailabilityPublication.dataOwner cell copy) (names cell)
    (NativePackageFuture.inputs copy NativePackageBundle.canonical) h (AvailabilityPublication.selected cell copy)
    (NativePackageFuture.selected_input cell copy) x da

theorem observation_equation (cell : Owner) (copy : Bool) (x : Frame.Registers) :
    RegisterFuture.observation (frame cell copy) NativePackageBundle.canonical (frameReady cell copy) x=
      TemporalRuntimeCoherence.observationImage (names cell)
        (TemporalFactorRules.observe (factorSchema (AvailabilityPublication.dataOwner cell copy))
          (AvailabilityPublication.selected cell copy).temporal 2 (x ())) := by
  unfold frame NativePackageFuture.raw
  have h := (FutureCellReindex.ready_iff (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
    id (NativePackageFuture.value copy)
    (Frame.raw cell false (AvailabilityPublication.dataOwner cell copy) (names cell)) NativePackageBundle.canonical).mp
      (frameReady cell copy)
  rw [FutureCellReindex.observation_equation (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
    id (NativePackageFuture.value copy)
    (Frame.raw cell false (AvailabilityPublication.dataOwner cell copy) (names cell)) NativePackageBundle.canonical
      (frameReady cell copy) h]
  exact Frame.observation_equation cell false (AvailabilityPublication.dataOwner cell copy) (names cell)
    (NativePackageFuture.inputs copy NativePackageBundle.canonical) h (AvailabilityPublication.selected cell copy)
    (NativePackageFuture.selected_input cell copy) x

noncomputable def sourceRoot (cell : Owner) (h : Factor) : Frame.Registers :=
  Frame.pack ((AcquisitionExecution.initial (PublicationReplay.raw cell) PublicationExecution.nativeAssignment
    (PublicationReplay.ready cell) h ()).1)
noncomputable def targetRoot (cell : Owner) (h : Factor) :=
  RegisterSubstitution.translate (translation cell) NativePackageBundle.canonical (mapReady cell) (sourceRoot cell h) ()
noncomputable def sourceRoots (cell : Owner) := factors.map (sourceRoot cell)
noncomputable def targetRoots (cell : Owner) := factors.map (targetRoot cell)
abbrev SourceClosure (cell : Owner) := RegisterFuture.Closure (source cell) NativePackageBundle.canonical
  (frameReady cell true) (sourceRoots cell)
abbrev TargetClosure (cell : Owner) := RegisterFuture.Closure (target cell) NativePackageBundle.canonical
  (frameReady cell false) (targetRoots cell)

theorem source_root (cell : Owner) (h : Factor) :
    sourceRoot cell h=Frame.pack (⟨h,start cell,start cell,(List.replicate (copies cell) h,[false,true]),true⟩ : Frame.State) := by
  cases cell
  · exact congrArg (fun y : ModeExecution.Registers => Frame.pack ((y ()).1))
      (PublicationExecution.second_initializer (PublicationReplay.ready false) h)
  · exact congrArg (fun y : ModeExecution.Registers => Frame.pack ((y ()).1))
      (PublicationExecution.first_initializer (PublicationReplay.ready true) h)

theorem root_is_actual_entry (cell : Owner) (h : Factor) :
    SupportedAcquisitionSequence.firstEntry (PublicationReplay.raw cell) PublicationExecution.nativeAssignment
      (PublicationReplay.ready cell) h h=some (ModeExecution.pack (targetRoot cell h (),cell)) := by
  simp only [targetRoot,interpreted_translation,source_root]
  cases cell
  · exact PublicationExecution.second_entry (PublicationReplay.ready false) h
  · exact PublicationExecution.first_entry (PublicationReplay.ready true) h

theorem semantic_root_entry (cell : Owner) (h : Factor) :
    AcquisitionExecution.Entry (PublicationReplay.schema cell) (PublicationReplay.raw cell)
      PublicationExecution.nativeAssignment (PublicationReplay.ready cell) (ModeExecution.pack (targetRoot cell h (),cell)) := by
  have he := root_is_actual_entry cell h
  cases cell
  · have hs := PublicationExecution.second_entry (PublicationReplay.ready false) h
    have hv := Option.some.inj (hs.symm.trans he)
    rw [← hv]
    exact PublicationExecution.second_semantic_entry (PublicationReplay.ready false) h
  · have hs := PublicationExecution.first_entry (PublicationReplay.ready true) h
    have hv := Option.some.inj (hs.symm.trans he)
    rw [← hv]
    exact PublicationExecution.first_semantic_entry (PublicationReplay.ready true) h

def Shape (cell : Owner) (x : Frame.Registers) : Prop :=
  (x ()).funded=true ∧ ∃ h : Factor, (x ()).residue=(List.replicate (copies cell) h,[false,true])
theorem closure_shape (cell : Owner) (x : Frame.Registers) (hx : SourceClosure cell x) : Shape cell x := by
  induction hx with
  | root x hm =>
    obtain ⟨h,_,rfl⟩ := List.mem_map.mp hm
    rw [source_root]
    exact ⟨rfl,h,rfl⟩
  | step hx da o ho ih =>
    change Shape cell (RegisterFuture.next (source cell) NativePackageBundle.canonical (frameReady cell true) _ da o)
    rw [next_equation]
    exact ih

noncomputable def translate (cell : Owner) (x : Frame.Registers) :=
  RegisterSubstitution.translate (translation cell) NativePackageBundle.canonical (mapReady cell) x ()
theorem translated_successor (cell : Owner) (x : Frame.Registers) (da : Unit × Bool) (o : Factor) :
    translate cell (RegisterFuture.next (source cell) NativePackageBundle.canonical (frameReady cell true) x da o)=
      RegisterFuture.next (target cell) NativePackageBundle.canonical (frameReady cell false) (translate cell x) da o := by
  simp only [translate,interpreted_translation,next_equation]
  simp [shifted,ModeExecution.stepState,Frame.pack,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem translated_weight (cell : Owner) (x : Frame.Registers) (da : Unit × Bool) (o : Factor) :
    RegisterFuture.weight (target cell) NativePackageBundle.canonical (frameReady cell false) (translate cell x) da o=
      RegisterFuture.weight (source cell) NativePackageBundle.canonical (frameReady cell true) x da o := by
  simp only [RegisterFuture.weight,row_equation,translate,interpreted_translation]
  rfl
theorem translated_closure (cell : Owner) (x : Frame.Registers) (hx : SourceClosure cell x) :
    TargetClosure cell (translate cell x) := by
  induction hx with
  | root x hm =>
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hm
    exact FutureClosure.root _ (List.mem_map.mpr ⟨h,hh,rfl⟩)
  | step hx da o ho ih =>
    change TargetClosure cell (translate cell (RegisterFuture.next (source cell) NativePackageBundle.canonical
      (frameReady cell true) _ da o))
    rw [translated_successor]
    exact FutureClosure.step ih da o ho

theorem translation_is_supported_episode (cell : Owner) (x : Frame.Registers) (hx : SourceClosure cell x) :
    SupportedAcquisitionSequence.postExit (PublicationReplay.raw cell) PublicationExecution.nativeAssignment
      (PublicationReplay.ready cell) (x ()).factor (x ()).factor
      (SupportedAcquisitionSequence.fromStart (PublicationReplay.raw cell) PublicationExecution.nativeAssignment
        (PublicationReplay.ready cell) (ModeExecution.pack (x (),swapOwner cell)) (x ()).factor)=
      some (ModeExecution.pack (translate cell x (),cell)) := by
  simp only [translate,interpreted_translation]
  exact PublicationReplay.supported_translation cell (x ()) (closure_shape cell x hx).1

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationFuture
