import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationReceiver

/-! Execute the second repaired acquisition from the ACTUAL first exit. The
boundary is the identity raw register instruction, checked against the second
independent initializer. No middle state is supplied as a primitive. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationSequence
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence
open ModeExecution PublicationReplay PublicationExecution

def boundary : (k : Unit) → Expr Owner MemoryValue Unit (fun _ => ModeExecution.State) Unit ModeExecution.State :=
  fun _ => .register ()
theorem boundary_ready (a : Assignment Owner MemoryValue) : RegisterSubstitution.Ready boundary a := by
  intro r k hk; simp [boundary,Expr.dependencies] at hk
theorem boundary_identity (a : Assignment Owner MemoryValue) (hb : RegisterSubstitution.Ready boundary a)
    (x : ModeExecution.Registers) : RegisterSubstitution.translate boundary a hb x ()=x := by
  funext r
  have he := RegisterSubstitution.translation_equation boundary a hb x () r
  change some (x ())=some (RegisterSubstitution.translate boundary a hb x () r) at he
  cases r
  exact (Option.some.inj he).symm

theorem actual_middle_initializer (h : Factor) (actual : ModeExecution.Registers)
    (routes : Route → AcquisitionExecution.Route History Bool)
    (he : firstEntry PublicationExecution.firstAcquisition PublicationExecution.nativeAssignment (ready true) h h=some actual)
    (hr : PublicationExecution.secondAcquisition.routes.read PublicationExecution.nativeAssignment=some routes) :
    RegisterSubstitution.translate boundary PublicationExecution.nativeAssignment (boundary_ready PublicationExecution.nativeAssignment) actual ()=
      initial PublicationExecution.secondAcquisition PublicationExecution.nativeAssignment (ready false) (routes h).history := by
  have hx := Option.some.inj ((PublicationExecution.first_entry (ready true) h).symm.trans he)
  have hroute := Option.some.inj ((PublicationExecution.native_routes false true 2 2 1 PublicationExecution.nativeAssignment rfl).symm.trans hr)
  subst actual; subst routes
  rw [boundary_identity,PublicationExecution.second_initializer]

theorem next_arrival (h : Factor) :
    nextArrival PublicationExecution.firstAcquisition PublicationExecution.secondAcquisition boundary PublicationExecution.nativeAssignment
      (ready true) (ready false) (boundary_ready PublicationExecution.nativeAssignment) h h h=
      some (PublicationExecution.snapshot h 8 5 false) := by
  simp only [nextArrival,PublicationExecution.first_entry,bind,pure,Option.bind_some,
    boundary_identity,PublicationExecution.second_from_start]
theorem next_entry (h : Factor) :
    nextEntry PublicationExecution.firstAcquisition PublicationExecution.secondAcquisition boundary PublicationExecution.nativeAssignment
      (ready true) (ready false) (boundary_ready PublicationExecution.nativeAssignment) h h h h=
      some (PublicationExecution.snapshot h 8 6 false) := by
  simp only [nextEntry,next_arrival]
  simpa only [firstEntry,PublicationExecution.second_arrival] using PublicationExecution.second_entry (ready false) h

theorem next_semantic_entry (h : Factor) :
    Entry ModeExecution.secondSchema PublicationExecution.secondAcquisition PublicationExecution.nativeAssignment (ready false)
      (PublicationExecution.snapshot h 8 6 false) := by
  have ha := next_arrival_sound ModeExecution.secondSchema PublicationExecution.firstAcquisition
    PublicationExecution.secondAcquisition boundary PublicationExecution.nativeAssignment (ready true) (ready false)
    (boundary_ready PublicationExecution.nativeAssignment) h h h _ (PublicationExecution.second_route_check h)
    (actual_middle_initializer h) (next_arrival h)
  apply post_exit_sound ModeExecution.secondSchema PublicationExecution.secondAcquisition PublicationExecution.nativeAssignment
    (ready false) h h (PublicationExecution.snapshot h 8 5 false) _
    (PublicationExecution.native_domain false true secondNames 2 2) ha
  · intro routes da _ he
    have hd : ((),false)=da := Option.some.inj he
    subst da
    exact PublicationExecution.snapshot_normalized false true 2 2 1 PublicationExecution.nativeAssignment rfl h 8 5 false
  · simpa only [nextEntry,next_arrival] using next_entry h

theorem physical_middle (h : Factor) :
    PublicationPhysical.entryRun true h=initial (raw false) PublicationExecution.nativeAssignment (ready false) h := by
  change PublicationExecution.snapshot h 4 2 true=initial PublicationExecution.secondAcquisition
    PublicationExecution.nativeAssignment (ready false) h
  rw [PublicationExecution.second_initializer]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationSequence
