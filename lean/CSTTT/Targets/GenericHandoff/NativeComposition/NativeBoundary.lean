import CSTTT.Targets.GenericHandoff.NativeComposition.NativeSemantics

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence

def boundary : (k : Unit) → Expr Owner MemoryValue Unit (fun _ => State) Unit State :=
  fun _ => .register ()

theorem boundary_ready (a : Assignment Owner MemoryValue) : RegisterSubstitution.Ready boundary a := by
  intro r k hk
  simp [boundary,Expr.dependencies] at hk

theorem boundary_identity (a : Assignment Owner MemoryValue) (hb : RegisterSubstitution.Ready boundary a)
    (x : Registers) : RegisterSubstitution.translate boundary a hb x () = x := by
  funext r
  cases r
  have he := RegisterSubstitution.translation_equation boundary a hb x () ()
  change some (x ()) = some (RegisterSubstitution.translate boundary a hb x () ()) at he
  exact (Option.some.inj he).symm

/-- This physical boundary preserves the ACTUAL entry. It is distinct from
any whole-future map between retrospectively initialized frames. -/
theorem actual_middle_initializer (hf : Ready firstAcquisition nativeAssignment)
    (hs : Ready secondAcquisition nativeAssignment) (hb : RegisterSubstitution.Ready boundary nativeAssignment)
    (h : Factor) (actual : Registers) (routes : Route → AcquisitionExecution.Route History Bool)
    (he : firstEntry firstAcquisition nativeAssignment hf h h = some actual)
    (hr : secondAcquisition.routes.read nativeAssignment = some routes) :
    RegisterSubstitution.translate boundary nativeAssignment hb actual () =
      initial secondAcquisition nativeAssignment hs (routes h).history := by
  have hx := Option.some.inj ((first_entry hf h).symm.trans he)
  have hroute := Option.some.inj ((native_routes false true 2 2 1 nativeAssignment rfl).symm.trans hr)
  subst actual
  subst routes
  rw [boundary_identity,second_initializer]

theorem native_next_arrival (hf : Ready firstAcquisition nativeAssignment)
    (hs : Ready secondAcquisition nativeAssignment) (hb : RegisterSubstitution.Ready boundary nativeAssignment)
    (h : Factor) :
    nextArrival firstAcquisition secondAcquisition boundary nativeAssignment hf hs hb h h h =
      some (snapshot h 8 5 false) := by
  simp only [nextArrival,first_entry,bind,pure,Option.bind_some,boundary_identity,second_from_start]

theorem native_next_entry (hf : Ready firstAcquisition nativeAssignment)
    (hs : Ready secondAcquisition nativeAssignment) (hb : RegisterSubstitution.Ready boundary nativeAssignment)
    (h : Factor) :
    nextEntry firstAcquisition secondAcquisition boundary nativeAssignment hf hs hb h h h h =
      some (snapshot h 8 6 false) := by
  simp only [nextEntry,native_next_arrival]
  simpa only [firstEntry,second_arrival] using second_entry hs h

theorem native_next_semantic_arrival (hf : Ready firstAcquisition nativeAssignment)
    (hs : Ready secondAcquisition nativeAssignment) (hb : RegisterSubstitution.Ready boundary nativeAssignment)
    (h : Factor) : Arrival secondSchema secondAcquisition nativeAssignment hs h (snapshot h 8 5 false) :=
  next_arrival_sound secondSchema firstAcquisition secondAcquisition boundary nativeAssignment hf hs hb h h h _
    (second_route_check h) (actual_middle_initializer hf hs hb h) (native_next_arrival hf hs hb h)

theorem actual_physical_clock_seam (h : Factor) :
    firstSchema.clock firstSchema.exitStage = (snapshot h 4 2 true ()).1.counter ∧
    secondSchema.clock secondSchema.entryStage = (snapshot h 4 2 true ()).1.counter ∧
    secondSchema.clock secondSchema.exitStage = (snapshot h 8 6 false ()).1.counter ∧
    firstNames true=secondNames true := by
  exact ⟨rfl,rfl,rfl,rfl⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
