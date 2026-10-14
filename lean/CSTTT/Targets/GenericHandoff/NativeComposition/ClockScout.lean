import CSTTT.Targets.GenericHandoff.NativeComposition.NativeBoundary

/-! The initial linear second clock has the correct outer seam but places its
mixed stage at4 while actual reception happens at5. Preserve this direct
counterexample before replacing the candidate clock interface. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ClockScout
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence ModeExecution

def oldLinearClock (s : Stage) := 2+2*s.val

def ActualMixedReceptionClock (hr : Ready secondAcquisition nativeAssignment) : Prop :=
  ∀ h arrived, firstArrival secondAcquisition nativeAssignment hr h=some arrived →
    (arrived ()).1.counter=oldLinearClock 1

theorem old_linear_clock_rejected (hr : Ready secondAcquisition nativeAssignment) :
    ¬ ActualMixedReceptionClock hr := by
  intro h
  have he := h (false,false,false) _ (second_arrival hr (false,false,false))
  change 5=4 at he
  contradiction

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ClockScout
