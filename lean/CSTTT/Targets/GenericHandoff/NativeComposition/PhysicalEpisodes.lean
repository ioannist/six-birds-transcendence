import CSTTT.Targets.GenericHandoff.EpisodeExecution
import CSTTT.Targets.GenericHandoff.NativeComposition.MiddleControls
import CSTTT.Targets.GenericHandoff.NativeComposition.NativeResourceGame

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PhysicalEpisodes
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence ModeExecution

def ownerExpr (cell sourceOwner : Owner) (names : Owner → CarrierId) :
    Expr Owner MemoryValue Unit (fun _ => State) Unit CarrierId :=
  .map (fun p : FactorData × State => names p.1.resource.owner) (context cell sourceOwner)

theorem owner_evaluation (cell sourceOwner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (p : Input × Input) (hp : a cell=some p) (x : ModeExecution.Registers) :
    (ownerExpr cell sourceOwner names).eval a x ()=some
      (names (if (x ()).2=swapOwner sourceOwner then p.1.temporal.resource.owner else p.2.temporal.resource.owner)) := by
  simp only [ownerExpr,Expr.eval,context_evaluation cell sourceOwner a p hp x,Option.map_some]
  split <;> rfl

theorem first_source_terminal (hf : Ready firstAcquisition nativeAssignment) (h : Factor) :
    EpisodeExecution.sourceTerminal firstAcquisition nativeAssignment hf h=some (snapshot h 2 1 false) := by
  have hr := native_routes true false 0 1 0 nativeAssignment rfl
  have hh : firstAcquisition.histories.read nativeAssignment=some (fun h => [((),false,h)]) := rfl
  simp only [EpisodeExecution.sourceTerminal,hr,hh,bind,Option.bind_some,first_initializer,
    supportedFold,snapshot_check true false 0 1 0 nativeAssignment rfl,ite_true,
    snapshot_step true false 0 1 0 nativeAssignment hf rfl]

theorem second_source_terminal (hs : Ready secondAcquisition nativeAssignment) (h : Factor) :
    EpisodeExecution.sourceTerminal secondAcquisition nativeAssignment hs h=some (snapshot h 4 5 true) := by
  have hr := native_routes false true 2 2 1 nativeAssignment rfl
  have hh : secondAcquisition.histories.read nativeAssignment=
      some (fun h => [((),false,h),((),false,h),((),false,h)]) := rfl
  simp only [EpisodeExecution.sourceTerminal,hr,hh,bind,Option.bind_some,second_initializer,
    supportedFold,snapshot_check false true 2 2 1 nativeAssignment rfl,ite_true,
    snapshot_step false true 2 2 1 nativeAssignment hs rfl]

theorem first_receive_from_terminal (hf : Ready firstAcquisition nativeAssignment) (h : Factor) :
    receive firstAcquisition nativeAssignment hf (snapshot h 2 1 false) h h=snapshot h 4 1 true := by
  rw [acquisition_receive true false 0 1 nativeAssignment hf (episodePair 0) rfl]
  rfl
theorem second_receive_from_terminal (hs : Ready secondAcquisition nativeAssignment) (h : Factor) :
    receive secondAcquisition nativeAssignment hs (snapshot h 4 5 true) h h=snapshot h 8 5 false := by
  rw [acquisition_receive false true 2 2 nativeAssignment hs (episodePair 1) rfl]
  rfl

/-- Mixed-stage source ownership is read BEFORE reception. The receiver writes
target ownership at the same physical time, which is then retained at exit. -/
theorem first_actual_owners (h : Factor) :
    (ownerExpr true false firstNames).eval nativeAssignment (snapshot h 2 1 false) ()=some (firstNames false) ∧
    (ownerExpr true false firstNames).eval nativeAssignment (snapshot h 4 1 true) ()=some (firstNames true) ∧
    (ownerExpr true false firstNames).eval nativeAssignment (snapshot h 4 2 true) ()=some (firstNames true) := by
  simp only [owner_evaluation true false firstNames nativeAssignment (episodePair 0) rfl]
  exact ⟨rfl,rfl,rfl⟩

theorem second_actual_owners (h : Factor) :
    (ownerExpr false true secondNames).eval nativeAssignment (snapshot h 4 5 true) ()=some (secondNames true) ∧
    (ownerExpr false true secondNames).eval nativeAssignment (snapshot h 8 5 false) ()=some (secondNames false) ∧
    (ownerExpr false true secondNames).eval nativeAssignment (snapshot h 8 6 false) ()=some (secondNames false) := by
  simp only [owner_evaluation false true secondNames nativeAssignment (episodePair 1) rfl]
  exact ⟨rfl,rfl,rfl⟩

theorem first_event_durations (h : Factor) :
    (acquisitionEvents 0 1 (episodePair 0) false).orderAdvance=
      (snapshot h 2 1 false ()).1.counter-(snapshot h 2 0 false ()).1.counter ∧
    (acquisitionEvents 0 1 (episodePair 0) true).orderAdvance=
      (snapshot h 4 2 true ()).1.counter-(snapshot h 4 1 true ()).1.counter := ⟨rfl,rfl⟩

theorem second_event_durations (h : Factor) :
    (acquisitionEvents 2 2 (episodePair 1) false).orderAdvance=
      (snapshot h 4 5 true ()).1.counter-(snapshot h 4 2 true ()).1.counter ∧
    (acquisitionEvents 2 2 (episodePair 1) true).orderAdvance=
      (snapshot h 8 6 false ()).1.counter-(snapshot h 8 5 false ()).1.counter := ⟨rfl,rfl⟩

theorem reception_preserves_time_changes_owner (h : Factor) :
    (snapshot h 2 1 false ()).1.counter=(snapshot h 4 1 true ()).1.counter ∧
    (snapshot h 4 5 true ()).1.counter=(snapshot h 8 5 false ()).1.counter ∧
    firstNames false≠firstNames true ∧ secondNames true≠secondNames false := by
  exact ⟨rfl,rfl,by decide +kernel,by decide +kernel⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PhysicalEpisodes
