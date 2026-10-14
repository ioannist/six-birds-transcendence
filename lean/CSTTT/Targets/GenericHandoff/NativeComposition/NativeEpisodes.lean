import CSTTT.Targets.GenericHandoff.NativeComposition.EpisodeRules

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence

def nativeAssignment : Assignment Owner MemoryValue := fun cell =>
  some (episodePair (if cell then 0 else 1))
abbrev firstAcquisition := acquisition true false 0 1
abbrev secondAcquisition := acquisition false true 2 2

def snapshot (h : Factor) (copies time : Nat) (mode : Owner) : Registers :=
  pack ((⟨h,time,time,(List.replicate copies h,[false,true]),true⟩ : Frame.State),mode)

theorem native_first_ready : Ready firstAcquisition nativeAssignment :=
  acquisition_ready true false 0 1 nativeAssignment rfl

theorem native_second_ready : Ready secondAcquisition nativeAssignment :=
  acquisition_ready false true 2 2 nativeAssignment rfl

theorem round_route (n : Nat) (h : Factor) :
    TemporalFactorRules.route (roundInput n).temporal h = some ⟨h,h,[false,true]⟩ := by
  have he : (roundInput n).temporal.routes = (factorData false).routes := by
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  unfold TemporalFactorRules.route
  rw [he]
  rcases h with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> rfl

theorem round_path (n : Nat) (h : Factor) : routePath (roundInput n).temporal h = [false,true] := by
  change ((TemporalFactorRules.route (roundInput n).temporal h).map TemporalFactorRules.Route.eventPath).getD [] = _
  rw [round_route]
  rfl

theorem native_routes (cell sourceOwner : Owner) (start stride n : Nat)
    (a : Assignment Owner MemoryValue) (hp : a cell=some (episodePair n)) :
    (acquisition cell sourceOwner start stride).routes.read a = some (fun h => ⟨h,[false,true]⟩) := by
  simp only [acquisition,CellView.read,hp,Option.map_some]
  congr 1
  funext h
  simp only [acquisitionRoutes,episodePair,round_route]

theorem first_initializer (hr : Ready firstAcquisition nativeAssignment) (h : Factor) :
    initial firstAcquisition nativeAssignment hr h = snapshot h 2 0 false := by
  rw [acquisition_initial true false 0 1 nativeAssignment hr (episodePair 0) rfl]
  simp only [initialized,episodePair,round_path]
  rfl

theorem second_initializer (hr : Ready secondAcquisition nativeAssignment) (h : Factor) :
    initial secondAcquisition nativeAssignment hr h = snapshot h 4 2 true := by
  rw [acquisition_initial false true 2 2 nativeAssignment hr (episodePair 1) rfl]
  simp only [initialized,episodePair,round_path]
  rfl

theorem snapshot_step (cell sourceOwner : Owner) (start stride n : Nat)
    (a : Assignment Owner MemoryValue) (hr : Ready (acquisition cell sourceOwner start stride) a)
    (hp : a cell=some (episodePair n)) (h : Factor) (copies time : Nat) (mode : Owner) :
    update (acquisition cell sourceOwner start stride) a hr (snapshot h copies time mode) () false h =
      snapshot h copies (time+1) mode := by
  rw [episode_update cell sourceOwner start stride a hr n hp]
  rfl

theorem snapshot_check (cell sourceOwner : Owner) (start stride n : Nat)
    (a : Assignment Owner MemoryValue) (hp : a cell=some (episodePair n))
    (h : Factor) (copies time : Nat) (mode : Owner) :
    stepCheck (acquisition cell sourceOwner start stride) a (snapshot h copies time mode) () false h = true :=
  episode_step_check cell sourceOwner start stride a n hp _ rfl

theorem first_from_start (hr : Ready firstAcquisition nativeAssignment)
    (h : Factor) (time : Nat) :
    fromStart firstAcquisition nativeAssignment hr (snapshot h 2 time false) h =
      some (snapshot h 4 (time+1) true) := by
  have hroutes := native_routes true false 0 1 0 nativeAssignment rfl
  have hhist : firstAcquisition.histories.read nativeAssignment = some (fun h => [((),false,h)]) := rfl
  simp only [fromStart,hroutes,hhist,bind,pure,Option.bind_some,supportedFold,
    snapshot_check true false 0 1 0 nativeAssignment rfl,ite_true,
    snapshot_step true false 0 1 0 nativeAssignment hr rfl]
  rw [acquisition_receive true false 0 1 nativeAssignment hr (episodePair 0) rfl]
  rfl

theorem second_from_start (hr : Ready secondAcquisition nativeAssignment)
    (h : Factor) (time : Nat) :
    fromStart secondAcquisition nativeAssignment hr (snapshot h 4 time true) h =
      some (snapshot h 8 (time+3) false) := by
  have hroutes := native_routes false true 2 2 1 nativeAssignment rfl
  have hhist : secondAcquisition.histories.read nativeAssignment =
      some (fun h => [((),false,h),((),false,h),((),false,h)]) := rfl
  simp only [fromStart,hroutes,hhist,bind,pure,Option.bind_some,supportedFold,
    snapshot_check false true 2 2 1 nativeAssignment rfl,ite_true,
    snapshot_step false true 2 2 1 nativeAssignment hr rfl]
  rw [acquisition_receive false true 2 2 nativeAssignment hr (episodePair 1) rfl]
  rfl

theorem first_arrival (hr : Ready firstAcquisition nativeAssignment) (h : Factor) :
    firstArrival firstAcquisition nativeAssignment hr h = some (snapshot h 4 1 true) := by
  have hroutes := native_routes true false 0 1 0 nativeAssignment rfl
  simp only [firstArrival,hroutes,bind,pure,Option.bind_some,first_initializer,first_from_start]

theorem second_arrival (hr : Ready secondAcquisition nativeAssignment) (h : Factor) :
    firstArrival secondAcquisition nativeAssignment hr h = some (snapshot h 8 5 false) := by
  have hroutes := native_routes false true 2 2 1 nativeAssignment rfl
  simp only [firstArrival,hroutes,bind,pure,Option.bind_some,second_initializer,second_from_start]

theorem first_entry (hr : Ready firstAcquisition nativeAssignment) (h : Factor) :
    firstEntry firstAcquisition nativeAssignment hr h h = some (snapshot h 4 2 true) := by
  have hroutes := native_routes true false 0 1 0 nativeAssignment rfl
  simp only [firstEntry,first_arrival,postExit,hroutes,bind,pure,Option.bind_some]
  change (some ((),false)).bind (fun da => if stepCheck firstAcquisition nativeAssignment
    (snapshot h 4 1 true) da.1 da.2 h then some (update firstAcquisition nativeAssignment hr
      (snapshot h 4 1 true) da.1 da.2 h) else none) = _
  simp only [bind,pure,Option.bind_some,snapshot_check true false 0 1 0 nativeAssignment rfl,ite_true,
    snapshot_step true false 0 1 0 nativeAssignment hr rfl]

theorem second_entry (hr : Ready secondAcquisition nativeAssignment) (h : Factor) :
    firstEntry secondAcquisition nativeAssignment hr h h = some (snapshot h 8 6 false) := by
  have hroutes := native_routes false true 2 2 1 nativeAssignment rfl
  simp only [firstEntry,second_arrival,postExit,hroutes,bind,pure,Option.bind_some]
  change (some ((),false)).bind (fun da => if stepCheck secondAcquisition nativeAssignment
    (snapshot h 8 5 false) da.1 da.2 h then some (update secondAcquisition nativeAssignment hr
      (snapshot h 8 5 false) da.1 da.2 h) else none) = _
  simp only [bind,pure,Option.bind_some,snapshot_check false true 2 2 1 nativeAssignment rfl,ite_true,
    snapshot_step false true 2 2 1 nativeAssignment hr rfl]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
