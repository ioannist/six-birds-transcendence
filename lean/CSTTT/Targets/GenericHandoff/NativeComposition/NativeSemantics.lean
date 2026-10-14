import CSTTT.Targets.GenericHandoff.NativeComposition.NativeEpisodes

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence

def firstNames (o : Owner) : CarrierId := ⟨if o then 55 else 17⟩
def secondNames (o : Owner) : CarrierId := ⟨if o then 55 else 101⟩
abbrev firstSchema := acquisitionSchema false firstNames 0 1
abbrev secondSchema := acquisitionSchema true secondNames 2 2

theorem native_domain (cell sourceOwner : Owner) (names : Owner → CarrierId) (start stride : Nat) :
    DomainCheck (acquisitionSchema sourceOwner names start stride) (acquisition cell sourceOwner start stride) := by
  have hn : factors ≠ [] := by decide +kernel
  have hi : ∀ id : Bool, id ∈ [false,true] := by decide +kernel
  have hs : ∀ s : Stage, s ∈ stages := by decide +kernel
  have hd : ([()] : List Unit) ≠ [] := by decide +kernel
  have hu : ∀ d : Unit, d ∈ [()] := by intro d; cases d; decide +kernel
  exact ⟨hn,hn,factor_mem,factor_mem,hi,hs,hd,hu⟩

theorem first_route_check (h : Factor) : RouteCheck firstSchema firstAcquisition nativeAssignment h := by
  refine ⟨(fun h => [((),false,h)]),(fun h => ⟨h,[false,true]⟩),
    acquisitionEvents 0 1 (episodePair 0),stages,(episodePair 0).1.receiver,
    rfl,native_routes true false 0 1 0 nativeAssignment rfl,rfl,rfl,rfl,
    factor_mem h,factor_mem h,?_,?_⟩
  · change PathCheck firstSchema (acquisitionEvents 0 1 (episodePair 0)) stages [false,true]
    refine ⟨false,[true],rfl,rfl,?_,?_,true,rfl,rfl,rfl,rfl⟩
    · intro id _; cases id <;> decide +kernel
    · decide +kernel
  · change Activated (episodePair 0).1.receiver (acquisitionEvents 0 1 (episodePair 0)) stages [false,true]
    refine ⟨rfl,rfl,rfl,?_⟩
    intro _
    refine ⟨false,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem second_route_check (h : Factor) : RouteCheck secondSchema secondAcquisition nativeAssignment h := by
  refine ⟨(fun h => [((),false,h),((),false,h),((),false,h)]),(fun h => ⟨h,[false,true]⟩),
    acquisitionEvents 2 2 (episodePair 1),stages,(episodePair 1).1.receiver,
    rfl,native_routes false true 2 2 1 nativeAssignment rfl,rfl,rfl,rfl,
    factor_mem h,factor_mem h,?_,?_⟩
  · change PathCheck secondSchema (acquisitionEvents 2 2 (episodePair 1)) stages [false,true]
    refine ⟨false,[true],rfl,rfl,?_,?_,true,rfl,rfl,rfl,rfl⟩
    · intro id _; cases id <;> decide +kernel
    · decide +kernel
  · change Activated (episodePair 1).1.receiver (acquisitionEvents 2 2 (episodePair 1)) stages [false,true]
    refine ⟨rfl,rfl,rfl,?_⟩
    intro _
    refine ⟨false,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem snapshot_normalized (cell sourceOwner : Owner) (start stride n : Nat)
    (a : Assignment Owner MemoryValue) (hp : a cell=some (episodePair n))
    (h : Factor) (copies time : Nat) (mode : Owner) :
    StrategyGame.Normalized (rows (acquisition cell sourceOwner start stride) a)
      (snapshot h copies time mode) () false := by
  have hr := episode_rows cell sourceOwner start stride a n hp (snapshot h copies time mode) () false
  change rows _ _ (snapshot h copies time mode) () false = [(h,(1:Rat))] at hr
  refine ⟨?_,?_,h,1,?_,by decide +kernel⟩
  · intro e he
    rw [hr] at he
    have he' : e=(h,(1:Rat)) := by simpa using he
    subst e
    change 0 ≤ (1:Rat)
    decide +kernel
  · rw [hr]
    change (1:Rat)+0=1
    decide +kernel
  · rw [hr]; simp

theorem first_semantic_entry (hr : Ready firstAcquisition nativeAssignment) (h : Factor) :
    Entry firstSchema firstAcquisition nativeAssignment hr (snapshot h 4 2 true) := by
  have ha := first_arrival_sound firstSchema firstAcquisition nativeAssignment hr h _
    (first_route_check h) (first_arrival hr h)
  apply post_exit_sound firstSchema firstAcquisition nativeAssignment hr h h (snapshot h 4 1 true) _
    (native_domain true false firstNames 0 1) ha
  · intro routes da _ he
    have hd : ((),false)=da := Option.some.inj he
    subst da
    exact snapshot_normalized true false 0 1 0 nativeAssignment rfl h 4 1 true
  · simpa only [firstEntry,first_arrival] using first_entry hr h

theorem second_semantic_entry (hr : Ready secondAcquisition nativeAssignment) (h : Factor) :
    Entry secondSchema secondAcquisition nativeAssignment hr (snapshot h 8 6 false) := by
  have ha := first_arrival_sound secondSchema secondAcquisition nativeAssignment hr h _
    (second_route_check h) (second_arrival hr h)
  apply post_exit_sound secondSchema secondAcquisition nativeAssignment hr h h (snapshot h 8 5 false) _
    (native_domain false true secondNames 2 2) ha
  · intro routes da _ he
    have hd : ((),false)=da := Option.some.inj he
    subst da
    exact snapshot_normalized false true 2 2 1 nativeAssignment rfl h 8 5 false
  · simpa only [firstEntry,second_arrival] using second_entry hr h

/-- Semantic arrivals cannot replace the actual interpreted terminal state. -/
theorem arrival_computed (cell sourceOwner : Owner) (start stride : Nat)
    (cfg : Schema Stage Bool History Route) (a : Assignment Owner MemoryValue)
    (hr : Ready (acquisition cell sourceOwner start stride) a) (rid : Route) (arrived : Registers)
    (ha : Arrival cfg (acquisition cell sourceOwner start stride) a hr rid arrived) :
    firstArrival (acquisition cell sourceOwner start stride) a hr rid = some arrived := by
  rcases ha with ⟨histories,routes,events,realized,receiver,hh,hroutes,_,_,_,_,_,_,_,source,hex,he⟩
  have hf := (fold_some_iff (acquisition cell sourceOwner start stride) a hr
    (initial (acquisition cell sourceOwner start stride) a hr (routes rid).history) source
    (histories (routes rid).history)).mpr hex
  simp only [firstArrival,fromStart,hh,hroutes,bind,pure,Option.bind_some,hf,he]

theorem all_first_entries (hr : Ready firstAcquisition nativeAssignment) (entry : Registers)
    (he : Entry firstSchema firstAcquisition nativeAssignment hr entry) :
    ∃ h, entry=snapshot h 4 2 true := by
  rcases he with ⟨_,rid,arrived,routes,da,o,ha,_,hda,_,_,_,hp,he⟩
  have hs := (first_arrival hr rid).symm.trans (arrival_computed true false 0 1 firstSchema nativeAssignment hr rid arrived ha)
  have harr := Option.some.inj hs
  subst arrived
  have hd : ((),false)=da := Option.some.inj hda
  subst da
  have ho := (episode_positive_unique true false 0 1 nativeAssignment 0 rfl _ () false o).mp hp
  have hout : o=rid := ho.2
  subst o
  refine ⟨rid,he.trans ?_⟩
  exact snapshot_step true false 0 1 0 nativeAssignment hr rfl rid 4 1 true

theorem all_second_entries (hr : Ready secondAcquisition nativeAssignment) (entry : Registers)
    (he : Entry secondSchema secondAcquisition nativeAssignment hr entry) :
    ∃ h, entry=snapshot h 8 6 false := by
  rcases he with ⟨_,rid,arrived,routes,da,o,ha,_,hda,_,_,_,hp,he⟩
  have hs := (second_arrival hr rid).symm.trans (arrival_computed false true 2 2 secondSchema nativeAssignment hr rid arrived ha)
  have harr := Option.some.inj hs
  subst arrived
  have hd : ((),false)=da := Option.some.inj hda
  subst da
  have ho := (episode_positive_unique false true 2 2 nativeAssignment 1 rfl _ () false o).mp hp
  have hout : o=rid := ho.2
  subst o
  refine ⟨rid,he.trans ?_⟩
  exact snapshot_step false true 2 2 1 nativeAssignment hr rfl rid 8 5 false

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
