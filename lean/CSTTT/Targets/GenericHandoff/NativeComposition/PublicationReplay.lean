import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationSemantics
import CSTTT.Targets.GenericHandoff.NativeComposition.EpisodeMap
import CSTTT.Targets.GenericHandoff.EpisodeExecution

/-! Raw bundle instructions replay the actual copied history selected by the
current factor, receive its actual incoming residue, and take one supported
exit step. At initialized roots this is actual Entry. Off root it is supported
replay, with no claim that an arbitrary closure state is an Arrival. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationReplay
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence ModeExecution
open PublicationExecution

def start (cell : Owner) := if cell then 0 else 2
def stride (cell : Owner) := if cell then 1 else 2
def round (cell : Owner) := if cell then 0 else 1
def jump (cell : Owner) := if cell then 2 else 4
def copies (cell : Owner) := if cell then 2 else 4
def names (cell : Owner) := if cell then firstNames else secondNames
def raw (cell : Owner) := acquisition cell (swapOwner cell) (start cell) (stride cell)
def schema (cell : Owner) := acquisitionSchema (swapOwner cell) (names cell) (start cell) (stride cell)

theorem ready (cell : Owner) : Ready (raw cell) PublicationExecution.nativeAssignment := by
  cases cell
  · exact PublicationExecution.native_second_ready
  · exact PublicationExecution.native_first_ready

def shifted (cell : Owner) (x : Frame.State) : Frame.State :=
  ⟨x.factor,x.counter+jump cell,x.ticks+jump cell,
    (x.residue.1++x.residue.1,x.residue.2),x.funded⟩
def translation (cell : Owner) :
    (r : Unit) → Expr Owner NativePackageBundle.Value Unit (fun _ => Frame.State) Unit Frame.State :=
  fun _ => .map (fun p : (NativePackageBundle.Bundle × NativePackageBundle.Bundle) × Frame.State =>
    EpisodeMap.program (p.1.1.native,p.1.2.native) p.2) (.pair (.cell cell) (.register ()))

theorem translation_ready_iff (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    RegisterSubstitution.Ready (translation cell) a ↔ (a cell).isSome=true := by
  constructor
  · intro h; exact h () cell (by simp [translation,Expr.dependencies])
  · intro h r k hk
    have he : k=cell := by simpa [translation,Expr.dependencies] using hk
    subst k; exact h
theorem translation_missing (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (hm : a cell=none) (x : Frame.Registers) : (translation cell ()).eval a x ()=none := by
  simp [translation,Expr.eval,hm]
abbrev mapReady (cell : Owner) := (translation_ready_iff cell NativePackageBundle.canonical).mpr
  (by cases cell <;> rfl)

theorem assigned_word (cell : Owner) (h : Factor) :
    EpisodeMap.assignedWord (PublicationExecution.episodePair (round cell)) h=
      if cell then [((),false,h)] else [((),false,h),((),false,h),((),false,h)] := by
  cases cell <;> rfl
theorem program_equation (cell : Owner) (x : Frame.State) :
    EpisodeMap.program (PublicationExecution.episodePair (round cell)) x=shifted cell x := by
  simp only [EpisodeMap.program,EpisodeMap.sourceFold,assigned_word]
  cases cell
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,List.foldl_cons,List.foldl_nil,
    PublicationExecution.episodePair,PublicationExecution.round_update]
  all_goals simp [received,stepState,shifted,jump,PublicationExecution.roundInput,
    round,publish,AvailabilityFactor.input,AvailabilityFactor.temporal,canonicalInput,factorData,Nat.add_assoc]

theorem interpreted_translation (cell : Owner) (x : Frame.Registers) :
    RegisterSubstitution.translate (translation cell) NativePackageBundle.canonical (mapReady cell) x ()=
      Frame.pack (shifted cell (x ())) := by
  funext r
  have he := RegisterSubstitution.translation_equation (translation cell) NativePackageBundle.canonical
    (mapReady cell) x () r
  have hv : (translation cell r).eval NativePackageBundle.canonical x ()=
      some (EpisodeMap.program (PublicationExecution.episodePair (round cell)) (x ())) := by
    cases cell <;> rfl
  change (translation cell r).eval _ _ _=some _ at he
  rw [hv,program_equation] at he
  exact (Option.some.inj he).symm

def arrived (cell : Owner) (x : Frame.State) : ModeExecution.State :=
  (⟨x.factor,x.counter+(jump cell-1),x.ticks+(jump cell-1),
    (x.residue.1++x.residue.1,x.residue.2),x.funded⟩,cell)

theorem from_start_actual (cell : Owner) (x : Frame.State) (hx : x.funded=true) :
    fromStart (raw cell) PublicationExecution.nativeAssignment (ready cell)
      (ModeExecution.pack (x,swapOwner cell)) x.factor=some (ModeExecution.pack (arrived cell x)) := by
  have hu : ∀ y : ModeExecution.Registers, ∀ o : Factor,
      update (raw cell) PublicationExecution.nativeAssignment (ready cell) y () false o=
        ModeExecution.pack (stepState (y ()).1 o,(y ()).2) := by
    intro y o
    exact PublicationExecution.episode_update cell (swapOwner cell) (start cell) (stride cell)
      PublicationExecution.nativeAssignment (ready cell) (round cell) (PublicationExecution.assigned_pair cell) y () false o
  have hc : ∀ y : ModeExecution.Registers, (y ()).1.funded=true →
      stepCheck (raw cell) PublicationExecution.nativeAssignment y () false (y ()).1.factor=true := by
    intro y hy
    exact PublicationExecution.episode_step_check cell (swapOwner cell) (start cell) (stride cell)
      PublicationExecution.nativeAssignment (round cell) (PublicationExecution.assigned_pair cell) y hy
  have hr := PublicationExecution.native_routes cell (swapOwner cell) (start cell) (stride cell)
    (round cell) PublicationExecution.nativeAssignment (PublicationExecution.assigned_pair cell)
  change (raw cell).routes.read PublicationExecution.nativeAssignment=some (fun h => ⟨h,[false,true]⟩) at hr
  have hh : (raw cell).histories.read PublicationExecution.nativeAssignment=some
      (if cell then (fun h => [((),false,h)]) else (fun h => [((),false,h),((),false,h),((),false,h)])) := by
    cases cell <;> rfl
  have hre : ∀ y : ModeExecution.Registers, receive (raw cell) PublicationExecution.nativeAssignment
      (ready cell) y x.factor x.factor=ModeExecution.pack
        (received (PublicationExecution.episodePair (round cell)) (swapOwner cell) (y ())) := by
    intro y
    exact acquisition_receive cell (swapOwner cell) (start cell) (stride cell)
      PublicationExecution.nativeAssignment (ready cell) (PublicationExecution.episodePair (round cell))
      (PublicationExecution.assigned_pair cell) y x.factor x.factor
  have h0 := hc (ModeExecution.pack (x,swapOwner cell)) hx
  have h1 := hc (ModeExecution.pack (stepState x x.factor,swapOwner cell)) hx
  have h2 := hc (ModeExecution.pack (stepState (stepState x x.factor) x.factor,swapOwner cell)) hx
  change stepCheck (raw cell) _ (ModeExecution.pack (x,swapOwner cell)) () false x.factor=true at h0
  change stepCheck (raw cell) _ (ModeExecution.pack (stepState x x.factor,swapOwner cell)) () false x.factor=true at h1
  change stepCheck (raw cell) _ (ModeExecution.pack (stepState (stepState x x.factor) x.factor,swapOwner cell)) () false x.factor=true at h2
  cases cell
  all_goals
    simp only [fromStart,hr,hh,Bool.false_eq_true,ite_false,ite_true,bind,Option.bind_some,supportedFold]
    simp only [ModeExecution.pack,stepState] at h0 h1 h2 hu hre ⊢
    simp only [h0,ite_true,hu,h1,h2,Option.bind_some,hre,ModeExecution.pack,stepState]
    simp [received,arrived,jump,stepState,PublicationExecution.episodePair,PublicationExecution.roundInput,
      round,ModeExecution.pack,swap_owner_involution,publish,AvailabilityFactor.input,AvailabilityFactor.temporal,canonicalInput,factorData,Nat.add_assoc]

theorem supported_translation (cell : Owner) (x : Frame.State) (hx : x.funded=true) :
    postExit (raw cell) PublicationExecution.nativeAssignment (ready cell) x.factor x.factor
      (fromStart (raw cell) PublicationExecution.nativeAssignment (ready cell)
        (ModeExecution.pack (x,swapOwner cell)) x.factor)=
      some (ModeExecution.pack (shifted cell x,cell)) := by
  have hr := PublicationExecution.native_routes cell (swapOwner cell) (start cell) (stride cell)
    (round cell) PublicationExecution.nativeAssignment (PublicationExecution.assigned_pair cell)
  change (raw cell).routes.read PublicationExecution.nativeAssignment=some (fun h => ⟨h,[false,true]⟩) at hr
  rw [from_start_actual cell x hx]
  simp only [postExit,hr,bind,Option.bind_some]
  change (some ((),false)).bind (fun da => if stepCheck (raw cell) _
    (ModeExecution.pack (arrived cell x)) da.1 da.2 x.factor then
      some (update (raw cell) _ (ready cell) (ModeExecution.pack (arrived cell x)) da.1 da.2 x.factor) else none)=_
  have hc := PublicationExecution.episode_step_check cell (swapOwner cell) (start cell) (stride cell)
    PublicationExecution.nativeAssignment (round cell) (PublicationExecution.assigned_pair cell)
    (ModeExecution.pack (arrived cell x)) hx
  have hu := PublicationExecution.episode_update cell (swapOwner cell) (start cell) (stride cell)
    PublicationExecution.nativeAssignment (ready cell) (round cell) (PublicationExecution.assigned_pair cell)
    (ModeExecution.pack (arrived cell x)) () false x.factor
  change stepCheck (raw cell) _ (ModeExecution.pack (arrived cell x)) () false x.factor=true at hc
  change update (raw cell) _ (ready cell) (ModeExecution.pack (arrived cell x)) () false x.factor=
    ModeExecution.pack (stepState (arrived cell x).1 x.factor,(arrived cell x).2) at hu
  simp only [Option.bind_some,hc,ite_true,hu]
  cases cell <;> rfl

theorem actual_boundary (h : Factor) :
    firstEntry PublicationExecution.firstAcquisition PublicationExecution.nativeAssignment
      PublicationExecution.native_first_ready h h =
      some (initial PublicationExecution.secondAcquisition PublicationExecution.nativeAssignment
        PublicationExecution.native_second_ready h) := by
  rw [PublicationExecution.first_entry,PublicationExecution.second_initializer]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationReplay
