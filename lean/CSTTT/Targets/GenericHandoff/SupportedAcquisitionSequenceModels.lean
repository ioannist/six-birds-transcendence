import CSTTT.Targets.GenericHandoff.SupportedAcquisitionSequence
import CSTTT.Targets.GenericHandoff.RawCorridorSequenceModels
import CSTTT.Targets.GenericHandoff.SupportedSequenceCellReindex
import CSTTT.Targets.GenericHandoff.StagedCorridorSequenceModels

namespace CSTTT.TargetTheory.GenericHandoff.SupportedAcquisitionSequenceModels
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence RawCorridorSequenceModels
def natRaw (cell : Bool) (n : Nat) := { acquisition cell with initializer := fun _ => .literal n }
def run (n : Nat) : Registers Unit (fun _ => Nat) := fun _ => n

theorem nat_ready (cell : Bool) (n : Nat) (a : Assignment Bool Value) (ha : (a cell).isSome = true) :
    Ready (natRaw cell n) a := by
  have h := RawCorridorSequenceModels.ready cell a ha
  refine ⟨h.1,?_,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
  intro r k hk
  simp [natRaw,Expr.dependencies] at hk

theorem init_equation (cell : Bool) (n : Nat) (a : Assignment Bool Value) (h : Ready (natRaw cell n) a) :
    initial (natRaw cell n) a h () = run n := by
  funext r
  have he := RegisterInitialization.initial_eq (natRaw cell n).initializer a h.2.1 () r
  change some n = some (initial (natRaw cell n) a h () r) at he
  exact (Option.some.inj he).symm

theorem update_equation (cell : Bool) (n : Nat) (a : Assignment Bool Value) (h : Ready (natRaw cell n) a)
    (x : Registers Unit (fun _ => Nat)) : update (natRaw cell n) a h x () () () = run (x ()+1) := by
  funext r
  cases r
  have he := checked_execute_eq (natRaw cell n).execution.program a h.2.2.2.1 x ((),(),()) ()
  change some (x ()+1) = some (update (natRaw cell n) a h x () () () ()) at he
  exact (Option.some.inj he).symm

theorem receive_equation (cell : Bool) (n : Nat) (a : Assignment Bool Value) (h : Ready (natRaw cell n) a)
    (x : Registers Unit (fun _ => Nat)) : receive (natRaw cell n) a h x () () = x := by
  funext r
  have he := checked_execute_eq (natRaw cell n).receive a h.2.2.2.2 x ((),()) r
  change some (x r) = some (receive (natRaw cell n) a h x () () r) at he
  exact (Option.some.inj he).symm

theorem step_equation (cell : Bool) (n : Nat) (a : Assignment Bool Value) (x : Registers Unit (fun _ => Nat)) :
    stepCheck (natRaw cell n) a x () () () = true := by
  simp [stepCheck,supports,rows,natRaw,acquisition,Expr.eval]
  decide +kernel

theorem fold_equation (cell : Bool) (n : Nat) (a : Assignment Bool Value) (h : Ready (natRaw cell n) a)
    (x : Registers Unit (fun _ => Nat)) : supportedFold (natRaw cell n) a h x [((),(),())] = some (run (x ()+1)) := by
  simp only [supportedFold,step_equation,ite_true,update_equation]

theorem first_arrival_equation (cell : Bool) (n : Nat) (h : Ready (natRaw cell n) canonical) :
    firstArrival (natRaw cell n) canonical h () = some (run (n+1)) := by
  have hr : (natRaw cell n).routes.read canonical = some (fun _ => ⟨(),[false,true]⟩) := by
    cases cell <;> rfl
  have hh : (natRaw cell n).histories.read canonical = some (fun _ => [((),(),())]) := rfl
  simp [firstArrival,hr,init_equation,fromStart,hh,fold_equation,receive_equation,run]

theorem first_entry_equation (cell : Bool) (n : Nat) (h : Ready (natRaw cell n) canonical) :
    firstEntry (natRaw cell n) canonical h () () = some (run (n+2)) := by
  have hr : (natRaw cell n).routes.read canonical = some (fun _ => ⟨(),[false,true]⟩) := by
    cases cell <;> rfl
  simp only [firstEntry,first_arrival_equation,postExit,hr]
  change (some ((),())).bind (fun da => if stepCheck (natRaw cell n) canonical (run (n+1)) da.1 da.2 () then
    some (update (natRaw cell n) canonical h (run (n+1)) da.1 da.2 ()) else none) = _
  simp only [Option.bind_some,step_equation,ite_true,update_equation]
  rfl


def firstRaw := natRaw false 0
def secondRaw := natRaw true 2
def wrongInitial := natRaw true 0
def boundary : (k : Unit) → Expr Bool Value Unit (fun _ => Nat) Unit Nat := fun _ => .register ()
theorem boundary_ready (a : Assignment Bool Value) : RegisterSubstitution.Ready boundary a := by
  intro r k hk; simp [boundary,Expr.dependencies] at hk

theorem boundary_equation (a : Assignment Bool Value) (hb : RegisterSubstitution.Ready boundary a)
    (x : Registers Unit (fun _ => Nat)) : RegisterSubstitution.translate boundary a hb x () = x := by
  funext r
  cases r
  have he := RegisterSubstitution.translation_equation boundary a hb x () ()
  change some (x ()) = some (RegisterSubstitution.translate boundary a hb x () ()) at he
  exact (Option.some.inj he).symm

theorem from_start_equation (cell : Bool) (n : Nat) (h : Ready (natRaw cell n) canonical)
    (x : Registers Unit (fun _ => Nat)) :
    fromStart (natRaw cell n) canonical h x () = some (run (x ()+1)) := by
  have hr : (natRaw cell n).routes.read canonical = some (fun _ => ⟨(),[false,true]⟩) := by cases cell <;> rfl
  have hh : (natRaw cell n).histories.read canonical = some (fun _ => [((),(),())]) := rfl
  simp [fromStart,hr,hh,fold_equation,receive_equation]

theorem next_arrival_equation (n : Nat) (hf : Ready firstRaw canonical) (hs : Ready (natRaw true n) canonical)
    (hb : RegisterSubstitution.Ready boundary canonical) :
    nextArrival firstRaw (natRaw true n) boundary canonical hf hs hb () () () = some (run 3) := by
  change (firstEntry (natRaw false 0) canonical hf () ()).bind
    (fun actual => fromStart (natRaw true n) canonical hs (RegisterSubstitution.translate boundary canonical hb actual ()) ()) = _
  rw [first_entry_equation]
  simp [boundary_equation,from_start_equation,run]

theorem next_entry_equation (n : Nat) (hf : Ready firstRaw canonical) (hs : Ready (natRaw true n) canonical)
    (hb : RegisterSubstitution.Ready boundary canonical) :
    nextEntry firstRaw (natRaw true n) boundary canonical hf hs hb () () () () = some (run 4) := by
  simp only [nextEntry,next_arrival_equation]
  have hr : (natRaw true n).routes.read canonical = some (fun _ => ⟨(),[false,true]⟩) := rfl
  simp only [postExit,hr]
  change (some ((),())).bind (fun da => if stepCheck (natRaw true n) canonical (run 3) da.1 da.2 () then
    some (update (natRaw true n) canonical hs (run 3) da.1 da.2 ()) else none) = _
  simp only [Option.bind_some,step_equation,ite_true,update_equation]
  rfl

theorem left_route_check : RouteCheck left.schema firstRaw canonical () := by
  have hrid : () ∈ left.schema.routes := by change () ∈ [()]; simp
  have hc := left_view_check.2.2.2.2.2.2 () hrid
  refine ⟨(fun _ => [((),(),())]),leftInput.routes,leftInput.events,leftInput.realized,leftInput.receiver,
    rfl,rfl,rfl,rfl,rfl,hrid,hc.1,hc.2.1,hc.2.2.1⟩

theorem right_route_check (n : Nat) : RouteCheck right.schema (natRaw true n) canonical () := by
  have hrid : () ∈ right.schema.routes := by change () ∈ [()]; simp
  have hc := right_view_check.2.2.2.2.2.2 () hrid
  refine ⟨(fun _ => [((),(),())]),rightInput.routes,rightInput.events,rightInput.realized,rightInput.receiver,
    rfl,rfl,rfl,rfl,rfl,hrid,hc.1,hc.2.1,hc.2.2.1⟩

theorem domain_check (cell : Bool) (n : Nat) (source target offset : Nat) :
    DomainCheck (schema source target offset) (natRaw cell n) := by
  simp [DomainCheck,schema,natRaw,acquisition,stageList,Fin.forall_fin_succ]

theorem response_check (cell : Bool) (n : Nat) (a : Assignment Bool Value) : ResponseCheck (natRaw cell n) a () () := by
  intro arrived routes hr
  refine ⟨((),()),rfl,by simp [natRaw,acquisition],by simp [natRaw,acquisition],?_,?_⟩
  · refine ⟨?_,by change (1 : Rat)+0 = 1; decide +kernel,(),1,by simp [rows,natRaw,acquisition,Expr.eval],by decide +kernel⟩
    intro e he
    have he' : e = ((),(1:Rat)) := by simpa [rows,natRaw,acquisition,Expr.eval] using he
    subst e
    decide +kernel
  · exact ⟨1,by simp [rows,natRaw,acquisition,Expr.eval],by decide +kernel⟩

theorem middle_initial (hf : Ready firstRaw canonical) (hs : Ready secondRaw canonical)
    (hb : RegisterSubstitution.Ready boundary canonical) (actual : Registers Unit (fun _ => Nat))
    (routes : Unit → AcquisitionExecution.Route Unit Bool)
    (he : firstEntry firstRaw canonical hf () () = some actual)
    (_hr : secondRaw.routes.read canonical = some routes) :
    RegisterSubstitution.translate boundary canonical hb actual () = initial secondRaw canonical hs (routes ()).history := by
  have hfirst : some (run 2) = some actual := (first_entry_equation false 0 hf).symm.trans he
  have eq := Option.some.inj hfirst
  subst actual
  cases hhist : (routes ()).history
  rw [boundary_equation]
  exact (init_equation true 2 canonical hs).symm

theorem positive_checked (hf : Ready firstRaw canonical) (hs : Ready secondRaw canonical)
    (hb : RegisterSubstitution.Ready boundary canonical) :
    CheckedAt firstRaw secondRaw boundary left.schema right.schema canonical hf hs hb () () () () := by
  constructor
  · exact domain_check false 0 17 55 0
  · exact domain_check true 2 55 101 2
  · exact left_route_check
  · exact right_route_check 2
  · intro histories routes hh hr
    have hh' : (fun _ => [((),(),())]) = histories := Option.some.inj hh
    have hr' : leftInput.routes = routes := Option.some.inj hr
    subst histories; subst routes
    apply history_execution_checked firstRaw canonical hf
    exact (fold_some_iff firstRaw canonical hf _ _ [((),(),())]).mp (fold_equation false 0 canonical hf _)
  · intro actual histories routes he hh hr
    have hh' : (fun _ => [((),(),())]) = histories := Option.some.inj hh
    have hr' : rightInput.routes = routes := Option.some.inj hr
    subst histories; subst routes
    apply history_execution_checked secondRaw canonical hs
    exact (fold_some_iff secondRaw canonical hs _ _ [((),(),())]).mp (fold_equation true 2 canonical hs _)
  · exact response_check false 0 canonical
  · exact response_check true 2 canonical
  · exact middle_initial hf hs hb

theorem positive : Readout firstRaw secondRaw boundary left.schema right.schema canonical () () () () :=
  constructs firstRaw secondRaw boundary left.schema right.schema canonical
    (nat_ready false 0 canonical rfl) (nat_ready true 2 canonical rfl) (boundary_ready canonical)
    () () () () (positive_checked _ _ _)

theorem wrong_initial_no_readout :
    ¬ Readout firstRaw wrongInitial boundary left.schema right.schema canonical () () () () := by
  rintro ⟨hf,hs,hb,before,after,hbe,_,_,_,hmid⟩
  have hfirst : some (run 2) = some before := (first_entry_equation false 0 hf).symm.trans hbe
  have eq := Option.some.inj hfirst
  subst before
  have hm := hmid rightInput.routes rfl
  change RegisterSubstitution.translate boundary canonical hb (run 2) () = initial (natRaw true 0) canonical hs () at hm
  rw [boundary_equation,init_equation] at hm
  have bad := congrFun hm ()
  change 2 = 0 at bad
  contradiction

theorem wrong_initial_not_arrival (hf : Ready firstRaw canonical) (hs : Ready wrongInitial canonical)
    (hb : RegisterSubstitution.Ready boundary canonical) :
    nextArrival firstRaw wrongInitial boundary canonical hf hs hb () () () = some (run 3) ∧
    ¬ Arrival right.schema wrongInitial canonical hs () (run 3) := by
  refine ⟨next_arrival_equation 0 hf hs hb,?_⟩
  intro ha
  have he := first_arrival_complete right.schema wrongInitial canonical hs () (run 3) ha
  have hv := first_arrival_equation true 0 hs
  have eq := Option.some.inj (hv.symm.trans he)
  have bad := congrFun eq ()
  change 1 = 3 at bad
  contradiction



def zeroWeight (cell : Bool) (n : Nat) :=
  {natRaw cell n with execution := {(natRaw cell n).execution with row := .literal [((),0)]}}

theorem zero_ready (cell : Bool) (n : Nat) (a : Assignment Bool Value) (ha : (a cell).isSome = true) :
    Ready (zeroWeight cell n) a := by
  have h := nat_ready cell n a ha
  refine ⟨h.1,h.2.1,?_,h.2.2.2.1,h.2.2.2.2⟩
  intro k hk
  simp [zeroWeight,Expr.dependencies] at hk

theorem zero_fold (cell : Bool) (n : Nat) (a : Assignment Bool Value) (h : Ready (zeroWeight cell n) a)
    (x : Registers Unit (fun _ => Nat)) : supportedFold (zeroWeight cell n) a h x [((),(),())] = none := by
  apply unsupported_no_execution
  intro hp
  obtain ⟨w,hw,hp⟩ := hp
  have he : w = 0 := by simpa [rows,zeroWeight,natRaw,acquisition,Expr.eval] using hw
  subst w
  exact (by decide +kernel : ¬ (0 : Rat) < 0) hp

theorem zero_next_arrival (hf : Ready firstRaw canonical) (hs : Ready (zeroWeight true 2) canonical)
    (hb : RegisterSubstitution.Ready boundary canonical) :
    nextArrival firstRaw (zeroWeight true 2) boundary canonical hf hs hb () () () = none := by
  have hfirst : firstEntry firstRaw canonical hf () () = some (run 2) := first_entry_equation false 0 hf
  have hr : (zeroWeight true 2).routes.read canonical = some rightInput.routes := rfl
  have hh : (zeroWeight true 2).histories.read canonical = some (fun _ => [((),(),())]) := rfl
  simp [nextArrival,hfirst,fromStart,hr,hh,zero_fold]

theorem zero_next_no_readout :
    ¬ Readout firstRaw (zeroWeight true 2) boundary left.schema right.schema canonical () () () () := by
  apply next_none_no_readout
  intro hf hs hb
  rw [nextEntry,zero_next_arrival]
  exact post_exit_none _ _ _ _ _

theorem zero_first_entry (hf : Ready (zeroWeight false 0) canonical) :
    firstEntry (zeroWeight false 0) canonical hf () () = none := by
  have hr : (zeroWeight false 0).routes.read canonical = some leftInput.routes := rfl
  have hh : (zeroWeight false 0).histories.read canonical = some (fun _ => [((),(),())]) := rfl
  have hn : firstArrival (zeroWeight false 0) canonical hf () = none := by
    simp [firstArrival,fromStart,hr,hh,zero_fold]
  rw [firstEntry,hn]
  exact post_exit_none _ _ _ _ _

theorem zero_first_no_readout :
    ¬ Readout (zeroWeight false 0) secondRaw boundary left.schema right.schema canonical () () () () :=
  first_none_no_readout _ _ _ _ _ _ _ _ _ _ zero_first_entry

theorem missing_right_no_readout (a : Assignment Bool Value) (hm : a true = none) :
    ¬ Readout firstRaw secondRaw boundary left.schema right.schema a () () () () := by
  apply missing_second_no_readout _ _ _ _ _ _ _ _ _ _ true _ hm
  simp [secondRaw,natRaw,acquisition,Raw.dependencies,StaticView.dependencies,Expr.dependencies]

theorem initializer_anchor_essential :
    ¬ ∀ (hf : Ready firstRaw canonical) (hs : Ready wrongInitial canonical)
      (hb : RegisterSubstitution.Ready boundary canonical) arrived,
      nextArrival firstRaw wrongInitial boundary canonical hf hs hb () () () = some arrived →
        Arrival right.schema wrongInitial canonical hs () arrived := by
  intro universal
  let hf := nat_ready false 0 canonical rfl
  let hs := nat_ready true 0 canonical rfl
  let hb := boundary_ready canonical
  have pair := wrong_initial_not_arrival hf hs hb
  exact pair.2 (universal hf hs hb (run 3) pair.1)



open CellReindex
def select : Bool → Sum Bool Bool | false => .inl false | true => .inr true
def jointValue : (k : Bool) → StagedAssignmentSpan.JointValue Value Value (select k) → Value k
  | false => fun x => x
  | true => fun x => x
def stagedFirst := AcquisitionCellReindex.raw select jointValue firstRaw
def stagedSecond := AcquisitionCellReindex.raw select jointValue secondRaw
def stagedBoundary := fun k => CellReindex.expression select jointValue (boundary k)
def stagedSpan := StagedCorridorSequenceModels.span

theorem staged_pullback (a : Assignment Bool Value) :
    pullback select jointValue (stagedSpan a) = fun k => if k then
      StagedCorridorSequenceModels.finalCells a true else StagedCorridorSequenceModels.middle a false := by
  funext k
  cases k <;> simp [pullback,select,jointValue,stagedSpan,StagedCorridorSequenceModels.span,
    StagedAssignmentSpan.span,StagedAssignmentSpan.join,StagedCorridorSequenceModels.middle,StagedCorridorSequenceModels.finalCells]

theorem staged_actual_pullback :
    pullback select jointValue (stagedSpan StagedCorridorSequenceModels.original) = canonical := by
  rw [staged_pullback,StagedCorridorSequenceModels.actual_middle,StagedCorridorSequenceModels.actual_final]
  funext k
  cases k <;> rfl

theorem staged_readout_iff (a : Assignment Bool Value) :
    Readout stagedFirst stagedSecond stagedBoundary left.schema right.schema (stagedSpan a) () () () () ↔
      Readout firstRaw secondRaw boundary left.schema right.schema (pullback select jointValue (stagedSpan a)) () () () () :=
  SupportedSequenceCellReindex.readout_iff select jointValue firstRaw secondRaw boundary left.schema right.schema (stagedSpan a) () () () ()

theorem staged_positive :
    Readout stagedFirst stagedSecond stagedBoundary left.schema right.schema
      (stagedSpan StagedCorridorSequenceModels.original) () () () () := by
  rw [staged_readout_iff,staged_actual_pullback]
  exact positive

theorem staged_next_entry
    (hf : Ready stagedFirst (stagedSpan StagedCorridorSequenceModels.original))
    (hs : Ready stagedSecond (stagedSpan StagedCorridorSequenceModels.original))
    (hb : RegisterSubstitution.Ready stagedBoundary (stagedSpan StagedCorridorSequenceModels.original)) :
    nextEntry stagedFirst stagedSecond stagedBoundary (stagedSpan StagedCorridorSequenceModels.original) hf hs hb () () () () = some (run 4) := by
  have jf := (AcquisitionCellReindex.ready_iff select jointValue firstRaw _).mp hf
  have js := (AcquisitionCellReindex.ready_iff select jointValue secondRaw _).mp hs
  have jb := (SupportedSequenceCellReindex.boundary_ready_iff select jointValue boundary _).mp hb
  have he := SupportedSequenceCellReindex.next_entry_equation select jointValue firstRaw secondRaw boundary
    (stagedSpan StagedCorridorSequenceModels.original) hf hs hb jf js jb () () () ()
  have value : ∀ (a : Assignment Bool Value) (jf : Ready firstRaw a) (js : Ready secondRaw a)
      (jb : RegisterSubstitution.Ready boundary a), a = canonical →
      nextEntry firstRaw secondRaw boundary a jf js jb () () () () = some (run 4) := by
    intro a jf js jb eq
    subst a
    exact next_entry_equation 2 jf js jb
  exact he.trans (value _ jf js jb staged_actual_pullback)

theorem staged_missing_final (a : Assignment Bool Value) :
    ¬ Readout stagedFirst stagedSecond stagedBoundary left.schema right.schema
      (put (stagedSpan a) (.inr true) none) () () () () := by
  apply missing_second_no_readout stagedFirst stagedSecond stagedBoundary left.schema right.schema
    (put (stagedSpan a) (.inr true) none) () () () () (.inr true) _ (put_same (stagedSpan a) (.inr true) none)
  change Sum.inr true ∈ (AcquisitionCellReindex.raw select jointValue secondRaw).dependencies
  rw [AcquisitionCellReindex.dependencies]
  simp [secondRaw,natRaw,acquisition,Raw.dependencies,StaticView.dependencies,Expr.dependencies,select]



/-- Normalized two-outcome control: the assigned true branch has zero weight,
while a different false history is supported. The interpreter follows the
assigned history and does not substitute the productive alternative. -/
def normalizedBranch : Raw Bool Value Unit (fun _ => Nat) Unit Unit Bool LocalStage Bool Unit Unit where
  initializer := fun _ => .literal 0
  histories := ⟨.literal (fun _ => [((),(),true)])⟩
  routes := (acquisition false).routes
  events := (acquisition false).events
  realized := (acquisition false).realized
  receiver := (acquisition false).receiver
  receive := (acquisition false).receive
  arrivalResponse := (acquisition false).arrivalResponse
  execution := ⟨[()],[()],[false,true],.literal [(false,1),(true,0)],fun _ => .map Nat.succ (.register ())⟩

theorem normalized_branch_ready (a : Assignment Bool Value) (ha : (a false).isSome = true) : Ready normalizedBranch a := by
  have h := RawCorridorSequenceModels.ready false a ha
  refine ⟨h.1,h.2.1,?_,?_,h.2.2.2.2⟩
  · intro k hk; simp [normalizedBranch,Expr.dependencies] at hk
  · intro r k hk; simp [normalizedBranch,Expr.dependencies] at hk

theorem normalized_branch_row (a : Assignment Bool Value) (x : Registers Unit (fun _ => Nat)) :
    StrategyGame.Normalized (rows normalizedBranch a) x () () := by
  refine ⟨?_,by change (1 : Rat)+(0+0) = 1; decide +kernel, false,1,by simp [rows,normalizedBranch,Expr.eval],by decide +kernel⟩
  intro e he
  have cases' : e = (false,(1:Rat)) ∨ e = (true,(0:Rat)) := by
    simpa [rows,normalizedBranch,Expr.eval] using he
  rcases cases' with rfl | rfl <;> decide +kernel

theorem normalized_branch_rejects (a : Assignment Bool Value) (h : Ready normalizedBranch a)
    (x : Registers Unit (fun _ => Nat)) : supportedFold normalizedBranch a h x [((),(),true)] = none := by
  apply unsupported_no_execution
  rintro ⟨w,hw,hp⟩
  have he : w = 0 := by simpa [rows,normalizedBranch,Expr.eval] using hw
  subst w
  exact (by decide +kernel : ¬ (0 : Rat) < 0) hp

theorem normalized_branch_has_alternative (a : Assignment Bool Value) (h : Ready normalizedBranch a)
    (x : Registers Unit (fun _ => Nat)) :
    supportedFold normalizedBranch a h x [((),(),false)] = some (update normalizedBranch a h x () () false) := by
  have hp : stepCheck normalizedBranch a x () () false = true := by
    simp [stepCheck,supports,rows,normalizedBranch,Expr.eval]
    decide +kernel
  simp [supportedFold,hp]

theorem normalized_branch_first_none (h : Ready normalizedBranch canonical) (o : Bool) :
    firstEntry normalizedBranch canonical h () o = none := by
  have hr : normalizedBranch.routes.read canonical = some leftInput.routes := rfl
  have hh : normalizedBranch.histories.read canonical = some (fun _ => [((),(),true)]) := rfl
  have ha : firstArrival normalizedBranch canonical h () = none := by
    simp [firstArrival,fromStart,hr,hh,normalized_branch_rejects]
  rw [firstEntry,ha]
  exact post_exit_none _ _ _ _ _

theorem normalized_branch_no_readout (o u : Bool) :
    ¬ Readout normalizedBranch normalizedBranch boundary left.schema right.schema canonical () () o u :=
  first_none_no_readout _ _ _ _ _ _ _ _ _ _ (fun h => normalized_branch_first_none h o)

end CSTTT.TargetTheory.GenericHandoff.SupportedAcquisitionSequenceModels
