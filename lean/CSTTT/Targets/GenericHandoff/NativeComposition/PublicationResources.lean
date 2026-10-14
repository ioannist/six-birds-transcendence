import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationTrace
import CSTTT.Targets.GenericHandoff.NativeComposition.Resources

/-! Both actual target entries admit the same explicit safe controller. All
six removed resource roles alias the false account; the true account is the
retained target recharge account. The complete structural dispatcher package,
with its disclosed C4–C7 grades, is checked on every generated continuation. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationResources
open RegisterInterpreter ModeExecution PublicationReplay

def runtime (cell : Owner) := resources cell (swapOwner cell) (names cell)
def cfg (cell : Owner) := resourceSchema (swapOwner cell) (names cell)
abbrev assignment := PublicationExecution.nativeAssignment
def run (cell : Owner) (h : Factor) (time : Nat) := PublicationExecution.snapshot h (2*copies cell) time cell
def accounts (cell : Owner) : Bool → ResourceRuntime.Account := fun r =>
  if r then ⟨some (names cell cell),true,1⟩ else ⟨none,false,0⟩
def charge (cell : Owner) : ResourceRuntime.Charge Bool :=
  ⟨names cell cell,[true],(fun r => if r then 1 else 0),(fun r => if r then 1 else 0)⟩
theorem ready (cell : Owner) : ResourceRuntime.Ready (runtime cell) assignment :=
  resources_ready cell (swapOwner cell) (names cell) assignment (by cases cell <;> rfl)
theorem ready_iff (cell : Owner) (a : Assignment Owner MemoryValue) :
    ResourceRuntime.Ready (runtime cell) a ↔ (a cell).isSome=true := by
  constructor
  · intro h
    exact h.2.2 cell (by simp [runtime,resources,ResourceRuntime.Raw.readDependencies])
  · exact resources_ready cell (swapOwner cell) (names cell) a
def entries (cell : Owner) := AcquisitionExecution.Entry (PublicationReplay.schema cell)
  (PublicationReplay.raw cell) assignment (PublicationReplay.ready cell)
def Inside (cell : Owner) (x : ModeExecution.Registers) : Prop := ∃ h time, x=run cell h time
def packageAt (cell : Owner) (x : ModeExecution.Registers) : Prop :=
  (NativeClosedPackage.package cell false).accept NativePackageBundle.canonical ∧
    ResourceRuntime.Inside (cfg cell) (runtime cell) assignment x
def safeController : StrategyGame.Strategy ModeExecution.Registers Unit Bool := fun _ _ => false

theorem target_context (cell : Owner) (h : Factor) (time : Nat) :
    (context cell (swapOwner cell)).eval assignment (run cell h time) ()=
      some ((PublicationExecution.episodePair (round cell)).1.temporal,run cell h time ()) := by
  have he := context_evaluation cell (swapOwner cell) assignment (PublicationExecution.episodePair (round cell))
    (PublicationExecution.assigned_pair cell) (run cell h time)
  simpa only [run,PublicationExecution.snapshot,pack,swap_owner_involution,ite_true] using he
theorem target_accounts (cell : Owner) (h : Factor) (time : Nat) :
    (runtime cell).accounts.eval assignment (run cell h time) ()=some (accounts cell) := by
  simp only [runtime,resources,Expr.eval,target_context,Option.map_some]
  cases cell <;> rfl
theorem target_charge (cell : Owner) (h : Factor) (time : Nat) (d : Unit) (act : Bool) :
    (runtime cell).charge.eval assignment (run cell h time) (d,act)=some (charge cell) := by
  simp only [runtime,resources,Expr.eval,Expr.reenv_eval,target_context,Option.map_some]
  cases cell <;> rfl
theorem target_writer (cell : Owner) (h : Factor) :
    TemporalFactorRules.writer (factorSchema (swapOwner cell)) (PublicationExecution.episodePair (round cell)).1.temporal
      (List.replicate (2*copies cell) h,[false,true])=true := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
theorem target_writer_eval (cell : Owner) (h : Factor) (time : Nat) :
    (runtime cell).writer.eval assignment (run cell h time) ()=some true := by
  simp only [runtime,resources,Expr.eval,target_context,Option.map_some]
  exact congrArg some (target_writer cell h)
theorem target_record_eval (cell : Owner) (h : Factor) (time : Nat) :
    (runtime cell).record.eval assignment (run cell h time) ()=some time := by
  simp only [runtime,resources,Expr.eval,target_context,Option.map_some]
  change some (if true && TemporalFactorRules.writer (factorSchema (swapOwner cell))
    (PublicationExecution.episodePair (round cell)).1.temporal
    (List.replicate (2*copies cell) h,[false,true]) then time else 0)=some time
  rw [target_writer]
  rfl
theorem withdrawn_reader (cell : Owner) : (runtime cell).withdrawal.read assignment=some withdrawal := by
  cases cell <;> rfl
theorem target_absence (cell : Owner) (x : Frame.State) :
    (runtime cell).sourcePresent.eval assignment (pack (x,cell)) ()=some false := by
  cases cell <;> rfl

theorem target_resource_closed (cell : Owner) (h : Factor) (time : Nat) :
    ResourceRuntime.ResourceClosed (cfg cell) (runtime cell) assignment (run cell h time) := by
  refine ⟨accounts cell,[true],withdrawal,target_accounts cell h time,rfl,withdrawn_reader cell,?_,
    target_writer_eval cell h time,by decide +kernel +revert,?_,?_,?_⟩
  · exact target_absence cell _
  · intro res hr; exact hr
  · intro res hr
    have he : res=true := by simpa using hr
    subst res
    refine ⟨?_,rfl,by decide +kernel +revert⟩
    cases cell <;> rfl
  · intro res hr
    have he : res=false := by simpa [withdrawal] using hr
    subst res; rfl
theorem target_legal (cell : Owner) (h : Factor) (time : Nat) :
    ResourceRuntime.Legal (cfg cell) (runtime cell) assignment (run cell h time) () false := by
  refine ⟨by simp [runtime,resources,execution],by simp [runtime,resources,execution],
    accounts cell,[true],charge cell,withdrawal,target_accounts cell h time,rfl,
    target_charge cell h time () false,withdrawn_reader cell,?_,by decide +kernel +revert,?_,?_,?_,?_⟩
  · cases cell <;> rfl
  · intro res hr; exact hr
  · intro res hr; exact hr
  · intro res hr
    have he : res=true := by simpa [charge] using hr
    subst res; decide +kernel +revert
  · intro res hr
    have he : res=true := by simpa [charge] using hr
    subst res
    refine ⟨?_,rfl,by decide +kernel +revert,by decide +kernel +revert⟩
    cases cell <;> rfl

theorem target_update (cell : Owner) (h : Factor) (time : Nat) :
    ResourceRuntime.update (runtime cell) assignment (ready cell) (run cell h time) () false h=
      run cell h (time+1) := by
  funext r
  have he := checked_execute_eq (runtime cell).execution.program assignment (ready cell).2.1
    (run cell h time) ((),false,h) r
  simp only [execute,runtime,resources,execution] at he
  rw [mode_update_evaluation cell (swapOwner cell) assignment (PublicationExecution.episodePair (round cell))
    (PublicationExecution.assigned_pair cell)] at he
  simp only [run,PublicationExecution.snapshot,pack,swap_owner_involution,ite_true,
    PublicationExecution.episodePair,PublicationExecution.round_update] at he
  exact (Option.some.inj he).symm
theorem target_step_law (cell : Owner) (h : Factor) (time : Nat) :
    ResourceRuntime.StepLaw (cfg cell) (runtime cell) assignment (ready cell) (run cell h time) () false h := by
  unfold ResourceRuntime.StepLaw
  rw [target_update]
  refine ⟨target_resource_closed cell h (time+1),accounts cell,accounts cell,charge cell,⟨1,1,1,1⟩,
    time,time,time,time,target_accounts cell h time,target_accounts cell h (time+1),
    target_charge cell h time () false,rfl,by decide +kernel +revert,by decide +kernel +revert,by decide +kernel +revert,by decide +kernel +revert,?_,
    rfl,rfl,rfl,rfl,rfl,rfl,target_record_eval cell h time,target_record_eval cell h (time+1),rfl⟩
  intro res hr
  have he : res=true := by simpa [charge] using hr
  subst res; rfl

theorem target_normalized (cell : Owner) (h : Factor) (time : Nat) :
    StrategyGame.Normalized (ResourceRuntime.rows (runtime cell) assignment) (run cell h time) () false := by
  exact PublicationExecution.snapshot_normalized cell (swapOwner cell) (start cell) (stride cell) (round cell)
    assignment (PublicationExecution.assigned_pair cell) h (2*copies cell) time cell
theorem target_positive_unique (cell : Owner) (h o : Factor) (time : Nat) :
    StrategyGame.PositiveSupport (ResourceRuntime.rows (runtime cell) assignment) (run cell h time) () false o ↔ o=h := by
  simpa only [run,PublicationExecution.snapshot,pack,true_and] using
    PublicationExecution.safe_positive_unique cell (swapOwner cell) (start cell) (stride cell)
      assignment (round cell) (PublicationExecution.assigned_pair cell) (run cell h time) () o
theorem entries_inside (cell : Owner) (x : ModeExecution.Registers) (hx : entries cell x) : Inside cell x := by
  cases cell
  · obtain ⟨h,hh⟩ := PublicationExecution.all_second_entries (PublicationReplay.ready false) x hx
    exact ⟨h,6,hh⟩
  · obtain ⟨h,hh⟩ := PublicationExecution.all_first_entries (PublicationReplay.ready true) x hx
    exact ⟨h,2,hh⟩
theorem entries_nonempty (cell : Owner) : ∃ x, entries cell x :=
  ⟨_,PublicationFuture.semantic_root_entry cell (false,false,false)⟩
theorem package_inside (cell : Owner) (x : ModeExecution.Registers) (hx : Inside cell x) : packageAt cell x := by
  obtain ⟨h,time,rfl⟩ := hx
  exact ⟨NativeClosedPackage.actual_package cell false,h,factor_mem h,rfl⟩

theorem domain (cell : Owner) : ResourceRuntime.DomainCheck (cfg cell) (runtime cell) := by
  have hn : factors≠[] := by decide +kernel +revert
  have hb : ([false,true] : List Bool)≠[] := by decide +kernel +revert
  have hi : ∀ r : Bool, r∈[false,true] := by decide +kernel +revert
  have hu : ∀ d : Unit, d∈[()] := by intro d; cases d; decide +kernel +revert
  have hd : ([()] : List Unit)≠[] := by decide +kernel +revert
  exact ⟨hn,hb,hd,hu,hi,factor_mem,factor_mem,hi⟩
theorem withdrawal_check (cell : Owner) : ResourceRuntime.WithdrawalCheck (cfg cell) (runtime cell) assignment := by
  refine ⟨withdrawal,withdrawn_reader cell,(fun _ h => h),(fun _ h => h),?_,?_,?_,?_⟩
  · intro role _ res hr; exact hr
  · intro res hr
    have he : res=false := by simpa [withdrawal] using hr
    subst res; decide +kernel +revert
  · intro res hr
    have he : res=true := by simpa [withdrawal] using hr
    subst res; decide +kernel +revert
  · intro res hr
    have he : res=false := by simpa [withdrawal] using hr
    subst res; decide +kernel +revert

theorem every_safe_play_inside (cell : Owner) (entry : ModeExecution.Registers) (he : entries cell entry)
    (history : List ModeExecution.Registers)
    (hp : StrategyGame.Play (ResourceRuntime.rows (runtime cell) assignment)
      (ResourceRuntime.update (runtime cell) assignment (ready cell)) safeController entry history) :
    ∀ x past, history=x::past → Inside cell x := by
  induction hp with
  | initial =>
    intro x past hx; cases hx; exact entries_inside cell entry he
  | @step x past earlier d o supported ih =>
    intro next rest hn; cases hn
    obtain ⟨h,time,hx⟩ := ih x past rfl
    subst x
    cases d
    have ho := (target_positive_unique cell h o time).mp supported
    subst o
    exact ⟨h,time+1,target_update cell h time⟩

/-- This complete-package game supplies an explicit controller that is literally
the same function at both hops, rather than an arbitrary existential selector. -/
theorem package_operational_autonomy (cell : Owner) :
    StrategyGame.GameReadout (ResourceRuntime.rows (runtime cell) assignment)
      (ResourceRuntime.update (runtime cell) assignment (ready cell)) (entries cell)
      (ResourceRuntime.DomainCheck (cfg cell) (runtime cell) ∧ ResourceRuntime.WithdrawalCheck (cfg cell) (runtime cell) assignment)
      (packageAt cell) (ResourceRuntime.ResourceClosed (cfg cell) (runtime cell) assignment)
      (ResourceRuntime.Legal (cfg cell) (runtime cell) assignment)
      (ResourceRuntime.StepLaw (cfg cell) (runtime cell) assignment (ready cell)) := by
  refine ⟨⟨domain cell,withdrawal_check cell⟩,entries_nonempty cell,safeController,?_⟩
  intro entry he x past hp
  have hx := every_safe_play_inside cell entry he _ hp x past rfl
  refine ⟨package_inside cell x hx,?_,?_⟩
  · obtain ⟨h,time,rfl⟩ := hx; exact target_resource_closed cell h time
  · intro d; cases d
    obtain ⟨h,time,rfl⟩ := hx
    refine ⟨target_legal cell h time,target_normalized cell h time,?_⟩
    intro o ho
    have he := (target_positive_unique cell h o time).mp ho
    subst o
    exact target_step_law cell h time

theorem every_safe_play_source_absent (cell : Owner) (entry : ModeExecution.Registers) (he : entries cell entry)
    (x : ModeExecution.Registers) (past : List ModeExecution.Registers)
    (hp : StrategyGame.Play (ResourceRuntime.rows (runtime cell) assignment)
      (ResourceRuntime.update (runtime cell) assignment (ready cell)) safeController entry (x::past)) :
    (runtime cell).sourcePresent.eval assignment x ()=some false := by
  obtain ⟨h,time,rfl⟩ := every_safe_play_inside cell entry he _ hp x past rfl
  exact target_absence cell _

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationResources
