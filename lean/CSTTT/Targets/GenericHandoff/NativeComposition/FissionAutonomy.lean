import CSTTT.Targets.GenericHandoff.NativeComposition.FissionResources

/-! Each branch has its actual named resource accounts AND charge owner.
Rows, updater, withdrawal, prices and controller are unchanged instructions;
the retained account is interpreted as201/202 in the branch's local context. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
open RegisterInterpreter PublicationReplay ModeExecution CSTTT.TransportTheory

def namedRuntime (branch : Bool) := resources true false (branchNames branch)
def namedCfg (branch : Bool) := resourceSchema false (branchNames branch)
theorem named_cfg_endpoints (branch : Bool) :
    (namedCfg branch).source=(⟨17⟩ : CarrierId) ∧ (namedCfg branch).target=(⟨branchTarget branch⟩ : CarrierId) := by
  cases branch <;> exact ⟨rfl,rfl⟩
theorem named_ready_iff (branch : Bool) (a : Assignment Owner MemoryValue) :
    ResourceRuntime.Ready (namedRuntime branch) a ↔ (a true).isSome=true := by
  constructor
  · intro h
    exact h.2.2 true (by simp [namedRuntime,resources,ResourceRuntime.Raw.readDependencies])
  · exact resources_ready true false (branchNames branch) a
theorem named_ready (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) : ResourceRuntime.Ready (namedRuntime branch) (PublicationComposition.native b) :=
  hb.resources true
def namedAccounts (branch : Bool) : Bool → ResourceRuntime.Account := fun res =>
  if res then ⟨some (⟨branchTarget branch⟩ : CarrierId),true,1⟩ else ⟨none,false,0⟩
def namedCharge (branch : Bool) : ResourceRuntime.Charge Bool :=
  ⟨⟨branchTarget branch⟩,[true],(fun r => if r then 1 else 0),(fun r => if r then 1 else 0)⟩

theorem named_target_accounts (branch : Bool) (h : Factor) (time : Nat) :
    (namedRuntime branch).accounts.eval PublicationResources.assignment (PublicationResources.run true h time) ()=
      some (namedAccounts branch) := by
  simp only [namedRuntime,resources,Expr.eval,PublicationResources.target_context,Option.map_some]
  cases branch <;> rfl
theorem named_target_charge (branch : Bool) (h : Factor) (time : Nat) (act : Bool) :
    (namedRuntime branch).charge.eval PublicationResources.assignment (PublicationResources.run true h time) ((),act)=
      some (namedCharge branch) := by
  simp only [namedRuntime,resources,Expr.eval,Expr.reenv_eval,PublicationResources.target_context,Option.map_some]
  cases branch <;> rfl
theorem named_target_closed (branch : Bool) (h : Factor) (time : Nat) :
    ResourceRuntime.ResourceClosed (namedCfg branch) (namedRuntime branch)
      PublicationResources.assignment (PublicationResources.run true h time) := by
  refine ⟨namedAccounts branch,[true],withdrawal,named_target_accounts branch h time,rfl,
    PublicationResources.withdrawn_reader true,PublicationResources.target_absence true _,
    PublicationResources.target_writer_eval true h time,by decide +kernel +revert,?_,?_,?_⟩
  · intro res hr; exact hr
  · intro res hr
    have he : res=true := by simpa using hr
    subst res
    refine ⟨?_,rfl,by decide +kernel +revert⟩
    cases branch <;> rfl
  · intro res hr
    have he : res=false := by simpa [withdrawal] using hr
    subst res; rfl
theorem named_target_legal (branch : Bool) (h : Factor) (time : Nat) :
    ResourceRuntime.Legal (namedCfg branch) (namedRuntime branch)
      PublicationResources.assignment (PublicationResources.run true h time) () false := by
  refine ⟨by simp [namedRuntime,resources,execution],by simp [namedRuntime,resources,execution],
    namedAccounts branch,[true],namedCharge branch,withdrawal,named_target_accounts branch h time,rfl,
    named_target_charge branch h time false,PublicationResources.withdrawn_reader true,?_,by decide +kernel +revert,
    ?_,?_,?_,?_⟩
  · cases branch <;> rfl
  · intro res hr; exact hr
  · intro res hr; exact hr
  · intro res hr
    have he : res=true := by simpa [namedCharge] using hr
    subst res; decide +kernel +revert
  · intro res hr
    have he : res=true := by simpa [namedCharge] using hr
    subst res
    refine ⟨?_,rfl,by decide +kernel +revert,by decide +kernel +revert⟩
    cases branch <;> rfl

theorem named_target_update (branch : Bool) (h : Factor) (time : Nat) :
    ResourceRuntime.update (namedRuntime branch) PublicationResources.assignment (PublicationResources.ready true)
      (PublicationResources.run true h time) () false h=PublicationResources.run true h (time+1) :=
  PublicationResources.target_update true h time

theorem named_target_step (branch : Bool) (h : Factor) (time : Nat) :
    ResourceRuntime.StepLaw (namedCfg branch) (namedRuntime branch) PublicationResources.assignment
      (PublicationResources.ready true) (PublicationResources.run true h time) () false h := by
  unfold ResourceRuntime.StepLaw
  rw [named_target_update]
  refine ⟨named_target_closed branch h (time+1),namedAccounts branch,namedAccounts branch,namedCharge branch,
    ⟨1,1,1,1⟩,time,time,time,time,named_target_accounts branch h time,named_target_accounts branch h (time+1),
    named_target_charge branch h time false,rfl,by decide +kernel +revert,by decide +kernel +revert,by decide +kernel +revert,by decide +kernel +revert,?_,
    rfl,rfl,rfl,rfl,rfl,rfl,PublicationResources.target_record_eval true h time,
    PublicationResources.target_record_eval true h (time+1),rfl⟩
  intro res hr
  have he : res=true := by simpa [namedCharge] using hr
  subst res; rfl

def NamedControllerWins (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) : Prop :=
  (ResourceRuntime.DomainCheck (namedCfg branch) (namedRuntime branch) ∧
    ResourceRuntime.WithdrawalCheck (namedCfg branch) (namedRuntime branch) (PublicationComposition.native b)) ∧
  (∃ x, PublicationComposition.entries b hb true x) ∧
  ∀ entry, PublicationComposition.entries b hb true entry → ∀ x past,
    StrategyGame.Play (ResourceRuntime.rows (namedRuntime branch) (PublicationComposition.native b))
      (ResourceRuntime.update (namedRuntime branch) (PublicationComposition.native b) (named_ready branch b hb))
      PublicationResources.safeController entry (x::past) →
    PublicationComposition.packageAt b true x ∧
    ResourceRuntime.ResourceClosed (namedCfg branch) (namedRuntime branch) (PublicationComposition.native b) x ∧
    ∀ d, ResourceRuntime.Legal (namedCfg branch) (namedRuntime branch) (PublicationComposition.native b) x d
      (PublicationResources.safeController (x::past) d) ∧
      StrategyGame.Normalized (ResourceRuntime.rows (namedRuntime branch) (PublicationComposition.native b)) x d
        (PublicationResources.safeController (x::past) d) ∧
      ∀ o, StrategyGame.PositiveSupport (ResourceRuntime.rows (namedRuntime branch) (PublicationComposition.native b))
        x d (PublicationResources.safeController (x::past) d) o →
        ResourceRuntime.StepLaw (namedCfg branch) (namedRuntime branch) (PublicationComposition.native b)
          (named_ready branch b hb) x d (PublicationResources.safeController (x::past) d) o

theorem canonical_named_controller (branch : Bool) :
    NamedControllerWins branch NativePackageBundle.canonical PublicationComposition.canonical_ready := by
  refine ⟨⟨PublicationResources.domain true,PublicationResources.withdrawal_check true⟩,
    PublicationResources.entries_nonempty true,?_⟩
  intro entry he x past hp
  have parent := (PublicationComposition.canonical_controller true).2.2 entry he x past hp
  obtain ⟨h,time,rfl⟩ := PublicationResources.every_safe_play_inside true entry he _ hp x past rfl
  refine ⟨parent.1,named_target_closed branch h time,?_⟩
  intro d; cases d
  refine ⟨named_target_legal branch h time,PublicationResources.target_normalized true h time,?_⟩
  intro o ho
  have he := (PublicationResources.target_positive_unique true h o time).mp ho
  subst o
  exact named_target_step branch h time

theorem named_controller_game (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (hw : NamedControllerWins branch b hb) :
    StrategyGame.GameReadout (ResourceRuntime.rows (namedRuntime branch) (PublicationComposition.native b))
      (ResourceRuntime.update (namedRuntime branch) (PublicationComposition.native b) (named_ready branch b hb))
      (PublicationComposition.entries b hb true)
      (ResourceRuntime.DomainCheck (namedCfg branch) (namedRuntime branch) ∧
        ResourceRuntime.WithdrawalCheck (namedCfg branch) (namedRuntime branch) (PublicationComposition.native b))
      (PublicationComposition.packageAt b true)
      (ResourceRuntime.ResourceClosed (namedCfg branch) (namedRuntime branch) (PublicationComposition.native b))
      (ResourceRuntime.Legal (namedCfg branch) (namedRuntime branch) (PublicationComposition.native b))
      (ResourceRuntime.StepLaw (namedCfg branch) (namedRuntime branch) (PublicationComposition.native b)
        (named_ready branch b hb)) := ⟨hw.1,hw.2.1,PublicationResources.safeController,hw.2.2⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
