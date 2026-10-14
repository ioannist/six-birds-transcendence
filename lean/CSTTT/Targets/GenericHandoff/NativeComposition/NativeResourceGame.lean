import CSTTT.Targets.GenericHandoff.NativeComposition.NativeBoundary

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter
abbrev finalResources := resources false true secondNames
abbrev finalResourceSchema := resourceSchema true secondNames

theorem final_resources_ready : ResourceRuntime.Ready finalResources nativeAssignment :=
  resources_ready false true secondNames nativeAssignment rfl

def targetAccounts : Bool → ResourceRuntime.Account := fun r =>
  if r then ⟨some (secondNames false),true,1⟩ else ⟨none,false,0⟩
def targetCharge : ResourceRuntime.Charge Bool :=
  ⟨secondNames false,[true],(fun r => if r then 1 else 0),(fun r => if r then 1 else 0)⟩

theorem final_writer (h : Factor) :
    TemporalFactorRules.writer (factorSchema true) (roundInput 2).temporal (List.replicate 8 h,[false,true]) = true := by
  rcases h with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> rfl

theorem final_accounts (h : Factor) (time : Nat) :
    finalResources.accounts.eval nativeAssignment (snapshot h 8 time false) () = some targetAccounts := by
  exact actual_target_ownership false true secondNames nativeAssignment (episodePair 1) rfl _

theorem final_charge (h : Factor) (time : Nat) (d : Unit) (act : Bool) :
    finalResources.charge.eval nativeAssignment (snapshot h 8 time false) (d,act) = some targetCharge := by
  exact actual_target_charge false true secondNames nativeAssignment (episodePair 1) rfl _ d act

theorem final_context (h : Factor) (time : Nat) :
    (context false true).eval nativeAssignment (snapshot h 8 time false) () =
      some ((roundInput 2).temporal,snapshot h 8 time false ()) :=
  context_evaluation false true nativeAssignment (episodePair 1) rfl _

theorem final_writer_eval (h : Factor) (time : Nat) :
    finalResources.writer.eval nativeAssignment (snapshot h 8 time false) () = some true := by
  simp only [resources,Expr.eval,final_context,Option.map_some]
  exact congrArg some (final_writer h)

theorem final_record_eval (h : Factor) (time : Nat) :
    finalResources.record.eval nativeAssignment (snapshot h 8 time false) () = some time := by
  simp only [resources,Expr.eval,final_context,Option.map_some]
  rw [show (snapshot h 8 time false ()).1.residue=(List.replicate 8 h,[false,true]) from rfl,final_writer]
  rfl

theorem final_resource_closed (h : Factor) (time : Nat) :
    ResourceRuntime.ResourceClosed finalResourceSchema finalResources nativeAssignment (snapshot h 8 time false) := by
  refine ⟨targetAccounts,[true],withdrawal,final_accounts h time,rfl,rfl,rfl,
    final_writer_eval h time,by decide +kernel,?_,?_,?_⟩
  · intro res hr
    exact hr
  · intro res hr
    have he : res=true := by simpa using hr
    subst res
    exact ⟨rfl,rfl,by decide +kernel⟩
  · intro res hr
    have he : res=false := by simpa [withdrawal] using hr
    subst res
    rfl

theorem final_legal (h : Factor) (time : Nat) :
    ResourceRuntime.Legal finalResourceSchema finalResources nativeAssignment (snapshot h 8 time false) () false := by
  refine ⟨by simp [resources,execution],by simp [resources,execution],
    targetAccounts,[true],targetCharge,withdrawal,final_accounts h time,rfl,final_charge h time () false,rfl,rfl,
    by decide +kernel,?_,?_,?_,?_⟩
  · intro res hr; exact hr
  · intro res hr; exact hr
  · intro res hr
    have he : res=true := by simpa [targetCharge] using hr
    subst res; decide +kernel
  · intro res hr
    have he : res=true := by simpa [targetCharge] using hr
    subst res
    exact ⟨rfl,rfl,by decide +kernel,by decide +kernel⟩

theorem final_update (hr : ResourceRuntime.Ready finalResources nativeAssignment)
    (h : Factor) (time : Nat) :
    ResourceRuntime.update finalResources nativeAssignment hr (snapshot h 8 time false) () false h =
      snapshot h 8 (time+1) false := by
  funext r
  have he := checked_execute_eq finalResources.execution.program nativeAssignment hr.2.1
    (snapshot h 8 time false) ((),false,h) r
  simp only [execute,resources,execution] at he
  rw [mode_update_evaluation false true nativeAssignment (episodePair 1) rfl] at he
  simp only [snapshot,pack,swapOwner,ite_true,episodePair,round_update] at he
  exact (Option.some.inj he).symm

theorem final_step_law (hr : ResourceRuntime.Ready finalResources nativeAssignment)
    (h : Factor) (time : Nat) :
    ResourceRuntime.StepLaw finalResourceSchema finalResources nativeAssignment hr (snapshot h 8 time false) () false h := by
  unfold ResourceRuntime.StepLaw
  rw [final_update]
  refine ⟨final_resource_closed h (time+1),targetAccounts,targetAccounts,targetCharge,⟨1,1,1,1⟩,
    time,time,time,time,final_accounts h time,final_accounts h (time+1),final_charge h time () false,rfl,
    by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,?_,
    rfl,rfl,rfl,rfl,rfl,rfl,final_record_eval h time,final_record_eval h (time+1),rfl⟩
  intro res hr
  have he : res=true := by simpa [targetCharge] using hr
  subst res
  rfl

theorem final_resource_domain : ResourceRuntime.DomainCheck finalResourceSchema finalResources := by
  have hn : factors ≠ [] := by decide +kernel
  have hb : ([false,true] : List Bool) ≠ [] := by decide +kernel
  have hi : ∀ r : Bool, r ∈ [false,true] := by decide +kernel
  have hu : ∀ d : Unit, d ∈ [()] := by intro d; cases d; decide +kernel
  have hd : ([()] : List Unit) ≠ [] := by decide +kernel
  exact ⟨hn,hb,hd,hu,hi,factor_mem,factor_mem,hi⟩

theorem final_withdrawal_check : ResourceRuntime.WithdrawalCheck finalResourceSchema finalResources nativeAssignment := by
  refine ⟨withdrawal,rfl,(fun _ h => h),(fun _ h => h),?_,?_,?_,?_⟩
  · intro role _ res hr; exact hr
  · intro res hr
    have he : res=false := by simpa [withdrawal] using hr
    subst res
    decide +kernel
  · intro res hr
    have he : res=true := by simpa [withdrawal] using hr
    subst res
    decide +kernel
  · intro res hr
    have he : res=false := by simpa [withdrawal] using hr
    subst res
    decide +kernel

/-- The entries are the existing semantic acquisition entries, including every
positive branch. The auxiliary invariant describes computed target runs only. -/
theorem final_resource_certificate (hr : ResourceRuntime.Ready finalResources nativeAssignment)
    (hs : AcquisitionExecution.Ready secondAcquisition nativeAssignment) :
    Nonempty (ResourceRuntime.Certificate finalResourceSchema finalResources nativeAssignment hr
      (AcquisitionExecution.Entry secondSchema secondAcquisition nativeAssignment hs)) := by
  refine ⟨{ inside := fun x => ∃ h time, x=snapshot h 8 time false
            withdrawn := ⟨final_resource_domain,final_withdrawal_check⟩
            entriesNonempty := ⟨_,NativeComposition.ModeExecution.second_semantic_entry hs (false,false,false)⟩
            entriesInside := ?_
            packageInside := ?_
            resourcesInside := ?_
            response := ?_ }⟩
  · intro x he
    obtain ⟨h,hx⟩ := all_second_entries hs x he
    exact ⟨h,6,hx⟩
  · rintro x ⟨h,time,rfl⟩
    exact ⟨h,factor_mem h,rfl⟩
  · rintro x ⟨h,time,rfl⟩
    exact final_resource_closed h time
  · rintro x ⟨h,time,rfl⟩ d
    cases d
    refine ⟨false,final_legal h time,?_,?_⟩
    · exact NativeComposition.ModeExecution.snapshot_normalized false true 2 2 1 nativeAssignment rfl h 8 time false
    · intro o ho
      have hout := (episode_positive_unique false true 2 2 nativeAssignment 1 rfl _ () false o).mp ho
      have he : o=h := hout.2
      subst o
      refine ⟨?_,final_step_law hr h time⟩
      exact ⟨h,time+1,final_update hr h time⟩

theorem final_operational_autonomy (hr : ResourceRuntime.Ready finalResources nativeAssignment)
    (hs : AcquisitionExecution.Ready secondAcquisition nativeAssignment) :
    ResourceRuntime.OperationalReadout finalResourceSchema finalResources nativeAssignment hr
      (AcquisitionExecution.Entry secondSchema secondAcquisition nativeAssignment hs) :=
  ResourceRuntime.soundness _ _ _ hr _ (Classical.choice (final_resource_certificate hr hs))

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
