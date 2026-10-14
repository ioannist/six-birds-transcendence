import CSTTT.Targets.ComputedFIACH.SnapshotExecution
import CSTTT.Autonomy.FiniteAutonomy

/-! G6_lane_spec.md:147–300. TTH-05 transport, for EVERY actual phase-2
entry, not a reset to a chosen receiver state. The finite carrier is the K
factor; unbounded counters stay in assigned C6's run dynamics. Nominal is a
declared disturbance, not an action. Safe responses retain ALL positive
support. C4–C7 remain the declared package surrogates.

Resource identifiers are an injective serialization of the declared names:
removed roles use their positions in removedRoles; the retained recharge uses
the next position (removedRoles.length). These codes express no new prices,
thresholds or dynamics. All proof fields of the existing TTH-05 structure
are filled from computed checks, not supplied as free propositions. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.AutonomyTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def removedResourceCode (r : RemovedRole) : ResourceId := ⟨removedRoles.idxOf r⟩
def rechargeResourceCode : ResourceId := ⟨removedRoles.length⟩
def retainedResourceCodes (m : RawLaneModel) : List ResourceId :=
  m.retained.map fun _ => rechargeResourceCode

def computedWithdrawal (m : RawLaneModel) : WithdrawalSpec where
  removedResources := m.removed.map removedResourceCode
  retainedResources := retainedResourceCodes m
  disjoint := by
    intro r hr ht
    obtain ⟨role,_,he⟩ := List.mem_map.mp hr
    obtain ⟨resource,_,het⟩ := List.mem_map.mp ht
    have hn : removedResourceCode role ≠ rechargeResourceCode := by cases role <;> decide
    exact hn (he.trans het.symm)
  sourceRemoved := .source ∈ m.removed ∧ m.sourcePresentAfterWithdrawal = false
  bridgeRemoved := .migrationBridge ∈ m.removed
  migrationControllerRemoved := .migrationController ∈ m.removed
  externalDecoderRemoved := .externalDecoder ∈ m.removed
  externalSchedulerRemoved := .externalScheduler ∈ m.removed
  undeclaredRepairRemoved := .undeclaredRepair ∈ m.removed

def computedAutonomySystem (m : RawLaneModel) : ControlledSystem where
  carrier := ⟨tagCarrierId .target,KState,⟨kernel,fun s => by cases s <;> decide⟩⟩
  Disturbance := LaneDisturbance
  Action := Action
  disturbanceEnum := ⟨[.nominal],fun d => by cases d; simp⟩
  actionEnum := ⟨actions,fun a => by cases a <;> decide⟩
  step := fun x _ a y => ∃ n > 0, (.inK y,n) ∈ (withdrawnInputs m).rows x a
  packageValid := fun x => packageAtCheck m x = true
  actionOwner := fun _ => tagCarrierId (withdrawnInputs m).resource.owner
  maintenanceResources := fun _ => [rechargeResourceCode]

/-- No finite factor is required to carry strictly growing counters. The
anti-stall and solvency obligations are assigned unit-tick/writer/ledger
checks; their actual unbounded advancement readout is proved separately. -/
def computedExactAutonomy (m : RawLaneModel) (endpoint : KState) : ExactAutonomyData where
  sys := computedAutonomySystem m
  endpoint := endpoint
  withdrawal := computedWithdrawal m
  inside := fun s => s ∈ greatestF m
  resourceOwner := fun _ => tagCarrierId (withdrawnInputs m).resource.owner
  antiStall := fun _ _ _ _ => advancementCheck m = true
  budgetSolvent := fun _ _ _ _ => Ledger8 (withdrawnInputs m)
  boundaryFixedBeforeEvaluation :=
    Complete autonomyInputs (image m.assignment) ∧ ∀ r ∈ routeIds, phase2Check m r = true
  disturbanceClassFixedBeforeEvaluation :=
    (computedAutonomySystem m).disturbanceEnum.elems = [.nominal]

theorem AF_shared_parts (m : RawLaneModel) (h : AF m) :
    Complete autonomyInputs (image m.assignment) ∧ withdrawalCheck m = true ∧
    advancementCheck m = true ∧ (∀ r ∈ routeIds, phase2Check m r = true) ∧
    (∀ e ∈ entries m, entryInside (greatestF m) e = true) := by
  have hs := (Bool.and_eq_true_iff.mp h).1
  simp only [sharedAutonomyCheck,Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc,hw⟩,ha⟩,_⟩,_⟩,hp⟩,_⟩,he⟩,_⟩ := hs
  exact ⟨of_decide_eq_true hc,hw,ha,List.all_eq_true.mp hp,List.all_eq_true.mp he⟩

theorem response_all_support (m : RawLaneModel) (S : List KState) (x : KState)
    (d : LaneDisturbance) (a : Action) (h : responseCheck m S x d a = true)
    (e : Ambient × Nat) (he : e ∈ (withdrawnInputs m).rows x a) :
    ∃ y, e.1 = .inK y ∧ e.2 > 0 ∧ y ∈ S := by
  have hr := (Bool.and_eq_true_iff.mp h).2
  have hall := (Bool.and_eq_true_iff.mp hr).2
  have hb := List.all_eq_true.mp hall e he
  rcases e with ⟨dest,n⟩
  cases dest with
  | inK y =>
    exact ⟨y,rfl,of_decide_eq_true (Bool.and_eq_true_iff.mp hb).1,
      of_decide_eq_true (Bool.and_eq_true_iff.mp hb).2⟩
  | p2w0 => simp at hb
  | p5w1 => simp at hb

theorem response_has_successor (m : RawLaneModel) (S : List KState) (x : KState)
    (d : LaneDisturbance) (a : Action) (h : responseCheck m S x d a = true) :
    ∃ y, (computedAutonomySystem m).step x d a y ∧ y ∈ S := by
  have hr := (Bool.and_eq_true_iff.mp h).2
  have hn := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hr).1).1
  cases heq : (withdrawnInputs m).rows x a with
  | nil => simp [heq] at hn
  | cons e rest =>
    have he : e ∈ (withdrawnInputs m).rows x a := by simp [heq]
    obtain ⟨y,hy,hw,hs⟩ := response_all_support m S x d a h e he
    refine ⟨y,⟨e.2,hw,?_⟩,hs⟩
    rcases e with ⟨dest,n⟩
    cases hy
    exact he

theorem AF_retained_recharge (m : RawLaneModel) (h : AF m) :
    .targetRecharge ∈ m.retained := by
  have ha := (AF_shared_parts m h).2.2.1
  have hav := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp ha).1).1).1).1
  have hr : (withdrawnInputs m).resource.rechargeAvailable = true :=
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp hav).1).1).1
  by_cases hn : RetainedResource.targetRecharge ∈ m.retained
  · exact hn
  apply False.elim
  have hc := (AF_shared_parts m h).1 (.resources .target) (by decide)
  have hs : (withdrawnInputs m).resource.rechargeAvailable = false := by
    generalize he : image m.assignment (.resources .target) = v at hc
    cases v with
    | none => contradiction
    | some r =>
      simp [withdrawnInputs,clause8,viabilityInputs,decode,clauseScope,
        withdrawnAssignment,mapCell,he,hn]
  rw [hs] at hr
  contradiction

theorem AF_exact_certificate (m : RawLaneModel) (h : AF m) (s : KState)
    (hs : s ∈ greatestF m) : Nonempty (ExactAutonomyCertificate (computedExactAutonomy m s)) := by
  obtain ⟨hc,hw,ha,hphase,_⟩ := AF_shared_parts m h
  have hroles : ∀ r ∈ removedRoles, r ∈ m.removed := by
    have hb := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1
    intro r hr
    exact List.mem_of_elem_eq_true (List.all_eq_true.mp hb r hr)
  have hsource : m.sourcePresentAfterWithdrawal = false := by
    simpa using (Bool.and_eq_true_iff.mp hw).2
  have hav := (Bool.and_eq_true_iff.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp ha).1).1).1).1
  have hledger : Ledger8 (withdrawnInputs m) := of_decide_eq_true
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ha).1).1).1).2
  have howner : (withdrawnInputs m).resource.owner = .target :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hav).2
  refine ⟨{
    sourceRemoved := ⟨hroles .source (by decide),hsource⟩
    bridgeRemoved := hroles .migrationBridge (by decide)
    migrationControllerRemoved := hroles .migrationController (by decide)
    externalDecoderRemoved := hroles .externalDecoder (by decide)
    externalSchedulerRemoved := hroles .externalScheduler (by decide)
    undeclaredRepairRemoved := hroles .undeclaredRepair (by decide)
    boundaryFixed := ⟨hc,hphase⟩
    disturbanceClassFixed := rfl
    endpointInside := hs
    packageInside := greatestF_packageInside m
    resourceClosed := ?_
    retainedResourcesTargetOwned := ?_
    response := ?_ }⟩
  · intro _ _ r hr
    have he : r = rechargeResourceCode := List.mem_singleton.mp hr
    subst r
    exact List.mem_map.mpr ⟨.targetRecharge,AF_retained_recharge m h,rfl⟩
  · intro _ _
    exact congrArg tagCarrierId howner
  · intro x d hx
    obtain ⟨a,_,hr⟩ := greatestF_all_support_responses m x hx d
    obtain ⟨y,hstep,hy⟩ := response_has_successor m (greatestF m) x d a hr
    exact ⟨a,y,congrArg tagCarrierId howner,hstep,hy,ha,hledger⟩

theorem AF_each_entry_inside (m : RawLaneModel) (h : AF m) (e : WithdrawalEntry)
    (he : e ∈ entries m) : ∃ s, e.factor = .inK s ∧ s ∈ greatestF m := by
  have hi := (AF_shared_parts m h).2.2.2.2 e he
  have hf := (Bool.and_eq_true_iff.mp hi).2
  cases hs : e.factor with
  | inK s => exact ⟨s,rfl,of_decide_eq_true (by simpa [hs] using hf)⟩
  | p2w0 => simp [hs] at hf
  | p5w1 => simp [hs] at hf

theorem AF_each_entry_exact_autonomy (m : RawLaneModel) (h : AF m)
    (e : WithdrawalEntry) (he : e ∈ entries m) :
    ∃ s, e.factor = .inK s ∧
      Nonempty (ExactAutonomyCertificate (computedExactAutonomy m s)) := by
  obtain ⟨s,hfactor,hs⟩ := AF_each_entry_inside m h e he
  exact ⟨s,hfactor,AF_exact_certificate m h s hs⟩

theorem AF_each_entry_nominal_words (m : RawLaneModel) (h : AF m)
    (e : WithdrawalEntry) (he : e ∈ entries m) (word : List LaneDisturbance) :
    ∃ s, e.factor = .inK s ∧ ∃ y,
      ControlledRun (computedExactAutonomy m s) s word y ∧ packageAtCheck m y = true := by
  obtain ⟨s,hfactor,⟨cert⟩⟩ := AF_each_entry_exact_autonomy m h e he
  exact ⟨s,hfactor,postWithdrawalFiniteHorizonInvariance cert word⟩

end CSTTT.TargetTheory.ComputedFIACH
