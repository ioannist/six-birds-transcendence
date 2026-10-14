import CSTTT.FullNative.CycleExecution

/-! Actual funded cycle/provenance obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Credit
open AccountExecution PhysicalExecution SnapshotExecution
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def disableNative (w : World) (o : Owner) : Option World :=
  (w.carriers o).bind fun p => if p.owner=o then
    some {w with carriers := putOwner w.carriers o (some {p with installed:=none})}
  else none

def bridgeIssued (supply : Supply) (w : World) (p : Local) (a : Bool) (s : State) (n : Nat) : Receipt :=
  ⟨.bridge,3,4*w.accounts.portCursor 3+3,p.current,s,a,n,supply 3 (w.accounts.portCursor 3)⟩

def bridgeAdvance (supply : Supply) (w : World) (o : Owner) (p : Local)
    (a : Bool) (s : State) (n : Nat) : World :=
  mount w o ⟨transact supply w.accounts 3,
    {p with current:=s,receipts:=bridgeIssued supply w p a s n::p.receipts}⟩

def bridgeRows (supply : Supply) (w : World) (o : Owner) (a : Bool) : List (World × Nat) :=
  match w.bridge,w.carriers o with
  | some d,some p =>
    if p.owner=o ∧ w.accounts.allocation 3=some .bridge ∧ w.accounts.charge 3=true then
      (d.rows p.current a).map fun e => (bridgeAdvance supply w o p a e.1 e.2,e.2)
    else []
  | _,_ => []

def scheduledStep (w : World) (o : Owner) (target : State) : Option (World × Nat) :=
  (bridgeRows renewable w o false).find? fun e =>
    (e.1.carriers o).map Local.current=some target

def runScheduled : World → Owner → List State → Option World
  | w,_,[] => some w
  | w,o,target::rest => (scheduledStep w o target).bind fun e => runScheduled e.1 o rest

def scheduledInitial : World :=
  {bothActivated with carriers := (putOwner bothActivated.carriers 1
    (some {(activatedLocal 1) with installed:=none}))}

theorem scheduled_initial_disable : disableNative bothActivated 1=some scheduledInitial := by rfl

theorem both_activated_historical : Historical bothActivated := by
  apply Historical.activation (o:=2) _ activate_second_step
  apply Historical.activation (o:=1) _ activate_first_step
  apply Historical.write (o:=2) _ write_second_step
  apply Historical.write (o:=1) _ write_first_step
  apply Historical.reserve _ reserve_step
  exact Historical.native (o:=0) (a:=false) (n:=1) .initial source_step_supported

inductive ScheduledHistorical : World → Prop where
  | snapshot {w : World} : Historical w → ScheduledHistorical w
  | disable {w v : World} {o : Owner} :
      ScheduledHistorical w → disableNative w o=some v → ScheduledHistorical v
  | step {w v : World} {o : Owner} {a : Bool} {n : Nat} :
      ScheduledHistorical w → (v,n)∈bridgeRows renewable w o a → ScheduledHistorical v

theorem scheduled_selection_supported (w : World) (o : Owner) (target : State) (v : World) (n : Nat)
    (selected : scheduledStep w o target=some (v,n)) : (v,n)∈bridgeRows renewable w o false :=
  List.mem_of_find?_eq_some selected

theorem scheduled_run_historical (w v : World) (o : Owner) (targets : List State)
    (historical : ScheduledHistorical w) (success : runScheduled w o targets=some v) : ScheduledHistorical v := by
  induction targets generalizing w with
  | nil =>
    have equal : w=v := by simpa [runScheduled] using success
    exact equal ▸ historical
  | cons target rest ih =>
    cases hs : scheduledStep w o target with
    | none => simp [runScheduled,hs] at success
    | some e =>
      simp only [runScheduled,hs,Option.bind_some] at success
      exact ih e.1 (ScheduledHistorical.step (a:=false) (n:=e.2) historical
        (scheduled_selection_supported w o target e.1 e.2 hs)) success

def scheduledCycleResult : Option World := runScheduled scheduledInitial 1 targetPlan

theorem scheduled_cycle_present : scheduledCycleResult.isSome=true := by decide +kernel

def scheduledCycleWorld : World := scheduledCycleResult.get scheduled_cycle_present

theorem scheduled_cycle_historical : ScheduledHistorical scheduledCycleWorld :=
  scheduled_run_historical _ _ 1 targetPlan
    (.disable (.snapshot both_activated_historical) scheduled_initial_disable) (by rfl)

def bridgeCredit (w : World) (o : Owner) : Option CreditVerdict :=
  (w.carriers o).map fun p =>
    if p.owner=o then match w.bridge with
    | none => .rejected
    | some d => if p.receipts.all (fun r => decide (r.issuer=.bridge)) then
        receiptCredit w.accounts p.owner d p.receipts else .rejected
    else .rejected

theorem scheduled_actual_credit : bridgeCredit scheduledCycleWorld 1=some .other ∧
    localCredit scheduledCycleWorld 1=some .rejected := by decide +kernel

theorem scheduled_actual_port : scheduledCycleWorld.accounts.portCursor 3=6 ∧
    scheduledCycleWorld.accounts.portCursor 1=0 ∧ scheduledCycleWorld.accounts.charge 1=true ∧
    (scheduledCycleWorld.carriers 1).map (fun p => p.receipts.all
      (fun r => decide (r.issuer=.bridge ∧ r.token=3)))=some true := by decide +kernel

theorem withdrawn_bridge_disables (w : World) (o : Owner) (a : Bool) :
    bridgeRows renewable (withdraw w) o a=[] := by simp [bridgeRows,withdraw]

theorem scheduled_actual_products :
    (scheduledCycleWorld.carriers 1).map (fun p => forwardReceipts model p.receipts)=some (324/(16:Rat)^6) ∧
    (scheduledCycleWorld.carriers 1).map (fun p => reverseReceipts model p.receipts)=some (36/(16:Rat)^6) := by
  decide +kernel

def mixedFirstResult : Option (World × Nat) :=
  selectedStep bothActivated 1 ⟨false,false,true,false,false⟩

theorem mixed_first_present : mixedFirstResult.isSome=true := by decide +kernel

def mixedFirstWorld : World := (mixedFirstResult.get mixed_first_present).1

theorem mixed_first_historical : Historical mixedFirstWorld :=
  .native (o:=1) (a:=false) (n:=3) both_activated_historical
    (selection_supported bothActivated 1 ⟨false,false,true,false,false⟩ mixedFirstWorld 3 (by rfl))

def mixedCycleResult : Option World := runScheduled mixedFirstWorld 1 (targetPlan.drop 1)

theorem mixed_cycle_present : mixedCycleResult.isSome=true := by decide +kernel

def mixedCycleWorld : World := mixedCycleResult.get mixed_cycle_present

theorem mixed_cycle_historical : ScheduledHistorical mixedCycleWorld :=
  scheduled_run_historical _ _ 1 (targetPlan.drop 1) (.snapshot mixed_first_historical) (by rfl)

theorem actual_mixed_issuers_reject : localCredit mixedCycleWorld 1=some .rejected ∧
    bridgeCredit mixedCycleWorld 1=some .rejected ∧
    mixedCycleWorld.accounts.portCursor 1=1 ∧ mixedCycleWorld.accounts.portCursor 3=5 := by decide +kernel

end CSTTT.FullNative.Credit
