import CSTTT.FullNative.ReceiptCredit

/-! Actual funded cycle/provenance obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Credit
open AccountExecution PhysicalExecution SnapshotExecution
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def selectedStep (w : World) (owner : Owner) (target : State) : Option (World × Nat) :=
  (nativeRows renewable w owner false).find? fun e =>
    (e.1.carriers owner).map Local.current=some target

def runCycle : World → Owner → List State → Option World
  | w,_,[] => some w
  | w,owner,target::rest => (selectedStep w owner target).bind fun e => runCycle e.1 owner rest

theorem selection_supported (w : World) (owner : Owner) (target : State) (v : World) (n : Nat)
    (selected : selectedStep w owner target=some (v,n)) : (v,n)∈nativeRows renewable w owner false := by
  exact List.mem_of_find?_eq_some selected

theorem run_historical (w v : World) (owner : Owner) (targets : List State)
    (historical : Historical w) (success : runCycle w owner targets=some v) : Historical v := by
  induction targets generalizing w with
  | nil =>
    have equal : w=v := by simpa [runCycle] using success
    exact equal ▸ historical
  | cons target rest ih =>
    cases hs : selectedStep w owner target with
    | none => simp [runCycle,hs] at success
    | some e =>
      simp only [runCycle,hs,Option.bind_some] at success
      exact ih e.1 (Historical.native (a:=false) (n:=e.2) historical
        (selection_supported w owner target e.1 e.2 hs)) success

def sourcePlan : List State := cycle.drop 1++cycle.take 1

def sourceCycleResult : Option World := runCycle initialWorld 0 sourcePlan

theorem source_cycle_present : sourceCycleResult.isSome=true := by decide +kernel

def sourceCycleWorld : World := sourceCycleResult.get source_cycle_present

theorem source_cycle_success : runCycle initialWorld 0 sourcePlan=some sourceCycleWorld := by rfl

theorem source_cycle_historical : Historical sourceCycleWorld :=
  run_historical initialWorld sourceCycleWorld 0 sourcePlan .initial source_cycle_success

theorem source_cycle_actual_accounts : sourceCycleWorld.accounts.charge 0=true ∧
    sourceCycleWorld.accounts.portCursor 0=6 ∧
    (sourceCycleWorld.carriers 0).map (fun x => x.receipts.length)=some 6 ∧
    (sourceCycleWorld.carriers 0).map Local.current=some FullInterface.rootState := by decide +kernel

theorem source_cycle_issuers :
    (sourceCycleWorld.carriers 0).map (fun x => x.receipts.all (fun r => decide (r.issuer=.localGenerator 0)))=some true := by
  decide +kernel

theorem source_actual_credit : localCredit sourceCycleWorld 0=some .self := by decide +kernel

theorem source_actual_cycle_products :
    (sourceCycleWorld.carriers 0).map (fun p => forwardReceipts model p.receipts)=some (324/(16:Rat)^6) ∧
    (sourceCycleWorld.carriers 0).map (fun p => reverseReceipts model p.receipts)=some (36/(16:Rat)^6) := by
  decide +kernel

def flipPhase (s : State) : State := {s with phase:= !s.phase}

def targetPlan : List State := sourcePlan.map flipPhase

def targetCycleResult (o : Owner) : Option World := runCycle autonomousSiblings o targetPlan

theorem first_target_cycle_present : (targetCycleResult 1).isSome=true := by decide +kernel

def firstTargetCycleWorld : World := (targetCycleResult 1).get first_target_cycle_present

theorem first_target_cycle_success : runCycle autonomousSiblings 1 targetPlan=some firstTargetCycleWorld := by rfl

theorem first_target_cycle_historical : Historical firstTargetCycleWorld :=
  run_historical _ _ 1 targetPlan actual_snapshot_history first_target_cycle_success

theorem first_target_credit : localCredit firstTargetCycleWorld 1=some .self := by decide +kernel

theorem first_target_withdrawn : firstTargetCycleWorld.carriers 0=none ∧
    firstTargetCycleWorld.bridge=none ∧ (∀ o, firstTargetCycleWorld.slots o=none) := by
  exact ⟨rfl,rfl,fun _ => rfl⟩

theorem second_target_cycle_present : (targetCycleResult 2).isSome=true := by decide +kernel

def secondTargetCycleWorld : World := (targetCycleResult 2).get second_target_cycle_present

theorem second_target_cycle_success : runCycle autonomousSiblings 2 targetPlan=some secondTargetCycleWorld := by rfl

theorem second_target_cycle_historical : Historical secondTargetCycleWorld :=
  run_historical _ _ 2 targetPlan actual_snapshot_history second_target_cycle_success

theorem second_target_credit : localCredit secondTargetCycleWorld 2=some .self := by decide +kernel

def sequentialCyclesResult : Option World := runCycle firstTargetCycleWorld 2 targetPlan

theorem sequential_cycles_present : sequentialCyclesResult.isSome=true := by decide +kernel

def sequentialCyclesWorld : World := sequentialCyclesResult.get sequential_cycles_present

theorem sequential_cycles_success : runCycle firstTargetCycleWorld 2 targetPlan=some sequentialCyclesWorld := by rfl

theorem sequential_cycles_historical : Historical sequentialCyclesWorld :=
  run_historical _ _ 2 targetPlan first_target_cycle_historical sequential_cycles_success

theorem both_targets_credited : localCredit sequentialCyclesWorld 1=some .self ∧
    localCredit sequentialCyclesWorld 2=some .self ∧
    sequentialCyclesWorld.accounts.portCursor 1=6 ∧ sequentialCyclesWorld.accounts.portCursor 2=6 := by
  decide +kernel

def flatSourceWorld : World :=
  {initialWorld with carriers := (putOwner initialWorld.carriers 0
    (some {source.resident with installed:=some (flatten model)}))}

def flatCycleResult : Option World := runCycle flatSourceWorld 0 sourcePlan

theorem flat_cycle_present : flatCycleResult.isSome=true := by decide +kernel

def flatCycleWorld : World := flatCycleResult.get flat_cycle_present

theorem flat_actual_credit : localCredit flatCycleWorld 0=some .neutral := by decide +kernel

theorem flat_actual_products :
    (flatCycleWorld.carriers 0).map (fun p => forwardReceipts (flatten model) p.receipts)=some (64/(16:Rat)^6) ∧
    (flatCycleWorld.carriers 0).map (fun p => reverseReceipts (flatten model) p.receipts)=some (64/(16:Rat)^6) := by
  decide +kernel

end CSTTT.FullNative.Credit
