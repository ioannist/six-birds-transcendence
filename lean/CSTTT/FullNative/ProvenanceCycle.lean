import CSTTT.FullNative.ScheduledExecution

/-! Actual funded cycle/provenance obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Credit
open AccountExecution PhysicalExecution SnapshotExecution
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def transferFrom (w : World) : Option World := do
  let reserved ← reserveSiblings w
  let written1 ← writeSnapshot reserved 1
  let written2 ← writeSnapshot written1 2
  let active1 ← activate written2 1
  let active2 ← activate active1 2
  pure (withdraw active2)

theorem transfer_historical (w v : World) (hw : Historical w) (success : transferFrom w=some v) :
    Historical v := by
  cases h1 : reserveSiblings w with
  | none => simp [transferFrom,h1] at success
  | some w1 =>
    cases h2 : writeSnapshot w1 1 with
    | none => simp [transferFrom,h1,h2] at success
    | some w2 =>
      cases h3 : writeSnapshot w2 2 with
      | none => simp [transferFrom,h1,h2,h3] at success
      | some w3 =>
        cases h4 : activate w3 1 with
        | none => simp [transferFrom,h1,h2,h3,h4] at success
        | some w4 =>
          cases h5 : activate w4 2 with
          | none => simp [transferFrom,h1,h2,h3,h4,h5] at success
          | some w5 =>
            have eq : withdraw w5=v := by simpa [transferFrom,h1,h2,h3,h4,h5] using success
            rw [←eq]
            exact .cut (.activation (o:=2) (.activation (o:=1)
              (.write (o:=2) (.write (o:=1) (.reserve hw h1) h2) h3) h4) h5)

def creditedTransferResult : Option World := transferFrom sourceCycleWorld

theorem credited_transfer_present : creditedTransferResult.isSome=true := by decide +kernel

def creditedTransferWorld : World := creditedTransferResult.get credited_transfer_present

theorem credited_transfer_historical : Historical creditedTransferWorld :=
  transfer_historical _ _ source_cycle_historical (by rfl)

theorem credited_transfer_consumed_actual_receipt :
    (creditedTransferWorld.carriers 1).map Local.rootedRoute=some ([FullInterface.rootState],[20]) ∧
    (creditedTransferWorld.carriers 2).map Local.rootedRoute=some ([FullInterface.rootState],[20]) ∧
    (creditedTransferWorld.carriers 1).map (fun p => p.receipts.length)=some 0 ∧
    (creditedTransferWorld.carriers 2).map (fun p => p.receipts.length)=some 0 ∧
    creditedTransferWorld.carriers 0=none ∧ creditedTransferWorld.bridge=none := by
  decide +kernel

def creditedFirstResult : Option World := runCycle creditedTransferWorld 1 sourcePlan

theorem credited_first_present : creditedFirstResult.isSome=true := by decide +kernel

def creditedFirstWorld : World := creditedFirstResult.get credited_first_present

theorem credited_first_historical : Historical creditedFirstWorld :=
  run_historical _ _ 1 sourcePlan credited_transfer_historical (by rfl)

def creditedBothResult : Option World := runCycle creditedFirstWorld 2 sourcePlan

theorem credited_both_present : creditedBothResult.isSome=true := by decide +kernel

def creditedBothWorld : World := creditedBothResult.get credited_both_present

theorem credited_both_historical : Historical creditedBothWorld :=
  run_historical _ _ 2 sourcePlan credited_first_historical (by rfl)

theorem same_history_both_credits : localCredit creditedBothWorld 1=some .self ∧
    localCredit creditedBothWorld 2=some .self ∧
    creditedBothWorld.accounts.portCursor 1=6 ∧ creditedBothWorld.accounts.portCursor 2=6 ∧
    creditedBothWorld.accounts.portCursor 0=6 ∧ creditedBothWorld.carriers 0=none ∧
    creditedBothWorld.bridge=none := by decide +kernel

theorem credited_target_local_receipts :
    (creditedBothWorld.carriers 1).map (fun p => p.receipts.all
      (fun r => decide (r.issuer=.localGenerator 1 ∧ r.token=1)))=some true ∧
    (creditedBothWorld.carriers 2).map (fun p => p.receipts.all
      (fun r => decide (r.issuer=.localGenerator 2 ∧ r.token=2)))=some true := by decide +kernel

theorem credited_first_carrier_present : (creditedBothWorld.carriers 1).isSome=true := by decide +kernel

theorem credited_second_carrier_present : (creditedBothWorld.carriers 2).isSome=true := by decide +kernel

def creditedFirstLocal : Local := (creditedBothWorld.carriers 1).get credited_first_carrier_present

def creditedSecondLocal : Local := (creditedBothWorld.carriers 2).get credited_second_carrier_present

theorem credited_both_siblings : Siblings creditedBothWorld := by
  exact ⟨creditedFirstLocal,creditedSecondLocal,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩⟩

theorem credited_joint_future (word : List (Bool × Bool)) :
    ∃ final, JointContinuation creditedBothWorld word final ∧ Historical final ∧ Siblings final := by
  obtain ⟨final,path,sectors⟩:=joint_all_words creditedBothWorld credited_both_siblings word
  exact ⟨final,path,joint_history _ _ _ credited_both_historical path,sectors⟩

end CSTTT.FullNative.Credit
