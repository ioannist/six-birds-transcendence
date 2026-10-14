import CSTTT.FullNative02.Response
import CSTTT.FullNative02.Controls

namespace CSTTT.FullNative02
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

theorem source_checkpoint_accepts : Epoch.accept sourceWorld 0=true := by decide +kernel
theorem both_withdrawn_children_accept :
    Epoch.accept branchesWorld 1=true ∧ Epoch.accept branchesWorld 2=true := by decide +kernel
theorem every_acquired_output_accepts :
    ∀ e∈fusionRows renewable branchesWorld mainRequest,
      ∀ v∈(outputWarmup e.1.world).toList, Epoch.accept v 3=true := by decide +kernel
theorem every_output_is_cold_viable :
    ∀ e∈fusionRows renewable branchesWorld mainRequest,
      (access e.1.world 3).isSome=true ∧ Epoch.accept e.1.world 3=false := by decide +kernel
theorem initial_cold_is_viable_uncredited :
    (access (initial 8) 0).isSome=true ∧ Epoch.accept (initial 8) 0=false := by decide +kernel

theorem actual_missing_account_epoch_controls :
    Epoch.accept missingProgram 1=false ∧ Epoch.accept wrongCustody 1=false ∧
    Epoch.accept disabledKey 1=false ∧ Epoch.accept forgedVersion 1=false := by decide +kernel

/-- Mutating an earlier record cannot borrow the intact last-record/version
check. The independent whole-epoch audit still detects it. -/
def tamperedTail (w : World) (owner : Nat) : World :=
  {w with residents := fun a => if a=owner then
    (w.residents a).map fun r => {r with receipts := r.receipts.mapIdx fun n receipt =>
      if n=0 then {receipt with serial := receipt.serial+1} else receipt}
    else w.residents a}

def mixedEpoch (w : World) (owner : Nat) : World :=
  {w with residents := fun a => if a=owner then
    (w.residents a).map fun r => {r with receipts := r.receipts.mapIdx fun n receipt =>
      if n=0 then {receipt with issuer := .external} else receipt}
    else w.residents a}

theorem actual_tampering_controls :
    (access (tamperedTail branchesWorld 1) 1).isSome=true ∧
    Epoch.accept (tamperedTail branchesWorld 1) 1=false ∧
    (access (mixedEpoch branchesWorld 1) 1).isSome=true ∧
    Epoch.accept (mixedEpoch branchesWorld 1) 1=false := by decide +kernel

end CSTTT.FullNative02
