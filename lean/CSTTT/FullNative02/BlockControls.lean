import CSTTT.FullNative02.AcquiredPackage
import CSTTT.FullNative.InternalizedCredit

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

/-- Exact generic specialization of the conjunct used by the new block rule.
Both products use the actual current installed generator, not channel weights. -/
theorem actual_internalized_new_blocks_rejected (flavor : Internalized.Flavor)
    (root current : Internalized.Execution) (gate : Internalized.LawGate flavor root)
    (history : Internalized.Closure AccountExecution.renewable root current)
    (candidate : List Internalized.Receipt) :
    (current.receipts.all (Internalized.receiptOK flavor current)=true) ∧
    Blocks.directional
      (TargetTheory.GenericHandoff.NativeComposition.NativeGeneratorCreditPrototype.liftP
        (Internalized.parameter flavor))
      Internalized.Receipt.before Internalized.Receipt.after candidate=false := by
  exact ⟨(Internalized.closure_receipt_integrity _ _ _ gate history).1,
    Blocks.symmetric_block_rejected _ _ _
      (TargetTheory.GenericHandoff.NativeComposition.NativeGeneratorCreditPrototype.lifted_symmetric _) candidate⟩

def flatRun : Option World := runChoices renewable (initial 8 .flat32) 0 sixCycle
theorem flat_run_supported : flatRun.isSome=true := by decide +kernel
def flatWorld : World := flatRun.get flat_run_supported
theorem actual_flat_new_block_rejected :
    (access flatWorld 0).isSome=true ∧
    (flatWorld.residents 0).map (fun r => Epoch.valid flatWorld 0 r .flat32 0)=some true ∧
    (flatWorld.residents 0).map (fun r => Blocks.evidence .flat32 0 r.receipts)=some false ∧
    Epoch.accept flatWorld 0=false := by decide +kernel

/-- Read the actual G19 scheduled experiment into the common block vocabulary.
The bridge issuer remains external; this is a readout specialization, not a new
FULL-NATIVE-02 execution, installation or copied local witness. -/
def scheduledRecord (r : PhysicalExecution.Receipt) : Receipt :=
  ⟨(match r.issuer with | .bridge => .external | .localGenerator owner => .local owner.val),
    1,r.token,r.serial/4,r.serial,.canonical32,r.before,r.after,r.action,r.weight,r.energy⟩
def scheduledRecords : List Receipt :=
  (Credit.scheduledCycleWorld.carriers 1).toList.flatMap fun r => r.receipts.reverse.map scheduledRecord
theorem scheduled_new_block_rejected :
    scheduledRecords.length=6 ∧
    Blocks.directional (Blocks.edge .canonical32) Receipt.before Receipt.after scheduledRecords=true ∧
    Blocks.evidence .canonical32 1 scheduledRecords=false := by decide +kernel

end CSTTT.FullNative02
