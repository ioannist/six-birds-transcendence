import CSTTT.FullNative.ProvenanceCycle

/-! Actual funded cycle/provenance obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Credit
open AccountExecution PhysicalExecution SnapshotExecution
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem actual_clock_step (x y : Execution) (hx : sector x) (a : Bool) (n : Nat)
    (edge : (y,n)∈rawRows renewable x a) :
    (frame y).context.order=(frame x).context.order+1 ∧
    (frame y).context.localRecords=(frame x).context.localRecords+1 ∧
    y.resident.current.phase= !x.resident.current.phase ∧
    y.accounts.portCursor x.resident.token=x.accounts.portCursor x.resident.token+1 ∧
    (y.resident.receipts.head?).map Receipt.issuer=some (.localGenerator x.resident.owner) := by
  rw [sector_rows x hx a] at edge
  obtain ⟨e,member,equal⟩:=List.mem_map.mp edge
  have state : y=advance renewable x a e.1 e.2 := (congrArg Prod.fst equal).symm
  subst y
  have phase:=supported_phase x.resident.current a e.1 e.2 member
  rw [frame_advance x hx a e.1 e.2]
  refine ⟨rfl,rfl,phase,?_,rfl⟩
  simp [advance,transact,put]

def selectedWith (supply : Supply) (w : World) (owner : Owner) (target : State) : Option (World × Nat) :=
  (nativeRows supply w owner false).find? fun e =>
    (e.1.carriers owner).map Local.current=some target

def runWith : Supply → World → Owner → List State → Option World
  | _,w,_,[] => some w
  | supply,w,owner,target::rest =>
    (selectedWith supply w owner target).bind fun e => runWith supply e.1 owner rest

theorem absent_energy_cycle_fails : runWith absentSupply initialWorld 0 sourcePlan=none := by decide +kernel

theorem absent_initial_step_exists : (nativeRows absentSupply initialWorld 0 false).isEmpty=false := by decide +kernel

theorem absent_second_rows_empty :
    nativeRows absentSupply (mount initialWorld 0 (advance absentSupply source false FullInterface.replicaLeft 1)) 0 false=[] := by
  rfl

theorem missing_generator_cycle_fails :
    runWith renewable {initialWorld with carriers := (putOwner initialWorld.carriers 0
      (some {source.resident with installed:=none}))} 0 sourcePlan=none := by rfl

theorem local_clock_history :
    (sourceCycleWorld.carriers 0).map (fun p => (p.orderBase+p.receipts.length,p.receipts.length))=some (6,6) ∧
    (firstTargetCycleWorld.carriers 1).map (fun p => (p.orderBase+p.receipts.length,p.receipts.length))=some (6,6) ∧
    (secondTargetCycleWorld.carriers 2).map (fun p => (p.orderBase+p.receipts.length,p.receipts.length))=some (6,6) := by
  decide +kernel

end CSTTT.FullNative.Credit
