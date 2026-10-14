import CSTTT.FullNative02.PredictiveAncestry

namespace CSTTT.FullNative02.Temporal
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

def nodeReading (w : World) : Node → Option (ROM × State)
  | .version n => match w.events[n]? with
    | some (.native _ receipt _) => some (receipt.rom,receipt.after)
    | _ => none
  | .birth n => match w.events[n]? with
    | some (.boot _ rom _ _) => some (rom,⟨false,false,false,false,false⟩)
    | some (.activation _ _ rom _ _ state) => some (rom,state)
    | some (.partition _ _ rom _ state) => some (rom,state)
    | some (.fusion _ _ _ rom _ _ left right _) =>
      if left.after=right.after then some (rom,left.after) else none
    | _ => none
  | _ => none

/-- Only the target's derived relative context is used. Literal owner/root
identity is never asserted; parent physical code is transported by rebasing. -/
def rebase (physical : State) (target : Run) : Run := ⟨physical,target.context⟩

theorem rebase_native_commutes (physical next : State) (target : Run) :
    rebase next (advance target next)=advance (rebase physical target) next := rfl

theorem copied_birth_anchors :
    nodeReading branchesWorld (.version 6)=some (.canonical32,⟨false,false,false,false,false⟩) ∧
    nodeReading branchesWorld (.birth 8)=nodeReading branchesWorld (.version 6) ∧
    nodeReading branchesWorld (.birth 9)=nodeReading branchesWorld (.version 6) ∧
    (Epoch.birth (branchesWorld.events.take 9) 1 8).map Epoch.Birth.roots=some [(.version 6,6)] ∧
    (Epoch.birth (branchesWorld.events.take 10) 2 9).map Epoch.Birth.roots=some [(.version 6,6)] ∧
    Epoch.nodeCount branchesWorld.events (.version 6)=some 6 := by decide +kernel

theorem every_fusion_birth_anchors :
    ∀ e∈fusionRows renewable branchesWorld mainRequest,
      nodeReading e.1.world (.birth 24)=nodeReading e.1.world (.version 22) ∧
      nodeReading e.1.world (.birth 24)=nodeReading e.1.world (.version 23) ∧
      (access e.1.world 3).map (fun data => (data.2.1,data.1.receipts.length,data.1.roots))=
        some (.canonical32,0,[(.version 22,7),(.version 23,7)]) ∧
      Epoch.nodeCount e.1.world.events (.version 22)=some 7 ∧
      Epoch.nodeCount e.1.world.events (.version 23)=some 7 := by decide +kernel

theorem node_to_resident_rebased_future (w : World) (owner : Nat) (r : Resident) (key : Token)
    (enabled : access w owner=some (r,.canonical32,key)) (node : Node) (physical : State)
    (ancestorReadout : nodeReading w node=some (.canonical32,physical))
    (copied : r.current=physical) (word : List Bool) (trace : List (Option Observation)) :
    WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
      (fun w => (actual w owner).map observe) w word trace=
    WeightedFuture.law rows (fun r => some (observe r)) (rebase physical (frame w r key)) word trace := by
  have installedAncestor := ancestorReadout
  rw [actual_all_words _ _ _ _ enabled]
  have equal : rebase physical (frame w r key)=frame w r key := by simp [rebase,frame,frameROM,←copied]
  rw [equal]

end CSTTT.FullNative02.Temporal
