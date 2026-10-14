import CSTTT.FullNative02.FusionAncestry
import CSTTT.FullNative02.Conservative

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

abbrev renewable : Supply := FullNative.AccountExecution.renewable
abbrev absent : Supply := FullNative.AccountExecution.absentSupply

/-- A requested physical outcome is accepted only if an actual installed,
owned weighted row contains it. Missing input/support returns none. -/
def chooseNative (supply : Supply) (w : World) (owner : Nat) (action : Bool) (state : State) : Option World :=
  ((nativeRows supply w owner action).find? fun e =>
    decide ((e.1.residents owner).map Resident.current=some state)).map Prod.fst

def runChoices (supply : Supply) : World → Nat → List State → Option World
  | w,_,[] => some w
  | w,owner,s::rest => do
    let next ← chooseNative supply w owner false s
    runChoices supply next owner rest

def sixCycle : List State :=
  [⟨false,false,true,false,true⟩,⟨false,true,true,false,false⟩,⟨false,false,false,false,true⟩,
   ⟨false,false,true,false,false⟩,⟨false,true,true,false,true⟩,⟨false,false,false,false,false⟩]

def sourceRun : Option World := runChoices renewable (initial 8) 0 sixCycle
theorem source_run_available : sourceRun.isSome=true := by decide +kernel
def sourceWorld : World := sourceRun.get source_run_available

def branchesRun : Option World := do
  let copied ← bootstrap sourceWorld 0 1 2
  let left ← runChoices renewable copied 1 sixCycle
  let right ← runChoices renewable left 2 sixCycle
  pure (withdraw right)

theorem branches_run_available : branchesRun.isSome=true := by decide +kernel
def branchesWorld : World := branchesRun.get branches_run_available

def requestFor (w : World) (left right output : Nat) (a b : Bool) : Option FusionRequest := do
  let l ← w.residents left
  let r ← w.residents right
  pure ⟨left,right,l.version,r.version,a,b,output⟩

def requestRun : Option FusionRequest := requestFor branchesWorld 1 2 3 false false
theorem request_available : requestRun.isSome=true := by decide +kernel
def mainRequest : FusionRequest := requestRun.get request_available

theorem main_parents_available : (parentView branchesWorld mainRequest).isSome=true := by decide +kernel
def mainParents : Parents := (parentView branchesWorld mainRequest).get main_parents_available
theorem main_view : parentView branchesWorld mainRequest=some mainParents := by
  exact (Option.some_get main_parents_available).symm

theorem main_resource_context :
    mainParents.leftKey=1 ∧ mainParents.rightKey=2 ∧ mainParents.outputKey=1 ∧
    mainParents.left.version=.version 15 ∧ mainParents.right.version=.version 21 ∧
    branchesWorld.accounts.cursor 1=6 ∧ branchesWorld.accounts.cursor 2=6 ∧
    branchesWorld.residents 0=none ∧ branchesWorld.acquisition=false := by decide +kernel

theorem main_meeting_present :
    0<meetingMass mainParents.rom mainParents.left.current mainParents.right.current false false := by
  decide +kernel

theorem main_fusion_normalized :
    ((fusionRows renewable branchesWorld mainRequest).map Prod.snd).sum=1 :=
  fusion_normalized renewable branchesWorld mainRequest mainParents main_view

theorem branches_source_ancestry :
    ancestry branchesWorld (.birth 0) mainParents.left.version ∧
    ancestry branchesWorld (.birth 0) mainParents.right.version := by
  have source : ancestry branchesWorld (.birth 0) (.version 6) := by
    apply Path.extend (y := .event 6)
    · apply Path.extend (y := .version 5)
      · apply Path.extend (y := .event 5)
        · apply Path.extend (y := .version 4)
          · apply Path.extend (y := .event 4)
            · apply Path.extend (y := .version 3)
              · apply Path.extend (y := .event 3)
                · apply Path.extend (y := .version 2)
                  · apply Path.extend (y := .event 2)
                    · apply Path.extend (y := .version 1)
                      · apply Path.extend (y := .event 1)
                        · exact .one (by decide +kernel)
                        · decide +kernel
                      · decide +kernel
                    · decide +kernel
                  · decide +kernel
                · decide +kernel
              · decide +kernel
            · decide +kernel
          · decide +kernel
        · decide +kernel
      · decide +kernel
    · decide +kernel
  have snapshot : ancestry branchesWorld (.birth 0) (.event 7) :=
    .extend source (by decide +kernel)
  have leftBirth : ancestry branchesWorld (.birth 0) (.birth 8) :=
    .extend snapshot (by decide +kernel)
  have rightBirth : ancestry branchesWorld (.birth 0) (.birth 9) :=
    .extend snapshot (by decide +kernel)
  have walk (start finish : Nat) (birth : Node) (initial : ancestry branchesWorld (.birth 0) birth)
      (first : (birth,.event start)∈ledgerEdges branchesWorld)
      (links : ∀ n∈List.range (finish-start+1),
        (.event (start+n),.version (start+n))∈ledgerEdges branchesWorld ∧
        (n=0 ∨ (.version (start+n-1),.event (start+n))∈ledgerEdges branchesWorld)) :
      ancestry branchesWorld (.birth 0) (.version start) :=
    .extend (.extend initial first) (links 0 (by simp)).1
  have l0 := walk 10 15 (.birth 8) leftBirth (by decide +kernel) (by decide +kernel)
  have r0 := walk 16 21 (.birth 9) rightBirth (by decide +kernel) (by decide +kernel)
  have l1 := Path.extend (Path.extend l0 (by decide +kernel)) (by decide +kernel :
      (.event 11,.version 11)∈ledgerEdges branchesWorld)
  have l2 := Path.extend (Path.extend l1 (by decide +kernel)) (by decide +kernel :
      (.event 12,.version 12)∈ledgerEdges branchesWorld)
  have l3 := Path.extend (Path.extend l2 (by decide +kernel)) (by decide +kernel :
      (.event 13,.version 13)∈ledgerEdges branchesWorld)
  have l4 := Path.extend (Path.extend l3 (by decide +kernel)) (by decide +kernel :
      (.event 14,.version 14)∈ledgerEdges branchesWorld)
  have l5 := Path.extend (Path.extend l4 (by decide +kernel)) (by decide +kernel :
      (.event 15,.version 15)∈ledgerEdges branchesWorld)
  have r1 := Path.extend (Path.extend r0 (by decide +kernel)) (by decide +kernel :
      (.event 17,.version 17)∈ledgerEdges branchesWorld)
  have r2 := Path.extend (Path.extend r1 (by decide +kernel)) (by decide +kernel :
      (.event 18,.version 18)∈ledgerEdges branchesWorld)
  have r3 := Path.extend (Path.extend r2 (by decide +kernel)) (by decide +kernel :
      (.event 19,.version 19)∈ledgerEdges branchesWorld)
  have r4 := Path.extend (Path.extend r3 (by decide +kernel)) (by decide +kernel :
      (.event 20,.version 20)∈ledgerEdges branchesWorld)
  have r5 := Path.extend (Path.extend r4 (by decide +kernel)) (by decide +kernel :
      (.event 21,.version 21)∈ledgerEdges branchesWorld)
  simpa only [main_resource_context.2.2.2.1,main_resource_context.2.2.2.2.1] using And.intro l5 r5

end CSTTT.FullNative02
