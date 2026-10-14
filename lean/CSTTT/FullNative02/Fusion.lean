import CSTTT.FullNative02.Fission
import CSTTT.FullNative02.Meeting

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 8000000

structure FusionRequest where
  left : Nat
  right : Nat
  leftVersion : Node
  rightVersion : Node
  leftAction : Bool
  rightAction : Bool
  output : Nat
  deriving DecidableEq, Repr

structure Parents where
  left : Resident
  right : Resident
  rom : ROM
  leftKey : Token
  rightKey : Token
  outputKey : Token
  deriving DecidableEq, Repr

def parentView (w : World) (q : FusionRequest) : Option Parents := do
  let (left,rom,leftKey) ← access w q.left
  let (right,rightROM,rightKey) ← access w q.right
  let outputKey ← (tokens.filter fun t => decide
    (w.accounts.custody t=.local q.left ∨ w.accounts.custody t=.local q.right)).head?
  if q.left≠q.right ∧ rom=rightROM ∧ leftKey≠rightKey ∧
      left.version=q.leftVersion ∧ right.version=q.rightVersion ∧
      freshAddress w q.output=true ∧
      (∀ t ∈ keys w.accounts q.left, t∉keys w.accounts q.right) then
    some ⟨left,right,rom,leftKey,rightKey,outputKey⟩
  else none

inductive OutcomeKind where
  | created (birth : Node)
  | empty (prospective : Node)
  deriving DecidableEq, Repr

structure Settlement where
  world : World
  kind : OutcomeKind

def prospective (q : FusionRequest) : Node :=
  .prospective q.leftVersion q.rightVersion q.leftAction q.rightAction q.output

def paidParents (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (pair : Pair) (probability : Rat) : World :=
  let first := advance supply w q.left parents.left parents.rom parents.leftKey q.leftAction
    (pair.1.state,pair.1.weight) (some probability)
  advance supply first q.right parents.right parents.rom parents.rightKey q.rightAction
    (pair.2.state,pair.2.weight) (some probability)

def settle (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (pair : Pair) (probability : Rat) : Settlement :=
  let paid := paidParents supply w q parents pair probability
  let leftReceipt := makeReceipt supply w q.left parents.left parents.rom parents.leftKey
    q.leftAction (pair.1.state,pair.1.weight)
  let first := advance supply w q.left parents.left parents.rom parents.leftKey q.leftAction
    (pair.1.state,pair.1.weight) (some probability)
  let rightReceipt := makeReceipt supply first q.right parents.right parents.rom parents.rightKey
    q.rightAction (pair.2.state,pair.2.weight)
  let output : Resident := ⟨q.output,some parents.rom,pair.1.state,
    .birth paid.events.length,.birth paid.events.length,paid.accounts.cursor parents.outputKey,
    [(.version w.events.length,parents.left.receipts.length+1),
     (.version (w.events.length+1),parents.right.receipts.length+1)],[]⟩
  let result : World := {paid with
    residents := put (put (put paid.residents q.left none) q.right none) q.output (some output)
    fresh := put paid.fresh q.output false
    accounts := {paid.accounts with
      custody := fun t =>
        if paid.accounts.custody t=.local q.left ∨ paid.accounts.custody t=.local q.right
        then .local q.output else paid.accounts.custody t}
    events := paid.events ++ [.fusion (.version w.events.length) (.version (w.events.length+1))
      q.output parents.rom (keys w.accounts q.left) (keys w.accounts q.right)
      leftReceipt rightReceipt probability]}
  ⟨result,.created output.birth⟩

def fusionRows (supply : Supply) (w : World) (q : FusionRequest) : List (Settlement × Rat) :=
  match parentView w q with
  | none => []
  | some parents =>
    let mass := meetingMass parents.rom parents.left.current parents.right.current q.leftAction q.rightAction
    if mass=0 then [(⟨w,.empty (prospective q)⟩,1)] else
      (meeting parents.rom parents.left.current parents.right.current q.leftAction q.rightAction).map fun p =>
        let probability := pairProbability parents.rom parents.left.current parents.right.current
          q.leftAction q.rightAction p
        (settle supply w q parents p probability,probability)

theorem unavailable_no_rows (supply : Supply) (w : World) (q : FusionRequest)
    (h : parentView w q=none) : fusionRows supply w q=[] := by simp [fusionRows,h]

theorem empty_same_world (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (h : parentView w q=some parents)
    (zero : meetingMass parents.rom parents.left.current parents.right.current q.leftAction q.rightAction=0) :
    fusionRows supply w q=[(⟨w,.empty (prospective q)⟩,1)] := by simp [fusionRows,h,zero]

theorem fusion_normalized (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (h : parentView w q=some parents) : ((fusionRows supply w q).map Prod.snd).sum=1 := by
  by_cases hz : meetingMass parents.rom parents.left.current parents.right.current q.leftAction q.rightAction=0
  · simp [fusionRows,h,hz,Rat.add_zero]
  · simpa [fusionRows,h,hz,List.map_map] using
      meeting_normalized parents.rom parents.left.current parents.right.current q.leftAction q.rightAction hz

theorem output_installed (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (pair : Pair) (probability : Rat) :
    (((settle supply w q parents pair probability).world.residents q.output).map Resident.installed)=
      some (some parents.rom) := by simp [settle,put]

theorem output_cold (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (pair : Pair) (probability : Rat) :
    (((settle supply w q parents pair probability).world.residents q.output).map Resident.receipts)=some [] := by
  simp [settle,put]

theorem output_cap_consumed (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (pair : Pair) (probability : Rat) :
    (settle supply w q parents pair probability).world.fresh q.output=false := by simp [settle,put]

theorem parents_retired (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (pair : Pair) (probability : Rat) (hl : q.left≠q.output) (hr : q.right≠q.output) :
    (settle supply w q parents pair probability).world.residents q.left=none ∧
    (settle supply w q parents pair probability).world.residents q.right=none := by
  constructor <;> simp [settle,put,hl,hr]

theorem all_stock_transferred_unchanged (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (pair : Pair) (probability : Rat) :
    (settle supply w q parents pair probability).world.accounts.charge=
      (paidParents supply w q parents pair probability).accounts.charge ∧
    (settle supply w q parents pair probability).world.accounts.cursor=
      (paidParents supply w q parents pair probability).accounts.cursor := ⟨rfl,rfl⟩

theorem every_parent_token_transferred (supply : Supply) (w : World) (q : FusionRequest) (parents : Parents)
    (pair : Pair) (probability : Rat) (t : Token)
    (owned : w.accounts.custody t=.local q.left ∨ w.accounts.custody t=.local q.right) :
    (settle supply w q parents pair probability).world.accounts.custody t=.local q.output := by
  simp [settle,paidParents,advance,transact,owned]

end CSTTT.FullNative02
