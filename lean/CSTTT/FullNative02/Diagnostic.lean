import CSTTT.FullNative02.GuardFacts

namespace CSTTT.FullNative02
set_option autoImplicit false

structure EmptyReceipt where
  request : FusionRequest
  reference : Node
  rom : ROM
  leftRows : List Edge
  rightRows : List Edge
  mass : Nat
  deriving DecidableEq, Repr

/-- The diagnostic is computed from the same authenticated inputs as the
settlement. Neither its normalizer nor its row evidence is supplied. -/
def emptyReceipt (w : World) (q : FusionRequest) : Option EmptyReceipt := do
  let p ← parentView w q
  let mass := meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction
  if mass=0 then some ⟨q,prospective q,p.rom,
    edges p.rom p.left.current q.leftAction,edges p.rom p.right.current q.rightAction,mass⟩
  else none

structure PaidFusionReceipt where
  request : FusionRequest
  leftBirth : Node
  rightBirth : Node
  leftRoots : List (Node × Nat)
  rightRoots : List (Node × Nat)
  leftOrder : Nat
  rightOrder : Nat
  leftIndex : Nat
  rightIndex : Nat
  mass : Nat
  probability : Rat
  leftReceipt : Receipt
  rightReceipt : Receipt
  outputBirth : Node
  leftKeys : List Token
  rightKeys : List Token
  deriving DecidableEq, Repr

def paidFusionReceipt (supply : Supply) (w : World) (q : FusionRequest) (p : Parents)
    (pair : Pair) : PaidFusionReceipt :=
  let probability := pairProbability p.rom p.left.current p.right.current q.leftAction q.rightAction pair
  let first := advance supply w q.left p.left p.rom p.leftKey q.leftAction
    (pair.1.state,pair.1.weight) (some probability)
  ⟨q,p.left.birth,p.right.birth,p.left.roots,p.right.roots,
    p.left.receipts.length,p.right.receipts.length,pair.1.index,pair.2.index,
    meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction,probability,
    makeReceipt supply w q.left p.left p.rom p.leftKey q.leftAction (pair.1.state,pair.1.weight),
    makeReceipt supply first q.right p.right p.rom p.rightKey q.rightAction (pair.2.state,pair.2.weight),
    .birth (w.events.length+2),keys w.accounts q.left,keys w.accounts q.right⟩

structure ExecutionReadout where
  settlement : Settlement
  empty : Option EmptyReceipt
  paid : Option PaidFusionReceipt

/-- Receipt-bearing execution interface. Envelopes are generated from actual
input rows and transactions. In particular the empty diagnostic is returned,
not appended to the accepted ledger; it leaves the ENTIRE world unchanged. -/
def fusionExecution (supply : Supply) (w : World) (q : FusionRequest) :
    List (ExecutionReadout × Rat) :=
  match parentView w q with
  | none => []
  | some p =>
    if meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction=0 then
      [(⟨⟨w,.empty (prospective q)⟩,emptyReceipt w q,none⟩,1)]
    else (meeting p.rom p.left.current p.right.current q.leftAction q.rightAction).map fun pair =>
      let receipt := paidFusionReceipt supply w q p pair
      (⟨settle supply w q p pair receipt.probability,none,some receipt⟩,receipt.probability)

theorem execution_projects_exactly (supply : Supply) (w : World) (q : FusionRequest) :
    (fusionExecution supply w q).map (fun e => (e.1.settlement,e.2))=fusionRows supply w q := by
  cases view : parentView w q with
  | none => simp [fusionExecution,fusionRows,view]
  | some p =>
    by_cases zero : meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction=0
    · simp [fusionExecution,fusionRows,view,zero]
    · simp [fusionExecution,fusionRows,view,zero,List.map_map,Function.comp_def,paidFusionReceipt]

theorem empty_receipt_from_execution (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (view : parentView w q=some p)
    (zero : meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction=0) :
    fusionExecution supply w q=[(⟨⟨w,.empty (prospective q)⟩,
      some ⟨q,prospective q,p.rom,edges p.rom p.left.current q.leftAction,
        edges p.rom p.right.current q.rightAction,0⟩,none⟩,1)] := by
  simp [fusionExecution,emptyReceipt,view,zero]

theorem paid_envelope_is_actual (supply : Supply) (w : World) (q : FusionRequest)
    (readout : ExecutionReadout) (probability : Rat)
    (member : (readout,probability)∈fusionExecution supply w q)
    (paid : readout.paid.isSome=true) :
    ∃ p pair, parentView w q=some p ∧
      pair∈meeting p.rom p.left.current p.right.current q.leftAction q.rightAction ∧
      readout.paid=some (paidFusionReceipt supply w q p pair) ∧
      probability=(paidFusionReceipt supply w q p pair).probability ∧
      readout.settlement=settle supply w q p pair probability := by
  cases view : parentView w q with
  | none => simp [fusionExecution,view] at member
  | some p =>
    by_cases zero : meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction=0
    · simp only [fusionExecution,view,if_pos zero,List.mem_cons,List.not_mem_nil,or_false] at member
      cases member
      cases paid
    · simp only [fusionExecution,view,if_neg zero] at member
      obtain ⟨pair,support,eq⟩ := List.mem_map.mp member
      cases eq
      exact ⟨p,pair,rfl,support,rfl,rfl,rfl⟩

theorem unavailable_has_no_diagnostic (w : World) (q : FusionRequest)
    (h : parentView w q=none) : emptyReceipt w q=none := by simp [emptyReceipt,h]

theorem paid_receipt_actual_issuers (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (view : parentView w q=some p) (pair : Pair) :
    (paidFusionReceipt supply w q p pair).leftReceipt.issuer=.local q.left ∧
    (paidFusionReceipt supply w q p pair).rightReceipt.issuer=.local q.right :=
  guarded_actual_issuers supply w q p view pair
    (pairProbability p.rom p.left.current p.right.current q.leftAction q.rightAction pair)

theorem paid_receipt_exact_edge_identity (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (pair : Pair)
    (support : pair∈meeting p.rom p.left.current p.right.current q.leftAction q.rightAction) :
    (p.rom.program.rows p.left.current q.leftAction)[(paidFusionReceipt supply w q p pair).leftIndex]?=
      some (pair.1.state,pair.1.weight) ∧
    (p.rom.program.rows p.right.current q.rightAction)[(paidFusionReceipt supply w q p pair).rightIndex]?=
      some (pair.2.state,pair.2.weight) := by
  have actual := meeting_support p.rom p.left.current p.right.current q.leftAction q.rightAction pair support
  exact ⟨edge_identity _ _ _ _ actual.1,edge_identity _ _ _ _ actual.2.1⟩

theorem receipt_execution_normalized (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (view : parentView w q=some p) :
    ((fusionExecution supply w q).map Prod.snd).sum=1 := by
  have projection := congrArg (fun rows : List (Settlement × Rat) => (rows.map Prod.snd).sum)
    (execution_projects_exactly supply w q)
  simp only [List.map_map,Function.comp_def] at projection
  exact projection.trans (fusion_normalized supply w q p view)

end CSTTT.FullNative02
