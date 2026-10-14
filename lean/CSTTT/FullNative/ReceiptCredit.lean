import CSTTT.FullNative.PhysicalCycle

/-! Actual funded cycle/provenance obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Credit
open AccountExecution PhysicalExecution SnapshotExecution
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

inductive CreditVerdict where
  | rejected | neutral | self | other
  deriving DecidableEq, Repr

def consecutive : List Receipt → Bool
  | [] => true
  | [_] => true
  | r::s::rest => decide (r.before=s.after) && consecutive (s::rest)

def closedReceipts (rs : List Receipt) : Bool :=
  !rs.isEmpty && consecutive rs &&
    decide ((rs.head?.map Receipt.after)=(rs.getLast?.map Receipt.before))

def edgeProbability (d : Model) (s t : State) : Rat :=
  ((rationalRows d s false).map fun e => if e.1=t then e.2 else 0).sum

def forwardReceipts (d : Model) (rs : List Receipt) : Rat :=
  (rs.reverse.map fun r => edgeProbability d r.before r.after).foldl (·*·) 1

def reverseReceipts (d : Model) (rs : List Receipt) : Rat :=
  (rs.map fun r => edgeProbability d r.after r.before).foldl (·*·) 1

def validReceipts (accounts : Accounts) (d : Model) (rs : List Receipt) : Bool :=
  closedReceipts rs && rs.all (fun r => decide
    (r.action=false ∧ (r.after,r.weight)∈d.rows r.before false ∧ 0<r.weight ∧
     accounts.allocation r.token=some r.issuer) && r.energy.isSome)

/-- Products and provenance are computed from actual receipts and installed rows. -/

def receiptCredit (accounts : Accounts) (owner : Owner) (d : Model) (rs : List Receipt) : CreditVerdict :=
  if validReceipts accounts d rs then
    match rs.head? with
    | none => .rejected
    | some first =>
      if rs.all (fun r => decide (r.issuer=first.issuer)) then
        if forwardReceipts d rs=reverseReceipts d rs then .neutral
        else if first.issuer=.localGenerator owner then .self else .other
      else .rejected
  else .rejected

def localCredit (w : World) (o : Owner) : Option CreditVerdict :=
  (w.carriers o).map fun p =>
    if p.owner=o then match p.installed with
    | none => .rejected
    | some d => receiptCredit w.accounts p.owner d p.receipts
    else .rejected

theorem missing_receipts_rejected (a : Accounts) (owner : Owner) (d : Model) :
    receiptCredit a owner d []=.rejected := by rfl

theorem mixed_issuers_reject (a : Accounts) (owner : Owner) (d : Model) (rs : List Receipt) (r : Receipt)
    (valid : validReceipts a d rs=true) (head : rs.head?=some r)
    (mixed : rs.all (fun x => decide (x.issuer=r.issuer))=false) :
    receiptCredit a owner d rs=.rejected := by simp [receiptCredit,valid,head,mixed]

end CSTTT.FullNative.Credit
