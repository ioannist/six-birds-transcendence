import CSTTT.FullNative02.Selectors

namespace CSTTT.FullNative02.Epoch
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

def tokenCount (events : List Event) (key : Token) : Nat :=
  (events.filter fun e => match e with
    | .native _ receipt _ => decide (receipt.token=key)
    | _ => false).length

def ownerCount (events : List Event) (owner : Nat) : Nat :=
  (events.filter fun e => match e with
    | .native _ receipt _ => decide (receipt.owner=owner)
    | _ => false).length

def nodeCount (events : List Event) (node : Node) : Option Nat :=
  match node with
  | .version n => match events[n]? with
    | some (.native _ receipt _) => some (ownerCount (events.take (n+1)) receipt.owner)
    | _ => none
  | .birth _ => some 0
  | _ => none

structure Birth where
  rom : ROM
  state : State
  key : Token
  roots : List (Node × Nat)
  recordedCursor : Option Nat
  deriving DecidableEq, Repr

/-- Decode the actual birth and its labelled causal offsets. No owner, program,
cursor or source time is accepted as a certificate input. -/
def birth (events : List Event) (owner ordinal : Nat) : Option Birth := do
  let event ← events[ordinal]?
  match event with
  | .boot a rom key cursor =>
    if a=owner then some ⟨rom,⟨false,false,false,false,false⟩,key,[],some cursor⟩ else none
  | .activation snapshot a rom key cursor state =>
    let .event n := snapshot | none
    let .snapshot source _ _ _ count ← events[n]? | none
    if a=owner then some ⟨rom,state,key,[(source,count)],some cursor⟩ else none
  | .partition parent a rom owned state =>
    let key ← leastOwned owned
    let count ← nodeCount events parent
    if a=owner then some ⟨rom,state,key,[(parent,count)],none⟩ else none
  | .fusion left right a rom xs ys l r _ =>
    let key ← (tokens.filter fun t => decide (t∈xs ∨ t∈ys)).head?
    let lc ← nodeCount events left
    let rc ← nodeCount events right
    if a=owner ∧ l.after=r.after then some ⟨rom,l.after,key,[(left,lc),(right,rc)],none⟩ else none
  | _ => none

structure Audit where
  valid : Bool
  state : State
  version : Node
  cursor : Nat
  records : List Receipt
  charge : Bool
  deriving DecidableEq, Repr

def tokenCharge (events : List Event) (key : Token) : Bool :=
  events.foldl (fun charge e => match e with
    | .native _ receipt _ => if receipt.token=key then receipt.packet.isSome else charge
    | _ => charge) true

def start (ordinal cursor : Nat) (b : Birth) (charge : Bool) : Audit :=
  ⟨true,b.state,.birth ordinal,cursor,[],charge⟩

/-- Every own record is checked, including open tails and absent packets.
Conditional fusion payments are not ordinary local-epoch maintenance. -/
def step (owner : Nat) (b : Birth) (a : Audit) (entry : Event × Nat) : Audit :=
  match entry.1 with
  | .native before r conditional =>
    if r.owner=owner then
      ⟨a.valid && a.charge && decide (before=a.version ∧ r.before=a.state ∧ r.rom=b.rom ∧
          r.issuer=.local owner ∧ r.token=b.key ∧ r.cursor=a.cursor ∧
          r.serial=4*a.cursor+b.key.val ∧ conditional=none ∧
          (r.after,r.weight)∈b.rom.program.rows r.before r.action),
        r.after,.version entry.2,a.cursor+1,a.records++[r],r.packet.isSome⟩
    else a
  | _ => a

def replay (owner : Nat) (ordinal cursor : Nat) (b : Birth) (events : List Event) : Audit :=
  ((events.zipIdx).drop (ordinal+1)).foldl (step owner b)
    (start ordinal cursor b (tokenCharge (events.take ordinal) b.key))

def valid (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token) : Bool :=
  match r.birth with
  | .birth ordinal =>
    match birth (w.events.take (ordinal+1)) owner ordinal with
    | none => false
    | some b =>
      let initialCursor := tokenCount (w.events.take ordinal) key
      let a := replay owner ordinal initialCursor b w.events
      a.valid && decide (ordinal<w.events.length ∧ b.rom=rom ∧ b.key=key ∧
        r.birthCursor=initialCursor ∧ r.roots=b.roots ∧ r.current=a.state ∧
        r.version=a.version ∧ r.receipts=a.records ∧ w.accounts.cursor key=a.cursor ∧
        w.accounts.charge key=a.charge ∧
        (b.recordedCursor=none ∨ b.recordedCursor=some initialCursor))
  | _ => false

theorem step_other (owner : Nat) (b : Birth) (a : Audit) (before : Node)
    (r : Receipt) (conditional : Option Rat) (index : Nat) (h : r.owner≠owner) :
    step owner b a (.native before r conditional,index)=a := by simp [step,h]

theorem step_invalid_stays_invalid (owner : Nat) (b : Birth) (a : Audit)
    (entry : Event × Nat) (h : a.valid=false) :
    (step owner b a entry).valid=false := by
  cases entry with | mk e n =>
    cases e <;> simp [step,h] <;> split <;> simp_all

theorem replay_append (owner ordinal cursor : Nat) (b : Birth) (events tail : List Event)
    (bound : ordinal+1≤events.length) :
    replay owner ordinal cursor b (events++tail)=
      (tail.zipIdx events.length).foldl (step owner b)
        (replay owner ordinal cursor b events) := by
  simp only [replay,List.zipIdx_append]
  rw [List.drop_append_of_le_length (by simpa using bound)]
  rw [List.take_append_of_le_length (by omega)]
  simpa only [Nat.zero_add] using List.foldl_append

end CSTTT.FullNative02.Epoch
