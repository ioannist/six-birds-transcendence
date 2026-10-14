import CSTTT.FullNative02.ROM
import CSTTT.FullNative.AccountExecution

/-! The FULL-NATIVE-02 raw store. Graph edges, funding, receipts and rows are
interpreter outputs, never request fields. Nat addresses range over a supplied
finite inventory; token IDs remain Fin 4. -/
namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
abbrev Token := FullNative.AccountExecution.Token
abbrev Supply := FullNative.AccountExecution.Supply

inductive Custody where
  | unallocated | reserved (recipient : Nat) | local (owner : Nat) | external | retired
  deriving DecidableEq, Repr

inductive Node where
  | hardware (address : Nat)
  | birth (ordinal : Nat)
  | event (ordinal : Nat)
  | version (ordinal : Nat)
  | prospective (left right : Node) (a b : Bool) (output : Nat)
  deriving DecidableEq, Repr

structure Accounts where
  custody : Token → Custody
  charge : Token → Bool
  cursor : Token → Nat

def tokens : List Token := [0,1,2,3]
def keys (a : Accounts) (owner : Nat) : List Token :=
  tokens.filter fun t => decide (a.custody t = .local owner)

def put {K X : Type} [DecidableEq K] (f : K → X) (k : K) (v : X) : K → X :=
  fun j => if j=k then v else f j

def transact (supply : Supply) (a : Accounts) (t : Token) : Accounts :=
  {a with charge := put a.charge t (supply t (a.cursor t)).isSome
          cursor := put a.cursor t (a.cursor t+1)}

structure Receipt where
  issuer : Custody
  owner : Nat
  token : Token
  cursor : Nat
  serial : Nat
  rom : ROM
  before : State
  after : State
  action : Bool
  weight : Nat
  packet : Option Unit
  deriving DecidableEq, Repr

structure Resident where
  owner : Nat
  installed : Option ROM
  current : State
  birth : Node
  version : Node
  birthCursor : Nat
  roots : List (Node × Nat)
  receipts : List Receipt
  deriving DecidableEq, Repr

structure Capture where
  program : ROM
  current : State
  sourceVersion : Node
  order : Nat
  count : Nat
  serial : Nat
  receipt : Receipt
  event : Node
  deriving DecidableEq, Repr

structure Slot where
  recipient : Nat
  key : Token
  capture : Capture
  deriving DecidableEq, Repr

inductive Event where
  | boot (address : Nat) (rom : ROM) (key : Token) (cursor : Nat)
  | native (before : Node) (receipt : Receipt) (conditional : Option Rat)
  | snapshot (source : Node) (captureReceipt : Receipt) (left right count : Nat)
  | activation (snapshot : Node) (address : Nat) (rom : ROM) (key : Token) (cursor : Nat) (state : State)
  | partition (parent : Node) (output : Nat) (rom : ROM) (ownedKeys : List Token) (state : State)
  | fusion (left right : Node) (output : Nat) (rom : ROM) (leftKeys rightKeys : List Token)
      (leftReceipt rightReceipt : Receipt) (probability : Rat)
  deriving DecidableEq, Repr

structure World where
  inventory : Nat
  residents : Nat → Option Resident
  fresh : Nat → Bool
  accounts : Accounts
  slots : Nat → Option Slot
  events : List Event
  acquisition : Bool

def initial (inventory : Nat := 8) (rom : ROM := .canonical32) : World :=
  { inventory := inventory
    residents := fun a => if a=0 ∧ 0<inventory then
      some ⟨0,some rom,⟨false,false,false,false,false⟩,.birth 0,.birth 0,0,[],[]⟩ else none
    fresh := fun a => decide (a<inventory ∧ a≠0)
    accounts := ⟨(fun t => if t=0 then .local 0 else if t=3 then .external else .unallocated),
      (fun _ => true),(fun _ => 0)⟩
    slots := fun _ => none
    events := [.boot 0 rom 0 0]
    acquisition := true }

def freshAddress (w : World) (a : Nat) : Bool :=
  decide (a<w.inventory) && w.fresh a && (w.residents a).isNone && (w.slots a).isNone

/-- Authenticate the address/version against the actual generated ledger,
including the installed ROM and current state. A supplied or stale node cannot
stand in for a generated live version. Full epoch package audits are separate. -/
def authenticVersion (w : World) (address : Nat) (r : Resident) : Bool :=
  match r.version with
  | .birth ordinal =>
    let common := decide (r.birth=.birth ordinal ∧ r.receipts=[])
    common && match w.events[ordinal]? with
    | some (.boot a rom _ _) => decide (a=address ∧ r.installed=some rom ∧
        r.current=⟨false,false,false,false,false⟩)
    | some (.activation _ a rom _ _ state) => decide (a=address ∧ r.installed=some rom ∧ r.current=state)
    | some (.partition _ a rom _ state) => decide (a=address ∧ r.installed=some rom ∧ r.current=state)
    | some (.fusion _ _ a rom _ _ left right _) => decide (a=address ∧ r.installed=some rom ∧
        r.current=left.after ∧ left.after=right.after)
    | _ => false
  | .version ordinal =>
    match w.events[ordinal]? with
    | some (.native _ receipt _) => decide (receipt.owner=address ∧ r.installed=some receipt.rom ∧
        r.current=receipt.after ∧ r.receipts.getLast?=some receipt)
    | _ => false
  | _ => false

/-- No fallback token: the primary is the least currently owned key, in the
fixed enumeration. Native operations never change that custody. -/
def binding (w : World) (a : Nat) : Option (Resident × ROM × Token) := do
  let r ← w.residents a
  let rom ← r.installed
  let key ← (keys w.accounts a).head?
  if decide (a<w.inventory ∧ r.owner=a) && authenticVersion w a r then some (r,rom,key) else none

def access (w : World) (a : Nat) : Option (Resident × ROM × Token) := do
  let (r,rom,key) ← binding w a
  if w.accounts.charge key then some (r,rom,key) else none

def makeReceipt (supply : Supply) (w : World) (owner : Nat) (r : Resident)
    (rom : ROM) (key : Token) (action : Bool) (edge : State × Nat) : Receipt :=
  ⟨w.accounts.custody key,owner,key,w.accounts.cursor key,
    4*w.accounts.cursor key+key.val,rom,r.current,edge.1,action,edge.2,
    supply key (w.accounts.cursor key)⟩

def advance (supply : Supply) (w : World) (owner : Nat) (r : Resident)
    (rom : ROM) (key : Token) (action : Bool) (edge : State × Nat)
    (conditional : Option Rat := none) : World :=
  let receipt := makeReceipt supply w owner r rom key action edge
  let next := {r with
    current := edge.1
    version := .version w.events.length
    receipts := r.receipts ++ [receipt]}
  {w with residents := put w.residents owner (some next)
          accounts := transact supply w.accounts key
          events := w.events ++ [.native r.version receipt conditional]}

def nativeRows (supply : Supply) (w : World) (a : Nat) (action : Bool) : List (World × Nat) :=
  match access w a with
  | none => []
  | some (r,rom,key) => (rom.program.rows r.current action).map fun e =>
      (advance supply w a r rom key action e,e.2)

def normalizedNative (supply : Supply) (w : World) (a : Nat) (action : Bool) :
    List (World × Rat) := (nativeRows supply w a action).map fun e => (e.1,(e.2 : Rat)/16)

theorem transaction_custody (supply : Supply) (a : Accounts) (t : Token) :
    (transact supply a t).custody = a.custody := rfl

theorem paid_cursor (supply : Supply) (a : Accounts) (t : Token) :
    (transact supply a t).cursor t = a.cursor t+1 := by simp [transact,put]

theorem paid_charge (supply : Supply) (a : Accounts) (t : Token) :
    (transact supply a t).charge t = (supply t (a.cursor t)).isSome := by simp [transact,put]

theorem other_cursor (supply : Supply) (a : Accounts) (t k : Token) (h : k≠t) :
    (transact supply a t).cursor k = a.cursor k := by simp [transact,put,h]

theorem other_charge (supply : Supply) (a : Accounts) (t k : Token) (h : k≠t) :
    (transact supply a t).charge k = a.charge k := by simp [transact,put,h]

theorem key_custody (a : Accounts) (owner : Nat) (key : Token) (h : key∈keys a owner) :
    a.custody key = .local owner := by
  exact of_decide_eq_true (List.mem_filter.mp h).2

theorem custody_exclusive (a : Accounts) (t : Token) (o p : Nat)
    (ho : a.custody t = .local o) (hp : a.custody t = .local p) : o=p := by
  rw [ho] at hp
  exact Custody.local.inj hp

theorem missing_program (w : World) (a : Nat) (r : Resident)
    (hr : w.residents a = some r) (h : r.installed=none) : access w a = none := by
  simp [access,binding,hr,h]

theorem missing_resident (w : World) (a : Nat) (h : w.residents a=none) : access w a=none := by
  simp [access,binding,h]

theorem native_rows_from_access (supply : Supply) (w : World) (a : Nat)
    (r : Resident) (rom : ROM) (key : Token) (h : access w a=some (r,rom,key)) (action : Bool) :
    nativeRows supply w a action = (rom.program.rows r.current action).map
      (fun e => (advance supply w a r rom key action e,e.2)) := by simp [nativeRows,h]

/-- Actual projection is indexed by the consumed installed ROM. -/
theorem installed_rom_projection (supply : Supply) (w : World) (a : Nat)
    (r : Resident) (rom : ROM) (key : Token) (h : access w a=some (r,rom,key)) (action : Bool) :
    (nativeRows supply w a action).map (fun e =>
      ((e.1.residents a).map Resident.current,e.2)) =
    (rom.program.rows r.current action).map (fun e => (some e.1,e.2)) := by
  simp [native_rows_from_access supply w a r rom key h action,List.map_map,advance,put]

end CSTTT.FullNative02
