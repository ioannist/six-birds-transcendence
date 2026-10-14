import CSTTT.FullNative02.Runtime

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 8000000

def readCapture (w : World) (source : Nat) : Option Capture := do
  let (r,rom,key) ← access w source
  let receipt ← r.receipts.getLast?
  let .version ordinal := r.version | none
  let .native _ recorded conditional ← w.events[ordinal]? | none
  if recorded=receipt ∧ conditional=none ∧ receipt.issuer=.local source ∧
      receipt.token=key ∧ receipt.rom=rom ∧ receipt.after=r.current ∧
      receipt.cursor+1=w.accounts.cursor key ∧
      receipt.serial=4*receipt.cursor+key.val ∧
      (receipt.after,receipt.weight)∈rom.program.rows receipt.before receipt.action then
    some ⟨rom,r.current,r.version,r.receipts.length,r.receipts.length,receipt.serial,
      receipt,.event w.events.length⟩
  else none

def writeSnapshot (w : World) (source left right : Nat) : Option World := do
  let capture ← readCapture w source
  if w.acquisition && freshAddress w left && freshAddress w right && decide (left≠right) &&
      decide (w.accounts.custody 1=.unallocated ∧ w.accounts.custody 2=.unallocated) &&
      w.accounts.charge 1 && w.accounts.charge 2 then
    some {w with
      slots := put (put w.slots left (some ⟨left,1,capture⟩)) right (some ⟨right,2,capture⟩)
      accounts := {w.accounts with
        custody := put (put w.accounts.custody 1 (.reserved left)) 2 (.reserved right)}
      events := w.events ++ [.snapshot capture.sourceVersion capture.receipt left right capture.count]}
  else none

def authenticSlot (w : World) (slot : Slot) : Bool :=
  match slot.capture.event with
  | .event ordinal =>
    match w.events[ordinal]? with
    | some (.snapshot source receipt left right count) =>
      decide (source=slot.capture.sourceVersion ∧ receipt=slot.capture.receipt ∧
        receipt.after=slot.capture.current ∧ receipt.rom=slot.capture.program ∧
        receipt.serial=slot.capture.serial ∧ count=slot.capture.order ∧
        count=slot.capture.count ∧ (slot.recipient=left ∨ slot.recipient=right))
    | _ => false
  | _ => false

def activate (w : World) (address : Nat) : Option World := do
  let slot ← w.slots address
  if decide (address<w.inventory ∧ slot.recipient=address ∧
      w.accounts.custody slot.key=.reserved address) && w.fresh address &&
      (w.residents address).isNone && authenticSlot w slot then
    let resident : Resident := ⟨address,some slot.capture.program,slot.capture.current,
      .birth w.events.length,.birth w.events.length,w.accounts.cursor slot.key,
      [(slot.capture.sourceVersion,slot.capture.count)],[]⟩
    some {w with
      residents := put w.residents address (some resident)
      fresh := put w.fresh address false
      slots := put w.slots address none
      accounts := {w.accounts with custody := put w.accounts.custody slot.key (.local address)}
      events := w.events ++ [.activation slot.capture.event address slot.capture.program
        slot.key (w.accounts.cursor slot.key) slot.capture.current]}
  else none

def bootstrap (w : World) (source left right : Nat) : Option World := do
  let staged ← writeSnapshot w source left right
  let first ← activate staged left
  activate first right

def sourceRetire (w : World) : World :=
  {w with
    residents := put w.residents 0 none
    accounts := {w.accounts with
      custody := fun t =>
        if w.accounts.custody t=.local 0 then .retired else w.accounts.custody t}}

def withdraw (w : World) : World :=
  let retired := sourceRetire w
  {retired with
    accounts := {retired.accounts with
      custody := fun t =>
        if retired.accounts.custody t=.external then .retired else retired.accounts.custody t}
    slots := fun _ => none
    acquisition := false}

def boot (w : World) (address : Nat) (key : Token) (rom : ROM) : Option World :=
  if w.acquisition && freshAddress w address &&
      decide (w.accounts.custody key=.unallocated) && w.accounts.charge key then
    let resident : Resident := ⟨address,some rom,⟨false,false,false,false,false⟩,
      .birth w.events.length,.birth w.events.length,w.accounts.cursor key,[],[]⟩
    some {w with
      residents := put w.residents address (some resident)
      fresh := put w.fresh address false
      accounts := {w.accounts with custody := put w.accounts.custody key (.local address)}
      events := w.events ++ [.boot address rom key (w.accounts.cursor key)]}
  else none

/-- Partition selectors are raw requests. Ownership, covering, disjointness
and freshness are checked against the installed parent; no witness is supplied. -/
def partition (w : World) (parent left right : Nat) (xs ys : List Token) : Option World := do
  let (r,rom,_) ← binding w parent
  let x ← (tokens.filter fun t => decide (t∈xs)).head?
  let y ← (tokens.filter fun t => decide (t∈ys)).head?
  if freshAddress w left && freshAddress w right && decide (left≠right) &&
      decide (xs.Nodup ∧ ys.Nodup ∧
        (∀ t ∈ tokens, (t∈xs ∨ t∈ys) ↔ t∈keys w.accounts parent) ∧
        (∀ t ∈ xs, t∉ys)) then
    let first : Resident := ⟨left,some rom,r.current,.birth w.events.length,
      .birth w.events.length,w.accounts.cursor x,[(r.version,r.receipts.length)],[]⟩
    let second : Resident := ⟨right,some rom,r.current,.birth (w.events.length+1),
      .birth (w.events.length+1),w.accounts.cursor y,[(r.version,r.receipts.length)],[]⟩
    some {w with
      residents := put (put (put w.residents parent none) left (some first)) right (some second)
      fresh := put (put w.fresh left false) right false
      accounts := {w.accounts with
        custody := fun t =>
          if t∈xs then .local left else if t∈ys then .local right else w.accounts.custody t}
      events := w.events ++ [.partition r.version left rom xs r.current,
        .partition r.version right rom ys r.current]}
  else none

theorem retirement_keeps_slots (w : World) : (sourceRetire w).slots=w.slots := rfl
theorem retirement_keeps_charge (w : World) : (sourceRetire w).accounts.charge=w.accounts.charge := rfl
theorem withdrawal_keeps_charge (w : World) : (withdraw w).accounts.charge=w.accounts.charge := rfl
theorem withdrawal_keeps_cursors (w : World) : (withdraw w).accounts.cursor=w.accounts.cursor := rfl
theorem withdrawal_clears_authority (w : World) : (withdraw w).acquisition=false := rfl
theorem no_boot_after_withdraw (w : World) (a : Nat) (t : Token) (rom : ROM) :
    boot (withdraw w) a t rom=none := by simp [boot,withdraw]

theorem live_transferred_key_survives_withdrawal (w : World) (t : Token) (owner : Nat)
    (h : w.accounts.custody t=.local owner) (different : owner≠0) :
    (withdraw w).accounts.custody t=.local owner := by
  simp [withdraw,sourceRetire,h,different]

end CSTTT.FullNative02
