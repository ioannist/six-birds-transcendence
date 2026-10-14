import CSTTT.FullNative02.Response

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false

theorem binding_after (supply : Supply) (w : World) (owner : Nat) (r : Resident)
    (rom : ROM) (key : Token) (h : access w owner=some (r,rom,key))
    (action : Bool) (edge : State × Nat) :
    binding (advance supply w owner r rom key action edge) owner=
      some ({r with
        current := edge.1
        version := .version w.events.length
        receipts := r.receipts++[makeReceipt supply w owner r rom key action edge]},rom,key) := by
  have hb := (access_facts w owner r rom key h).1
  have facts := binding_facts w owner r rom key hb
  have head := binding_primary w owner r rom key hb
  let next : Resident := {r with
    current := edge.1
    version := .version w.events.length
    receipts := r.receipts++[makeReceipt supply w owner r rom key action edge]}
  let updated := advance supply w owner r rom key action edge
  have read : updated.residents owner=some next := by simp [updated,next,advance,put]
  have program : next.installed=some rom := facts.2.1
  have primary : (keys updated.accounts owner).head?=some key := head
  have hi : (w.events++[Event.native r.version
      (makeReceipt supply w owner r rom key action edge) none])[w.events.length]?=
      some (Event.native r.version (makeReceipt supply w owner r rom key action edge) none) := by
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  have authenticated : authenticVersion updated owner next=true := by
    simp [authenticVersion,updated,next,advance,hi,makeReceipt,facts.2.1,List.getLast?_append]
  change binding updated owner=some (next,rom,key)
  simp only [binding,read,program,primary,Bind.bind,Option.bind]
  have bound : owner<updated.inventory ∧ next.owner=owner := ⟨facts.2.2.2.2,facts.2.2.2.1⟩
  simp [bound,authenticated]

theorem absent_access_after (w : World) (owner : Nat) (r : Resident)
    (rom : ROM) (key : Token) (h : access w owner=some (r,rom,key))
    (action : Bool) (edge : State × Nat) :
    access (advance absent w owner r rom key action edge) owner=none := by
  simp only [access,binding_after absent w owner r rom key h action edge,Bind.bind,Option.bind]
  simp [advance,paid_charge,absent,AccountExecution.absentSupply]

def quote (w : World) (owner : Nat) : Option (State × Bool) :=
  (binding w owner).map fun data => (data.1.current,w.accounts.charge data.2.2)

theorem native_factor_projection (renew : Bool) (w : World) (owner : Nat)
    (r : Resident) (rom : ROM) (key : Token) (h : access w owner=some (r,rom,key)) (action : Bool) :
    (nativeRows (if renew then renewable else absent) w owner action).map
      (fun e => (quote e.1 owner,e.2))=
    (rom.program.rows r.current action).map fun e => (some (e.1,renew),e.2) := by
  rw [native_rows_from_access _ _ _ _ _ _ h action]
  simp only [List.map_map,Function.comp_def,quote,binding_after _ _ _ _ _ _ h]
  cases renew <;> simp [advance,transact,put,renewable,absent,
    AccountExecution.renewable,AccountExecution.absentSupply]

end CSTTT.FullNative02
