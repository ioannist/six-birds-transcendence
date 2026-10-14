import CSTTT.FullNative02.EpochNative
import CSTTT.FullNative.ViabilityFactor

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem rom_maintenance_inside (rom : ROM) (s : State) :
    ∀ e∈rom.program.rows s false, e.1.outside=false ∧ e.1.phase= !s.phase := by
  cases rom <;> rcases s with ⟨p,u,v,r,c⟩ <;>
    cases p <;> cases u <;> cases v <;> cases r <;> cases c <;> decide +kernel

theorem rom_rows_nonempty (rom : ROM) (s : State) (action : Bool) :
    rom.program.rows s action≠[] := by
  intro empty
  have mass := (rom_rows_positive_normalized rom s action).2
  rw [empty] at mass
  contradiction

theorem native_nonempty (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token)
    (enabled : access w owner=some (r,rom,key)) (supply : Supply) (action : Bool) :
    nativeRows supply w owner action≠[] := by
  rw [native_rows_from_access _ _ _ _ _ _ enabled action]
  exact fun empty => rom_rows_nonempty rom r.current action (List.map_eq_nil_iff.mp empty)

theorem actual_response_progress (w : World) (owner : Nat) (r : Resident)
    (rom : ROM) (key : Token) (enabled : access w owner=some (r,rom,key))
    (v : World) (n : Nat) (support : (v,n)∈nativeRows renewable w owner false) :
    ∃ next, v.residents owner=some next ∧
      next.receipts.length=r.receipts.length+1 ∧ next.current.phase= !r.current.phase ∧
      v.accounts.cursor key=w.accounts.cursor key+1 ∧ v.accounts.charge key=true ∧
      next.birth=r.birth ∧ next.roots=r.roots ∧ next.installed=r.installed ∧
      v.accounts.custody key=.local owner ∧ 0<n := by
  rw [native_rows_from_access _ _ _ _ _ _ enabled false] at support
  obtain ⟨e,he,eq⟩ := List.mem_map.mp support
  have world : v=advance renewable w owner r rom key false e := (congrArg Prod.fst eq).symm
  have weight : n=e.2 := (congrArg Prod.snd eq).symm
  rw [world,weight]
  refine ⟨{r with
    current := e.1
    version := .version w.events.length
    receipts := r.receipts++[makeReceipt renewable w owner r rom key false e]},?_,?_,?_,?_,?_,
    rfl,rfl,rfl,?_,(rom_rows_positive_normalized rom r.current false).1 e he⟩
  · simp [advance,put]
  · simp
  · exact (rom_maintenance_inside rom r.current e he).2
  · exact paid_cursor renewable w.accounts key
  · simp [advance,paid_charge,renewable,AccountExecution.renewable]
  · exact actual_issuer renewable w owner r rom key enabled false e

def operationalCore (w : World) (owner : Nat) : Prop :=
  ∃ r rom key,access w owner=some (r,rom,key) ∧ r.current.outside=false

def safe (w : World) (owner : Nat) : Prop :=
  ∃ r,w.residents owner=some r ∧ r.current.outside=false

theorem operational_core_safe (w : World) (owner : Nat) (h : operationalCore w owner) : safe w owner := by
  obtain ⟨r,rom,key,enabled,inside⟩ := h
  exact ⟨r,(binding_facts _ _ _ _ _ (access_facts _ _ _ _ _ enabled).1).1,inside⟩

theorem operational_core_response (w : World) (owner : Nat) (h : operationalCore w owner)
    (v : World) (n : Nat) (support : (v,n)∈nativeRows renewable w owner false) : operationalCore v owner := by
  obtain ⟨r,rom,key,enabled,_⟩ := h
  rw [native_rows_from_access _ _ _ _ _ _ enabled false] at support
  obtain ⟨e,he,eq⟩ := List.mem_map.mp support
  have world : v=advance renewable w owner r rom key false e := (congrArg Prod.fst eq).symm
  rw [world]
  exact ⟨_,rom,key,renewable_access_after w owner r rom key enabled false e,
    (rom_maintenance_inside rom r.current e he).1⟩

theorem nonblocking_safe_core (supply : Supply) (w : World) (owner : Nat)
    (safety : safe w owner) (action : Bool) (enabledRows : nativeRows supply w owner action≠[]) :
    operationalCore w owner := by
  cases read : access w owner with
  | none => simp [nativeRows,read] at enabledRows
  | some data =>
    rcases data with ⟨r,rom,key⟩
    obtain ⟨s,present,inside⟩ := safety
    have actual := (binding_facts _ _ _ _ _ (access_facts _ _ _ _ _ read).1).1
    have same : s=r := Option.some.inj (present.symm.trans actual)
    subst s
    exact ⟨r,rom,key,read,inside⟩

end CSTTT.FullNative02
