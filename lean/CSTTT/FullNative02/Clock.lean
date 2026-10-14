import CSTTT.FullNative02.RetainedHistory

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000

theorem rom_supported_phase (rom : ROM) (s : State) (action : Bool) :
    ∀ e∈rom.program.rows s action,e.1.phase= !s.phase := by
  cases rom <;> rcases s with ⟨p,u,v,r,c⟩ <;>
    cases p <;> cases u <;> cases v <;> cases r <;> cases c <;> cases action <;> decide +kernel

inductive Walk (owner : Nat) : World → List Bool → World → Prop where
  | root (w : World) : Walk owner w [] w
  | cons {w mid : World} (action : Bool) (n : Nat)
      (edge : (mid,n)∈nativeRows renewable w owner action)
      {rest : List Bool} {v : World} (tail : Walk owner mid rest v) : Walk owner w (action::rest) v

def tickAfter : List Bool → Bool → Bool
  | [],phase => phase
  | _::rest,phase => tickAfter rest (!phase)

theorem every_word_continues (owner : Nat) (w : World) (r : Resident) (rom : ROM) (key : Token)
    (enabled : access w owner=some (r,rom,key)) (word : List Bool) :
    ∃ v,Walk owner w word v := by
  induction word generalizing w r with
  | nil => exact ⟨w,.root w⟩
  | cons action rest ih =>
    obtain ⟨edge,supported⟩ := List.exists_mem_of_ne_nil _ (rom_rows_nonempty rom r.current action)
    let next := advance renewable w owner r rom key action edge
    have row : (next,edge.2)∈nativeRows renewable w owner action := by
      rw [native_rows_from_access _ _ _ _ _ _ enabled action]
      exact List.mem_map.mpr ⟨edge,supported,rfl⟩
    obtain ⟨v,tail⟩ := ih next _ (renewable_access_after w owner r rom key enabled action edge)
    exact ⟨v,.cons action edge.2 row tail⟩

theorem all_word_registers (owner : Nat) (w v : World) (r : Resident) (rom : ROM) (key : Token)
    (enabled : access w owner=some (r,rom,key)) (word : List Bool) (history : Walk owner w word v) :
    ∃ next,access v owner=some (next,rom,key) ∧
      next.receipts.length=r.receipts.length+word.length ∧
      v.accounts.cursor key=w.accounts.cursor key+word.length ∧
      next.current.phase=tickAfter word r.current.phase ∧ next.birth=r.birth ∧
      next.birthCursor=r.birthCursor ∧ next.roots=r.roots ∧ next.installed=r.installed ∧ next.owner=r.owner := by
  induction history generalizing r with
  | root w => exact ⟨r,enabled,by simp,by simp,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | @cons w mid action n edge rest v tail ih =>
    rw [native_rows_from_access _ _ _ _ _ _ enabled action] at edge
    obtain ⟨e,supported,equal⟩ := List.mem_map.mp edge
    have world : mid=advance renewable w owner r rom key action e := (congrArg Prod.fst equal).symm
    subst mid
    have after := renewable_access_after w owner r rom key enabled action e
    obtain ⟨next,live,length,cursor,phase,birth,birthCursor,roots,program,ownership⟩ := ih _ after
    refine ⟨next,live,?_,?_,?_,birth,birthCursor,roots,program,ownership⟩
    · simpa [List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using length
    · simpa [advance,paid_cursor,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cursor
    · simpa only [tickAfter,(rom_supported_phase rom r.current action e supported)] using phase

theorem maintained_walk_retained (owner : Nat) (start v : World) (n : Nat)
    (history : Walk owner start (List.replicate n false) v) : Retained owner start v := by
  induction n generalizing start with
  | zero => cases history; exact .root _
  | succ n ih =>
    cases history with
    | cons action weight edge tail =>
      have first : Retained owner start _ := .next (.root start) _ weight edge
      have rest := ih _ tail
      exact retained_trans owner _ _ _ first rest

end CSTTT.FullNative02
