import CSTTT.FullNative02.IAPS
import CSTTT.FullNative02.FactorViability

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000

theorem chain_inside (r : Receipt) (rest : List Receipt) (chain : Blocks.consecutive (r::rest)=true)
    (headInside : r.before.outside=false) (afterInside : ∀ receipt∈r::rest,receipt.after.outside=false) :
    ∀ receipt∈r::rest,receipt.before.outside=false := by
  induction rest generalizing r with
  | nil => intro receipt h; simp only [List.mem_singleton] at h; subst receipt; exact headInside
  | cons s tail ih =>
    have pieces : decide (r.after=s.before)=true ∧ Blocks.consecutive (s::tail)=true := by
      simpa only [Blocks.consecutive,Bool.and_eq_true] using chain
    have adjacent : r.after=s.before := of_decide_eq_true pieces.1
    have inside : s.before.outside=false := adjacent ▸ afterInside r (by simp)
    intro receipt member
    rcases List.mem_cons.mp member with same | remaining
    · subst receipt; exact headInside
    · exact ih s pieces.2 inside
        (fun receipt member => afterInside receipt (List.mem_cons_of_mem _ member)) receipt remaining

theorem qualifying_block_inside (rom : ROM) (owner : Nat) (r : Receipt) (rest : List Receipt)
    (qualified : Blocks.qualifies rom owner (r::rest)=true) :
    ∀ receipt∈r::rest,receipt.before.outside=false ∧ receipt.after.outside=false := by
  have pieces := qualified
  simp only [Blocks.qualifies,List.isEmpty_cons,Bool.not_false,Bool.true_and,
    Bool.and_eq_true,decide_eq_true_eq,and_assoc] at pieces
  obtain ⟨chain,closed,owned,_⟩ := pieces
  have after : ∀ receipt∈r::rest,receipt.after.outside=false := by
    intro receipt member
    have facts := List.all_eq_true.mp owned receipt member
    simp only [Bool.and_eq_true,decide_eq_true_eq] at facts
    exact (rom_maintenance_inside rom receipt.before (receipt.after,receipt.weight) facts.1.2.2.2.2).1
  have loop : r.before=((r::rest).getLast (by simp)).after := by
    simpa only [List.head?_cons,List.getLast?_eq_some_getLast (l:=r::rest) (by simp),
      Option.map_some,Option.some.injEq] using closed
  have head : r.before.outside=false := by
    rw [loop]
    exact after _ (List.getLast_mem (by simp))
  exact fun receipt member => ⟨chain_inside r rest chain head after receipt member,after receipt member⟩

theorem current_maintained_generator_irreversible (w : World) (owner : Nat)
    (accepted : Package.Accept02 w owner=true) :
    ¬∃ measure : State → Rat,(∀ s,s.outside=false→measure s≠0) ∧
      ∀ s t,s.outside=false→t.outside=false→
        measure s*Blocks.edge .canonical32 s t=measure t*Blocks.edge .canonical32 t s := by
  obtain ⟨r,key,enabled,_,_,evidence⟩ := Epoch.accepted_access w owner accepted
  obtain ⟨block,_,qualified⟩ := List.any_eq_true.mp evidence
  cases block with
  | nil => simp [Blocks.qualifies] at qualified
  | cons first rest =>
    intro reversible
    obtain ⟨measure,positive,balance⟩ := reversible
    have inside := qualifying_block_inside .canonical32 owner first rest qualified
    exact Blocks.qualifying_block_no_local_balance _ _ _ _ qualified measure
      (positive _ (inside first (by simp)).1)
      (fun receipt member => balance _ _ (inside receipt member).1 (inside receipt member).2)

theorem every_maintained_owner_has_positive_loop_access (w : World) (owner : Nat)
    (accepted : Package.Accept02 w owner=true) :
    ∃ r key first rest,access w owner=some (r,.canonical32,key) ∧
      (first::rest)∈Blocks.blocks r.receipts ∧ Blocks.qualifies .canonical32 owner (first::rest)=true ∧
      ∀ v other current primary,access v other=some (current,.canonical32,primary)→
        current.current.outside=false→∃ next result,Retained other v next ∧
          access next other=some (result,.canonical32,primary) ∧ result.current=first.before := by
  obtain ⟨r,key,enabled,_,_,evidence⟩ := Epoch.accepted_access w owner accepted
  obtain ⟨block,member,qualified⟩ := List.any_eq_true.mp evidence
  cases block with
  | nil => simp [Blocks.qualifies] at qualified
  | cons first rest =>
    have inside := (qualifying_block_inside .canonical32 owner first rest qualified first (by simp)).1
    exact ⟨r,key,first,rest,enabled,member,qualified,
      fun v other current primary live _ => owned_reaches_every_inside other v current primary live first.before inside⟩

theorem flat_inside_symmetric (s t : State) (hs : s.outside=false) (ht : t.outside=false) :
    Blocks.edge .flat32 s t=Blocks.edge .flat32 t s := by
  rcases s with ⟨p,u,v,r,c⟩
  rcases t with ⟨q,x,y,j,d⟩
  cases p <;> cases q <;> try contradiction
  cases u <;> cases v <;> cases r <;> cases c <;>
    cases x <;> cases y <;> cases j <;> cases d <;> decide +kernel

theorem flat_qualifying_block_impossible (owner : Nat) (rs : List Receipt) :
    Blocks.qualifies .flat32 owner rs=false := by
  cases result : Blocks.qualifies .flat32 owner rs
  · rfl
  · cases rs with
    | nil => simp [Blocks.qualifies] at result
    | cons first rest =>
      have inside := qualifying_block_inside .flat32 owner first rest result
      have products : Blocks.forward (Blocks.edge .flat32) Receipt.before Receipt.after (first::rest)=
          Blocks.backward (Blocks.edge .flat32) Receipt.before Receipt.after (first::rest) := by
        unfold Blocks.forward Blocks.backward
        congr 1
        apply List.map_congr_left
        intro receipt member
        exact flat_inside_symmetric _ _ (inside receipt member).1 (inside receipt member).2
      simp [Blocks.qualifies,Blocks.directional,products] at result

theorem flat_all_new_blocks_rejected (owner : Nat) (rs : List Receipt) :
    Blocks.evidence .flat32 owner rs=false := by
  simp [Blocks.evidence,flat_qualifying_block_impossible]

end CSTTT.FullNative02
