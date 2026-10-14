import CSTTT.FullNative02.Temporal

namespace CSTTT.FullNative02.Epoch
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

theorem valid_append (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token)
    (enabled : access w owner=some (r,rom,key)) (audited : valid w owner r rom key=true)
    (action : Bool) (e : State × Nat) (supported : e∈rom.program.rows r.current action) :
    valid (advance renewable w owner r rom key action e) owner
      {r with
        current := e.1
        version := .version w.events.length
        receipts := r.receipts++[makeReceipt renewable w owner r rom key action e]} rom key=true := by
  have funded := (access_facts _ _ _ _ _ enabled).2
  have issued := actual_issuer renewable w owner r rom key enabled action e
  cases node : r.birth <;> simp only [valid,node] at audited ⊢
  case birth ordinal =>
    cases decoded : birth (w.events.take (ordinal+1)) owner ordinal with
    | none => simp [decoded] at audited
    | some b =>
      simp only [decoded,Bool.and_eq_true,decide_eq_true_eq] at audited
      rcases audited with ⟨authentic,bound,program,primary,cursor,roots,state,version,records,
        finalCursor,finalCharge,recordedCursor⟩
      have cut : (w.events++[Event.native r.version
          (makeReceipt renewable w owner r rom key action e) none]).take (ordinal+1)=
          w.events.take (ordinal+1) := by
        exact List.take_append_of_le_length (by omega)
      have past : (w.events++[Event.native r.version
          (makeReceipt renewable w owner r rom key action e) none]).take ordinal=
          w.events.take ordinal := List.take_append_of_le_length (by omega)
      simp only [advance]
      simp only [cut,decoded,past]
      rw [replay_append owner ordinal _ b w.events _ (by omega)]
      simp only [List.zipIdx_cons,List.zipIdx_nil,List.foldl_cons,List.foldl_nil]
      simp [step,makeReceipt,program,primary,←state,←version,←records,←finalCursor,
        ←finalCharge,funded,issued,authentic,supported,cursor,roots,recordedCursor,
        transact,put,renewable,AccountExecution.renewable,List.length_append,bound]
      exact ⟨issued,by omega⟩
  all_goals contradiction

def accept (w : World) (owner : Nat) : Bool :=
  match access w owner with
  | none => false
  | some (r,rom,key) => decide (rom=.canonical32) && !r.current.outside &&
      valid w owner r rom key && Blocks.evidence rom owner r.receipts

theorem accepted_access (w : World) (owner : Nat) (h : accept w owner=true) :
    ∃ r key, access w owner=some (r,.canonical32,key) ∧ r.current.outside=false ∧
      valid w owner r .canonical32 key=true ∧ Blocks.evidence .canonical32 owner r.receipts=true := by
  cases read : access w owner with
  | none => simp [accept,read] at h
  | some entry =>
    rcases entry with ⟨r,rom,key⟩
    simp only [accept,read,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true,and_assoc] at h
    rcases h with ⟨same,inside,audit,block⟩
    subst rom
    exact ⟨r,key,rfl,by simpa using inside,audit,block⟩

theorem accepted_native_append (w : World) (owner : Nat) (h : accept w owner=true)
    (v : World) (n : Nat) (edge : (v,n)∈nativeRows renewable w owner false) : accept v owner=true := by
  obtain ⟨r,key,enabled,inside,audit,block⟩ := accepted_access w owner h
  rw [native_rows_from_access _ _ _ _ _ _ enabled false] at edge
  obtain ⟨e,support,equal⟩ := List.mem_map.mp edge
  have world : v=advance renewable w owner r .canonical32 key false e := (congrArg Prod.fst equal).symm
  rw [world]
  have next := renewable_access_after w owner r .canonical32 key enabled false e
  have authenticated := valid_append w owner r .canonical32 key enabled audit false e support
  have retained := Blocks.append_keeps_evidence .canonical32 owner r.receipts
    [makeReceipt renewable w owner r .canonical32 key false e] block
  have targetInside : e.1.outside=false := by
    simp only [ROM.program,model,rows,Bool.false_eq_true,if_false] at support
    obtain ⟨uv,_,hm⟩ := List.mem_flatMap.mp support
    obtain ⟨rep,_,equal⟩ := List.mem_map.mp hm
    exact (congrArg (fun x : State × Nat => x.1.outside) equal).symm
  simp only [accept,next]
  simp [authenticated,retained,targetInside]

end CSTTT.FullNative02.Epoch
