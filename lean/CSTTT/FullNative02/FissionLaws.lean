import CSTTT.FullNative02.Ownership

namespace CSTTT.FullNative02
set_option autoImplicit false

theorem fresh_is_unoccupied (w : World) (a : Nat) (h : freshAddress w a=true) :
    w.residents a=none := by
  cases hr : w.residents a with
  | none => rfl
  | some resident => simp [freshAddress,hr] at h

theorem activation_guarantees (w v : World) (a : Nat) (h : activate w a=some v) :
    ∃ slot, w.slots a=some slot ∧
      (v.residents a).map Resident.installed=some (some slot.capture.program) ∧
      (v.residents a).map Resident.current=some slot.capture.current ∧
      (v.residents a).map Resident.receipts=some [] ∧ v.fresh a=false ∧
      v.slots a=none ∧ v.accounts.custody slot.key=.local a ∧
      v.accounts.charge=w.accounts.charge ∧ v.accounts.cursor=w.accounts.cursor ∧
      v.events=w.events++[.activation slot.capture.event a slot.capture.program
        slot.key (w.accounts.cursor slot.key) slot.capture.current] := by
  cases hs : w.slots a with
  | none => simp [activate,hs] at h
  | some slot =>
    simp only [activate,hs,Option.bind_some] at h
    dsimp only [Bind.bind,Option.bind] at h
    split at h
    · have eq := Option.some.inj h
      subst v
      refine ⟨slot,rfl,?_⟩
      simp [put]
    · contradiction

theorem activation_snapshot_path (w v : World) (a : Nat) (h : activate w a=some v) :
    ∃ slot, w.slots a=some slot ∧ ancestry v slot.capture.event (.birth w.events.length) := by
  obtain ⟨slot,read,_,_,_,_,_,_,_,_,events⟩ := activation_guarantees w v a h
  refine ⟨slot,read,Path.one ?_⟩
  simp [ledgerEdges,events,ledger_append,ledgerEdgesFrom,eventEdges]

theorem activation_preserves_old_ancestry (w v : World) (a : Nat) (h : activate w a=some v)
    (x y : Node) (old : ancestry w x y) : ancestry v x y := by
  obtain ⟨slot,_,_,_,_,_,_,_,_,_,events⟩ := activation_guarantees w v a h
  apply path_mono (es := ledgerEdges w) (x := x) (y := y) ?_ old
  intro e he
  simp only [ledgerEdges,events,ledger_append,Nat.zero_add]
  exact List.mem_append_left _ he

theorem partition_stock_and_caps (w v : World) (parent left right : Nat) (xs ys : List Token)
    (h : partition w parent left right xs ys=some v) :
    v.accounts.charge=w.accounts.charge ∧ v.accounts.cursor=w.accounts.cursor ∧
      v.fresh left=false ∧ v.fresh right=false ∧
      (v.residents left).map Resident.receipts=some [] ∧
      (v.residents right).map Resident.receipts=some [] := by
  cases hb : binding w parent with
  | none => simp [partition,hb] at h
  | some data =>
    rcases data with ⟨r,rom,key⟩
    cases hx : (tokens.filter fun t => decide (t∈xs)).head? with
    | none => simp [partition,hb,hx] at h
    | some x =>
      cases hy : (tokens.filter fun t => decide (t∈ys)).head? with
      | none => simp [partition,hb,hx,hy] at h
      | some y =>
        simp only [partition,hb,hx,hy,Option.bind_some] at h
        dsimp only [Bind.bind,Option.bind] at h
        split at h
        · rename_i gate
          have distinct : left≠right := by
            simp only [Bool.and_eq_true,decide_eq_true_eq] at gate
            omega
          have eq := Option.some.inj h
          subst v
          simp [put,distinct]
        · contradiction

end CSTTT.FullNative02
