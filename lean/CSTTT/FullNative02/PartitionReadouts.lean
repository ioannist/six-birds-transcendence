import CSTTT.FullNative02.HousedAccounts

namespace CSTTT.FullNative02
set_option autoImplicit false

/-- Exact public readout for every successful partition, including copied ROM
and physical state, cold local records, complete custody and actual cursors. -/
theorem partition_actual_readout (w v : World) (parent left right : Nat) (xs ys : List Token)
    (h : partition w parent left right xs ys=some v) :
    ∃ r rom key x y, binding w parent=some (r,rom,key) ∧
      (tokens.filter fun t => decide (t∈xs)).head?=some x ∧
      (tokens.filter fun t => decide (t∈ys)).head?=some y ∧
      (∀ t, (t∈xs ∨ t∈ys) ↔ w.accounts.custody t=.local parent) ∧
      (∀ t∈xs, t∉ys) ∧
      (v.residents left).map (fun child =>
        (child.installed,child.current,child.birthCursor,child.receipts))=
          some (some rom,r.current,w.accounts.cursor x,[]) ∧
      (v.residents right).map (fun child =>
        (child.installed,child.current,child.birthCursor,child.receipts))=
          some (some rom,r.current,w.accounts.cursor y,[]) ∧
      (∀ t, v.accounts.custody t=
        if t∈xs then .local left else if t∈ys then .local right else w.accounts.custody t) ∧
      v.accounts.charge=w.accounts.charge ∧ v.accounts.cursor=w.accounts.cursor := by
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
        simp only [partition,hb,hx,hy,Bind.bind,Option.bind] at h
        split at h
        · rename_i gate
          simp only [Bool.and_eq_true,decide_eq_true_eq] at gate
          have distinct := gate.1.2
          have cover := gate.2.2.2.1
          have disjoint := gate.2.2.2.2
          cases Option.some.inj h
          refine ⟨r,rom,key,x,y,rfl,rfl,rfl,?_,disjoint,?_,?_,?_,rfl,rfl⟩
          · intro t
            simpa [keys,every_token_enumerated t] using cover t (every_token_enumerated t)
          · simp [put,distinct]
          · simp [put]
          · intro t; rfl
        · contradiction

end CSTTT.FullNative02
