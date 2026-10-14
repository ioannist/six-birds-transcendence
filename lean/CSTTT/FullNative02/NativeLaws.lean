import CSTTT.FullNative02.Ownership

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false

theorem binding_primary (w : World) (a : Nat) (r : Resident) (rom : ROM) (key : Token)
    (h : binding w a=some (r,rom,key)) : (keys w.accounts a).head?=some key := by
  have facts := binding_facts w a r rom key h
  cases hk : (keys w.accounts a).head? with
  | none => simp [binding,facts.1,facts.2.1,hk] at h
  | some t =>
    by_cases gate : (decide (a<w.inventory ∧ r.owner=a) && authenticVersion w a r)=true
    · have eq : (r,rom,t)=(r,rom,key) := by
        simpa only [binding,facts.1,facts.2.1,hk,Bind.bind,Option.bind,if_pos gate,Option.some.injEq] using h
      have same : t=key := congrArg (fun data => data.2.2) eq
      cases same
      rfl
    · simp only [binding,facts.1,facts.2.1,hk,Bind.bind,Option.bind,if_neg gate] at h
      contradiction

theorem renewable_access_after (w : World) (a : Nat) (r : Resident) (rom : ROM) (key : Token)
    (h : access w a=some (r,rom,key)) (action : Bool) (edge : State × Nat) :
    access (advance AccountExecution.renewable w a r rom key action edge) a=
      some ({r with
        current := edge.1
        version := .version w.events.length
        receipts := r.receipts++[makeReceipt AccountExecution.renewable w a r rom key action edge]},rom,key) := by
  have hb := (access_facts w a r rom key h).1
  have facts := binding_facts w a r rom key hb
  have head := binding_primary w a r rom key hb
  let next : Resident := {r with
    current := edge.1
    version := .version w.events.length
    receipts := r.receipts++[makeReceipt AccountExecution.renewable w a r rom key action edge]}
  let updated := advance AccountExecution.renewable w a r rom key action edge
  have read : updated.residents a=some next := by simp [updated,next,advance,put]
  have program : next.installed=some rom := facts.2.1
  have primary : (keys updated.accounts a).head?=some key := head
  have charge : updated.accounts.charge key=true := by
    simp [updated,advance,paid_charge,AccountExecution.renewable]
  have hi : (w.events++[Event.native r.version
      (makeReceipt AccountExecution.renewable w a r rom key action edge) none])[w.events.length]?=
      some (Event.native r.version (makeReceipt AccountExecution.renewable w a r rom key action edge) none) := by
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  have authentic : authenticVersion updated a next=true := by
    simp [authenticVersion,updated,next,advance,hi,makeReceipt,facts.2.1,List.getLast?_append]
  change access updated a=some (next,rom,key)
  simp only [access,binding,read,program,primary,Bind.bind,Option.bind]
  have bound : a<updated.inventory ∧ next.owner=a := ⟨facts.2.2.2.2,facts.2.2.2.1⟩
  simp [bound,authentic,charge]

/-- Exact physical future projection for every installed ROM and every Bool
word, at every actually enabled owned sector. Includes initial observation. -/
theorem actual_native_physical_future (w : World) (owner : Nat) (r : Resident)
    (rom : ROM) (key : Token) (h : access w owner=some (r,rom,key))
    (observe : State → Nat) (word : List Bool) (trace : List (Option Nat)) :
    WeightedFuture.law (fun w action => normalizedNative AccountExecution.renewable w owner action)
      (fun w => (w.residents owner).map (fun r => observe r.current)) w word trace=
    WeightedFuture.law (rationalRows rom.program) (fun s => some (observe s)) r.current word trace := by
  induction word generalizing w r trace with
  | nil => simp [WeightedFuture.law,(binding_facts _ _ _ _ _ (access_facts _ _ _ _ _ h).1).1]
  | cons action rest ih =>
    cases trace with
    | nil => rfl
    | cons v tail =>
      have read := (binding_facts _ _ _ _ _ (access_facts _ _ _ _ _ h).1).1
      simp only [WeightedFuture.law,read,Option.map_some,normalizedNative,
        native_rows_from_access _ _ _ _ _ _ h action,rationalRows,List.foldr_map]
      by_cases hv : v=some (observe r.current)
      · simp only [hv,if_true]
        congr 1
        funext edge acc
        have future := ih _ _ (renewable_access_after w owner r rom key h action edge) tail
        exact congrArg (fun z => (edge.2 : Rat)/16*z+acc) future
      · simp [hv]

end CSTTT.FullNative02
