import CSTTT.FullNative02.FusionAncestry

namespace CSTTT.FullNative02
set_option autoImplicit false

theorem binding_facts (w : World) (a : Nat) (r : Resident) (rom : ROM) (key : Token)
    (h : binding w a=some (r,rom,key)) :
    w.residents a=some r ∧ r.installed=some rom ∧ key∈keys w.accounts a ∧ r.owner=a ∧ a<w.inventory := by
  cases hr : w.residents a with
  | none => simp [binding,hr] at h
  | some resident =>
    cases hd : resident.installed with
    | none => simp [binding,hr,hd] at h
    | some program =>
      cases hk : (keys w.accounts a).head? with
      | none => simp [binding,hr,hd,hk] at h
      | some t =>
        by_cases hg : (decide (a<w.inventory ∧ resident.owner=a) && authenticVersion w a resident)=true
        · have same : (resident,program,t)=(r,rom,key) := by
            simpa only [binding,hr,hd,hk,Bind.bind,Option.bind,if_pos hg,Option.some.injEq] using h
          cases same
          have bounds : a<w.inventory ∧ r.owner=a := by
            have facts := hg
            simp only [Bool.and_eq_true,decide_eq_true_eq] at facts
            exact facts.1
          exact ⟨rfl,hd,List.mem_of_head? hk,bounds.2,bounds.1⟩
        · simp only [binding,hr,hd,hk,Bind.bind,Option.bind,if_neg hg] at h
          contradiction

theorem access_facts (w : World) (a : Nat) (r : Resident) (rom : ROM) (key : Token)
    (h : access w a=some (r,rom,key)) :
    binding w a=some (r,rom,key) ∧ w.accounts.charge key=true := by
  cases hv : binding w a with
  | none => simp [access,hv] at h
  | some entry =>
    rcases entry with ⟨resident,program,t⟩
    cases hc : w.accounts.charge t with
    | false => simp [access,hv,hc] at h
    | true =>
      have same : (resident,program,t)=(r,rom,key) := by simpa [access,hv,hc] using h
      cases same
      exact ⟨rfl,hc⟩

theorem actual_issuer (supply : Supply) (w : World) (a : Nat)
    (r : Resident) (rom : ROM) (key : Token) (h : access w a=some (r,rom,key))
    (action : Bool) (edge : FullNative.State × Nat) :
    (makeReceipt supply w a r rom key action edge).issuer=.local a :=
  key_custody w.accounts a key (binding_facts w a r rom key (access_facts w a r rom key h).1).2.2.1

theorem actual_packet (supply : Supply) (w : World) (a : Nat)
    (r : Resident) (rom : ROM) (key : Token) (action : Bool) (edge : FullNative.State × Nat) :
    (makeReceipt supply w a r rom key action edge).packet=supply key (w.accounts.cursor key) := rfl

theorem custody_tokens_disjoint (w : World) (a b : Nat) (different : a≠b) :
    ∀ t∈keys w.accounts a, t∉keys w.accounts b := by
  intro t ha hb
  exact different (custody_exclusive w.accounts t a b
    (key_custody w.accounts a t ha) (key_custody w.accounts b t hb))

theorem native_keeps_primary (supply : Supply) (w : World) (a : Nat)
    (r : Resident) (rom : ROM) (key : Token) (action : Bool) (edge : FullNative.State × Nat) :
    keys (advance supply w a r rom key action edge).accounts a=keys w.accounts a := rfl

theorem paid_inputs_use_distinct_ports (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (pair : Pair) (probability : Rat) (different : p.leftKey≠p.rightKey) :
    (paidParents supply w q p pair probability).accounts.cursor p.leftKey=w.accounts.cursor p.leftKey+1 ∧
    (paidParents supply w q p pair probability).accounts.cursor p.rightKey=w.accounts.cursor p.rightKey+1 := by
  constructor
  · simp [paidParents,advance,transact,put,different]
  · simp [paidParents,advance,transact,put,Ne.symm different]

theorem renewable_paid_inputs_charged (w : World) (q : FusionRequest)
    (p : Parents) (pair : Pair) (probability : Rat) :
    (paidParents FullNative.AccountExecution.renewable w q p pair probability).accounts.charge p.leftKey=true ∧
    (paidParents FullNative.AccountExecution.renewable w q p pair probability).accounts.charge p.rightKey=true := by
  constructor <;> simp [paidParents,advance,transact,put,FullNative.AccountExecution.renewable]

end CSTTT.FullNative02
