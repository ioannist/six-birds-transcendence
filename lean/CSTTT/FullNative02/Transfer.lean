import CSTTT.FullNative02.HousedAccounts

namespace CSTTT.FullNative02
set_option autoImplicit false

theorem no_phantom_output_custody (w : World) (q : FusionRequest) (p : Parents)
    (view : parentView w q=some p) (housed : Housed w) :
    ∀ t, w.accounts.custody t≠.local q.output := by
  have vacant := fresh_is_unoccupied w q.output (fusion_guard_facts w q p view).2.2.2.2.2.2.1
  intro t owned
  obtain ⟨resident,read,_,_⟩ := housed t q.output owned
  rw [vacant] at read
  cases read

theorem fusion_output_keys_exact (supply : Supply) (w : World) (q : FusionRequest) (p : Parents)
    (view : parentView w q=some p) (housed : Housed w) (pair : Pair) (probability : Rat) :
    keys (settle supply w q p pair probability).world.accounts q.output =
      tokens.filter (fun t => decide (w.accounts.custody t=.local q.left ∨ w.accounts.custody t=.local q.right)) := by
  have noPhantom := no_phantom_output_custody w q p view housed
  apply congrArg (fun predicate : Token → Bool => tokens.filter predicate)
  funext t
  by_cases owned : w.accounts.custody t=.local q.left ∨ w.accounts.custody t=.local q.right
  · simp [settle,paidParents,advance,transact,owned]
  · simp [settle,paidParents,advance,transact,owned,noPhantom t]

theorem fusion_nonparent_custody (supply : Supply) (w : World) (q : FusionRequest) (p : Parents)
    (pair : Pair) (probability : Rat) (t : Token)
    (outside : ¬(w.accounts.custody t=.local q.left ∨ w.accounts.custody t=.local q.right)) :
    (settle supply w q p pair probability).world.accounts.custody t=w.accounts.custody t := by
  simp [settle,paidParents,advance,transact,outside]

theorem guarded_output_primary (w : World) (q : FusionRequest) (p : Parents)
    (view : parentView w q=some p) :
    (tokens.filter fun t => decide (w.accounts.custody t=.local q.left ∨
      w.accounts.custody t=.local q.right)).head?=some p.outputKey := by
  cases hl : access w q.left with
  | none => simp [parentView,hl] at view
  | some ld =>
    rcases ld with ⟨l,rom,lk⟩
    cases hr : access w q.right with
    | none => simp [parentView,hl,hr] at view
    | some rd =>
      rcases rd with ⟨r,rr,rk⟩
      cases hk : (tokens.filter fun t => decide (w.accounts.custody t=.local q.left ∨
          w.accounts.custody t=.local q.right)).head? with
      | none => simp only [parentView,hl,hr,hk,Bind.bind,Option.bind] at view; contradiction
      | some key =>
        simp only [parentView,hl,hr,hk,Bind.bind,Option.bind] at view
        split at view
        · cases Option.some.inj view
          rfl
        · contradiction

theorem inherited_least_primary (supply : Supply) (w : World) (q : FusionRequest) (p : Parents)
    (view : parentView w q=some p) (housed : Housed w) (pair : Pair) (probability : Rat) :
    (keys (settle supply w q p pair probability).world.accounts q.output).head?=some p.outputKey := by
  rw [fusion_output_keys_exact supply w q p view housed pair probability]
  exact guarded_output_primary w q p view

end CSTTT.FullNative02
