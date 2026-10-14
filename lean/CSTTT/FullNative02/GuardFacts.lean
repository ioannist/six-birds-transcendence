import CSTTT.FullNative02.FissionLaws

namespace CSTTT.FullNative02
set_option autoImplicit false

theorem fusion_guard_facts (w : World) (q : FusionRequest) (p : Parents)
    (h : parentView w q=some p) :
    access w q.left=some (p.left,p.rom,p.leftKey) ∧
    access w q.right=some (p.right,p.rom,p.rightKey) ∧
    q.left≠q.right ∧ p.leftKey≠p.rightKey ∧
    p.left.version=q.leftVersion ∧ p.right.version=q.rightVersion ∧
    freshAddress w q.output=true ∧ q.left≠q.output ∧ q.right≠q.output := by
  cases hl : access w q.left with
  | none => simp [parentView,hl] at h
  | some leftData =>
    rcases leftData with ⟨left,rom,leftKey⟩
    cases hr : access w q.right with
    | none => simp [parentView,hl,hr] at h
    | some rightData =>
      rcases rightData with ⟨right,rightROM,rightKey⟩
      cases hk : (tokens.filter fun t => decide
          (w.accounts.custody t=.local q.left ∨ w.accounts.custody t=.local q.right)).head? with
      | none =>
        simp only [parentView,hl,hr,hk,Bind.bind,Option.bind] at h
        contradiction
      | some outputKey =>
        by_cases gate : q.left≠q.right ∧ rom=rightROM ∧ leftKey≠rightKey ∧
            left.version=q.leftVersion ∧ right.version=q.rightVersion ∧
            freshAddress w q.output=true ∧
            (∀ t∈keys w.accounts q.left, t∉keys w.accounts q.right)
        · have same : Parents.mk left right rom leftKey rightKey outputKey=p := by
            simpa only [parentView,hl,hr,hk,Bind.bind,Option.bind,if_pos gate,Option.some.injEq] using h
          cases same
          rcases gate with ⟨different,program,keysDifferent,leftVersion,rightVersion,fresh,_⟩
          subst rightROM
          have leftRead := (binding_facts w q.left left rom leftKey (access_facts w q.left left rom leftKey hl).1).1
          have rightRead := (binding_facts w q.right right rom rightKey (access_facts w q.right right rom rightKey hr).1).1
          have vacant := fresh_is_unoccupied w q.output fresh
          have ld : q.left≠q.output := by
            intro eq
            rw [eq,vacant] at leftRead
            cases leftRead
          have rd : q.right≠q.output := by
            intro eq
            rw [eq,vacant] at rightRead
            cases rightRead
          exact ⟨rfl,rfl,different,keysDifferent,leftVersion,rightVersion,fresh,ld,rd⟩
        · simp only [parentView,hl,hr,hk,Bind.bind,Option.bind,if_neg gate] at h
          contradiction

theorem guarded_parents_retired (supply : Supply) (w : World) (q : FusionRequest) (p : Parents)
    (view : parentView w q=some p) (pair : Pair) (probability : Rat) :
    (settle supply w q p pair probability).world.residents q.left=none ∧
    (settle supply w q p pair probability).world.residents q.right=none := by
  have facts := fusion_guard_facts w q p view
  exact parents_retired supply w q p pair probability facts.2.2.2.2.2.2.2.1 facts.2.2.2.2.2.2.2.2

theorem guarded_actual_issuers (supply : Supply) (w : World) (q : FusionRequest) (p : Parents)
    (view : parentView w q=some p) (pair : Pair) (probability : Rat) :
    (makeReceipt supply w q.left p.left p.rom p.leftKey q.leftAction (pair.1.state,pair.1.weight)).issuer=
      .local q.left ∧
    (makeReceipt supply
      (advance supply w q.left p.left p.rom p.leftKey q.leftAction
        (pair.1.state,pair.1.weight) (some probability))
      q.right p.right p.rom p.rightKey q.rightAction (pair.2.state,pair.2.weight)).issuer=.local q.right := by
  have facts := fusion_guard_facts w q p view
  constructor
  · exact actual_issuer supply w q.left p.left p.rom p.leftKey facts.1 _ _
  · change w.accounts.custody p.rightKey=.local q.right
    exact key_custody w.accounts q.right p.rightKey
      (binding_facts w q.right p.right p.rom p.rightKey (access_facts w q.right p.right p.rom p.rightKey facts.2.1).1).2.2.1

end CSTTT.FullNative02
