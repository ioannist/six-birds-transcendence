import CSTTT.FullNative02.History

namespace CSTTT.FullNative02
set_option autoImplicit false
set_option maxHeartbeats 16000000

def Housed (w : World) : Prop :=
  ∀ t a, w.accounts.custody t=.local a →
    ∃ r, w.residents a=some r ∧ r.owner=a ∧ a<w.inventory

theorem initial_housed (inventory : Nat) (rom : ROM) (size : 4≤inventory) :
    Housed (initial inventory rom) := by
  intro t a owned
  simp only [initial] at owned
  split at owned
  · cases owned
    refine ⟨⟨0,some rom,⟨false,false,false,false,false⟩,.birth 0,.birth 0,0,[],[]⟩,?_,?_,?_⟩
    · simp [initial,show 0<inventory by omega] <;> rfl
    · rfl
    · exact Nat.lt_of_lt_of_le (by decide : 0<4) size
  · split at owned <;> cases owned

theorem advance_housed (supply : Supply) (w : World) (a : Nat) (r : Resident)
    (rom : ROM) (key : Token) (action : Bool) (edge : FullNative.State × Nat)
    (conditional : Option Rat) (old : Housed w) (owner : r.owner=a) (bound : a<w.inventory) :
    Housed (advance supply w a r rom key action edge conditional) := by
  intro t b owned
  change w.accounts.custody t=.local b at owned
  by_cases same : b=a
  · subst b
    refine ⟨{r with current := edge.1, version := .version w.events.length, receipts := r.receipts ++ [makeReceipt supply w a r rom key action edge]},?_,?_,?_⟩
    · simp [advance,put] <;> rfl
    · exact owner
    · exact bound
  · obtain ⟨resident,read,name,limit⟩ := old t b owned
    refine ⟨resident,?_,name,limit⟩
    simpa [advance,put,same] using read

theorem fusion_housed (supply : Supply) (w : World) (q : FusionRequest) (p : Parents)
    (view : parentView w q=some p) (pair : Pair) (probability : Rat) (old : Housed w) :
    Housed (settle supply w q p pair probability).world := by
  have facts := fusion_guard_facts w q p view
  have lb := binding_facts w q.left p.left p.rom p.leftKey (access_facts _ _ _ _ _ facts.1).1
  have rb := binding_facts w q.right p.right p.rom p.rightKey (access_facts _ _ _ _ _ facts.2.1).1
  have bound : q.output<w.inventory := by
    have fresh := facts.2.2.2.2.2.2.1
    simp only [freshAddress,Bool.and_eq_true,decide_eq_true_eq] at fresh
    exact fresh.1.1.1
  intro t a owned
  by_cases transferred : w.accounts.custody t=.local q.left ∨ w.accounts.custody t=.local q.right
  · have new := every_parent_token_transferred supply w q p pair probability t transferred
    have same := custody_exclusive (settle supply w q p pair probability).world.accounts t a q.output owned new
    subst a
    refine ⟨⟨q.output,some p.rom,pair.1.state,.birth (paidParents supply w q p pair probability).events.length,.birth (paidParents supply w q p pair probability).events.length,(paidParents supply w q p pair probability).accounts.cursor p.outputKey,[(.version w.events.length,p.left.receipts.length+1),(.version (w.events.length+1),p.right.receipts.length+1)],[]⟩,?_,?_,?_⟩
    · simp [settle,put] <;> rfl
    · rfl
    · exact bound
  · have before : w.accounts.custody t=.local a := by
      simpa [settle,paidParents,advance,transact,transferred] using owned
    have al : a≠q.left := by intro h; subst a; exact transferred (.inl before)
    have ar : a≠q.right := by intro h; subst a; exact transferred (.inr before)
    by_cases out : a=q.output
    · subst a
      refine ⟨⟨q.output,some p.rom,pair.1.state,.birth (paidParents supply w q p pair probability).events.length,.birth (paidParents supply w q p pair probability).events.length,(paidParents supply w q p pair probability).accounts.cursor p.outputKey,[(.version w.events.length,p.left.receipts.length+1),(.version (w.events.length+1),p.right.receipts.length+1)],[]⟩,?_,?_,?_⟩
      · simp [settle,put] <;> rfl
      · rfl
      · exact bound
    · obtain ⟨resident,read,name,limit⟩ := old t a before
      refine ⟨resident,?_,name,limit⟩
      simpa [settle,paidParents,advance,put,al,ar,out] using read

theorem source_retirement_housed (w : World) (old : Housed w) : Housed (sourceRetire w) := by
  intro t a owned
  by_cases cut : w.accounts.custody t=.local 0
  · simp [sourceRetire,cut] at owned
  · have before : w.accounts.custody t=.local a := by simpa [sourceRetire,cut] using owned
    have different : a≠0 := by intro eq; subst a; exact cut before
    obtain ⟨r,read,name,bound⟩ := old t a before
    exact ⟨r,by simpa [sourceRetire,put,different] using read,name,bound⟩

theorem withdrawal_housed (w : World) (old : Housed w) : Housed (withdraw w) := by
  have retired := source_retirement_housed w old
  intro t a owned
  by_cases cut : (sourceRetire w).accounts.custody t=.external
  · simp [withdraw,cut] at owned
  · apply retired t a
    simpa [withdraw,cut] using owned

theorem fresh_address_bound (w : World) (a : Nat) (h : freshAddress w a=true) :
    a<w.inventory := by
  simp only [freshAddress,Bool.and_eq_true,decide_eq_true_eq] at h
  exact h.1.1.1

theorem boot_housed (w v : World) (a : Nat) (key : Token) (rom : ROM)
    (h : boot w a key rom=some v) (old : Housed w) : Housed v := by
  unfold boot at h
  split at h
  · rename_i gate
    simp only [Bool.and_eq_true,decide_eq_true_eq] at gate
    have bound := fresh_address_bound w a gate.1.1.2
    cases Option.some.inj h
    intro t b owned
    by_cases same : b=a
    · subst b
      refine ⟨⟨a,some rom,⟨false,false,false,false,false⟩,.birth w.events.length,.birth w.events.length,w.accounts.cursor key,[],[]⟩,?_,?_,?_⟩
      · simp [put] <;> rfl
      · rfl
      · exact bound
    · have before : w.accounts.custody t=.local b := by
        by_cases selected : t=key
        · simp [put,selected] at owned
          exact False.elim (same owned.symm)
        · simpa [put,selected] using owned
      obtain ⟨r,read,name,limit⟩ := old t b before
      exact ⟨r,by simpa [put,same] using read,name,limit⟩
  · contradiction

theorem activation_housed (w v : World) (a : Nat) (h : activate w a=some v)
    (old : Housed w) : Housed v := by
  cases hs : w.slots a with
  | none => simp [activate,hs] at h
  | some slot =>
    simp only [activate,hs,Bind.bind,Option.bind] at h
    split at h
    · rename_i gate
      simp only [Bool.and_eq_true,decide_eq_true_eq] at gate
      have bound := gate.1.1.1.1
      cases Option.some.inj h
      intro t b owned
      by_cases same : b=a
      · subst b
        refine ⟨⟨a,some slot.capture.program,slot.capture.current,.birth w.events.length,.birth w.events.length,w.accounts.cursor slot.key,[(slot.capture.sourceVersion,slot.capture.count)],[]⟩,?_,?_,?_⟩
        · simp [put] <;> rfl
        · rfl
        · exact bound
      · have before : w.accounts.custody t=.local b := by
          by_cases selected : t=slot.key
          · simp [put,selected] at owned
            exact False.elim (same owned.symm)
          · simpa [put,selected] using owned
        obtain ⟨r,read,name,limit⟩ := old t b before
        exact ⟨r,by simpa [put,same] using read,name,limit⟩
    · contradiction

theorem snapshot_housed (w v : World) (source left right : Nat)
    (h : writeSnapshot w source left right=some v) (old : Housed w) : Housed v := by
  cases hc : readCapture w source with
  | none => simp [writeSnapshot,hc] at h
  | some capture =>
    simp only [writeSnapshot,hc,Bind.bind,Option.bind] at h
    split at h
    · cases Option.some.inj h
      intro t a owned
      apply old t a
      by_cases one : t=1
      · by_cases two : t=2 <;> simp [put,one,two] at owned
      · by_cases two : t=2
        · simp [put,two] at owned
        · simpa [put,one,two] using owned
    · contradiction

theorem every_token_enumerated : ∀ t : Token, t∈tokens := by decide +kernel

theorem partition_housed (w v : World) (parent left right : Nat) (xs ys : List Token)
    (h : partition w parent left right xs ys=some v) (old : Housed w) : Housed v := by
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
          have lb := fresh_address_bound w left gate.1.1.1
          have rb := fresh_address_bound w right gate.1.1.2
          have distinct := gate.1.2
          have cover := gate.2.2.2.1
          cases Option.some.inj h
          intro t a owned
          by_cases al : a=left
          · subst a
            refine ⟨⟨left,some rom,r.current,.birth w.events.length,.birth w.events.length,w.accounts.cursor x,[(r.version,r.receipts.length)],[]⟩,?_,?_,?_⟩
            · simp [put,distinct] <;> rfl
            · rfl
            · exact lb
          · by_cases ar : a=right
            · subst a
              refine ⟨⟨right,some rom,r.current,.birth (w.events.length+1),.birth (w.events.length+1),w.accounts.cursor y,[(r.version,r.receipts.length)],[]⟩,?_,?_,?_⟩
              · simp [put] <;> rfl
              · rfl
              · exact rb
            · have tx : t∉xs := by
                intro member
                simp [member] at owned
                exact al owned.symm
              have ty : t∉ys := by
                intro member
                simp [tx,member] at owned
                exact ar owned.symm
              have before : w.accounts.custody t=.local a := by simpa [tx,ty] using owned
              have ap : a≠parent := by
                intro eq
                subst a
                have keyMember : t∈keys w.accounts parent := by
                  simp [keys,every_token_enumerated t,before]
                rcases (cover t (every_token_enumerated t)).mpr keyMember with yes | yes
                · exact tx yes
                · exact ty yes
              obtain ⟨resident,read,name,limit⟩ := old t a before
              exact ⟨resident,by simpa [put,al,ar,ap] using read,name,limit⟩
        · contradiction

theorem step_housed (supply : Supply) (w v : World) (h : Step supply w v) (old : Housed w) :
    Housed v := by
  cases h with
  | native member =>
    rename_i a action weight
    cases ha : access w a with
    | none => simp [nativeRows,ha] at member
    | some data =>
      rcases data with ⟨r,rom,key⟩
      have binding := binding_facts w a r rom key (access_facts _ _ _ _ _ ha).1
      simp only [nativeRows,ha] at member
      obtain ⟨edge,_,eq⟩ := List.mem_map.mp member
      cases eq
      exact advance_housed _ _ _ _ _ _ _ _ _ old binding.2.2.2.1 binding.2.2.2.2
  | snapshot h => exact snapshot_housed _ _ _ _ _ h old
  | activation h => exact activation_housed _ _ _ h old
  | partition h => exact partition_housed _ _ _ _ _ _ _ h old
  | boot h => exact boot_housed _ _ _ _ _ h old
  | fusion member =>
    rename_i outcome probability q
    cases view : parentView w q with
    | none => simp [fusionRows,view] at member
    | some p =>
      by_cases zero : meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction=0
      · rw [empty_same_world supply w q p view zero] at member
        cases List.mem_singleton.mp member
        exact old
      · simp only [fusionRows,view,if_neg zero] at member
        obtain ⟨pair,_,eq⟩ := List.mem_map.mp member
        cases eq
        exact fusion_housed _ _ _ _ view _ _ old
  | retire => exact source_retirement_housed w old
  | withdraw => exact withdrawal_housed w old
  | idle => exact old

theorem all_history_accounts_housed (supply : Supply) (inventory : Nat) (rom : ROM)
    (w : World) (h : History supply inventory rom w) : Housed w := by
  induction h with
  | initial size => exact initial_housed inventory rom size
  | next _ step ih => exact step_housed _ _ _ step ih

end CSTTT.FullNative02
