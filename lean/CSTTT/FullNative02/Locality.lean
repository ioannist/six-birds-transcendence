import CSTTT.FullNative02.NativeAccounts

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000

theorem authentic_append_events (w : World) (owner : Nat) (r : Resident) (tail : List Event)
    (h : authenticVersion w owner r=true) :
    authenticVersion {w with events := w.events++tail} owner r=true := by
  have bound := authenticated_version_bound w owner r h
  cases node : r.version <;> simp only [authenticVersion,node] at h ⊢
  all_goals try contradiction
  all_goals rename_i n
  all_goals
    have index : n<w.events.length := by simp only [node,nodeRank] at bound; omega
    simpa only [List.getElem?_append_left index] using h

theorem different_owned_keys (w : World) (owner other : Nat) (r s : Resident)
    (rom otherROM : ROM) (key k : Token)
    (own : access w owner=some (r,rom,key)) (foreign : access w other=some (s,otherROM,k))
    (different : owner≠other) : key≠k := by
  intro same
  subst k
  exact different (custody_exclusive w.accounts key owner other
    (actual_issuer renewable w owner r rom key own false (r.current,1))
    (actual_issuer renewable w other s otherROM key foreign false (s.current,1)))

theorem foreign_access_after (w : World) (owner other : Nat) (r s : Resident)
    (rom otherROM : ROM) (key k : Token)
    (own : access w owner=some (r,rom,key)) (foreign : access w other=some (s,otherROM,k))
    (different : owner≠other) (action : Bool) (edge : State × Nat) :
    access (advance renewable w other s otherROM k action edge) owner=some (r,rom,key) := by
  have keysDifferent := different_owned_keys w owner other r s rom otherROM key k own foreign different
  have facts := binding_facts w owner r rom key (access_facts _ _ _ _ _ own).1
  have head := binding_primary w owner r rom key (access_facts _ _ _ _ _ own).1
  have authenticated := authentic_append_events w owner r
    [.native s.version (makeReceipt renewable w other s otherROM k action edge) none]
    (binding_authenticated _ _ _ _ _ (access_facts _ _ _ _ _ own).1)
  have charge : (advance renewable w other s otherROM k action edge).accounts.charge key=true := by
    simpa [advance,transact,put,keysDifferent] using (access_facts _ _ _ _ _ own).2
  have read : (advance renewable w other s otherROM k action edge).residents owner=some r := by
    simp [advance,put,different,facts.1]
  have primary : (keys (advance renewable w other s otherROM k action edge).accounts owner).head?=some key := head
  simp only [access,binding,read,facts.2.1,primary,Bind.bind,Option.bind]
  have bound : owner<(advance renewable w other s otherROM k action edge).inventory ∧ r.owner=owner :=
    ⟨facts.2.2.2.2,facts.2.2.2.1⟩
  have auth : authenticVersion (advance renewable w other s otherROM k action edge) owner r=true := authenticated
  simp [bound,auth,charge]

theorem foreign_epoch_valid (w : World) (owner other : Nat) (r s : Resident)
    (rom otherROM : ROM) (key k : Token)
    (own : access w owner=some (r,rom,key)) (foreign : access w other=some (s,otherROM,k))
    (different : owner≠other) (audited : Epoch.valid w owner r rom key=true)
    (action : Bool) (edge : State × Nat) :
    Epoch.valid (advance renewable w other s otherROM k action edge) owner r rom key=true := by
  have keysDifferent := different_owned_keys w owner other r s rom otherROM key k own foreign different
  cases node : r.birth <;> simp only [Epoch.valid,node] at audited ⊢
  case birth ordinal =>
    cases decoded : Epoch.birth (w.events.take (ordinal+1)) owner ordinal with
    | none => simp [decoded] at audited
    | some b =>
      have parts := audited
      simp only [decoded,Bool.and_eq_true,decide_eq_true_eq] at parts
      have bound : ordinal<w.events.length := parts.2.1
      have cut : (w.events++[Event.native s.version
          (makeReceipt renewable w other s otherROM k action edge) none]).take (ordinal+1)=
          w.events.take (ordinal+1) := List.take_append_of_le_length (by omega)
      have past : (w.events++[Event.native s.version
          (makeReceipt renewable w other s otherROM k action edge) none]).take ordinal=
          w.events.take ordinal := List.take_append_of_le_length (by omega)
      simp only [advance,cut,decoded,past]
      rw [Epoch.replay_append owner ordinal _ b w.events _ (by omega)]
      simp only [List.zipIdx_cons,List.zipIdx_nil,List.foldl_cons,List.foldl_nil]
      have otherOwner : (makeReceipt renewable w other s otherROM k action edge).owner≠owner := Ne.symm different
      simp only [Epoch.step,if_neg otherOwner]
      simp only [transact,put,if_neg keysDifferent]
      simp only [Epoch.valid,node,decoded] at audited
      simpa only [List.length_append,List.length_singleton,Bool.and_eq_true,decide_eq_true_eq] using
        (show (Epoch.replay owner ordinal (Epoch.tokenCount (w.events.take ordinal) key) b w.events).valid=true ∧
          ordinal<w.events.length+1 ∧ b.rom=rom ∧ b.key=key ∧
          r.birthCursor=Epoch.tokenCount (w.events.take ordinal) key ∧ r.roots=b.roots ∧
          r.current=(Epoch.replay owner ordinal (Epoch.tokenCount (w.events.take ordinal) key) b w.events).state ∧
          r.version=(Epoch.replay owner ordinal (Epoch.tokenCount (w.events.take ordinal) key) b w.events).version ∧
          r.receipts=(Epoch.replay owner ordinal (Epoch.tokenCount (w.events.take ordinal) key) b w.events).records ∧
          w.accounts.cursor key=(Epoch.replay owner ordinal (Epoch.tokenCount (w.events.take ordinal) key) b w.events).cursor ∧
          w.accounts.charge key=(Epoch.replay owner ordinal (Epoch.tokenCount (w.events.take ordinal) key) b w.events).charge ∧
          (b.recordedCursor=none ∨ b.recordedCursor=some (Epoch.tokenCount (w.events.take ordinal) key)) from
            ⟨parts.1,by omega,parts.2.2⟩)
  all_goals contradiction

theorem foreign_native_preserves_acceptance (w v : World) (owner other : Nat)
    (accepted : Epoch.accept w owner=true) (different : owner≠other) (action : Bool)
    (n : Nat) (support : (v,n)∈nativeRows renewable w other action) : Epoch.accept v owner=true := by
  obtain ⟨r,key,own,inside,audited,block⟩ := Epoch.accepted_access w owner accepted
  cases foreign : access w other with
  | none => simp [nativeRows,foreign] at support
  | some data =>
    rcases data with ⟨s,rom,k⟩
    rw [native_rows_from_access _ _ _ _ _ _ foreign action] at support
    obtain ⟨e,_,eq⟩ := List.mem_map.mp support
    have world : v=advance renewable w other s rom k action e := (congrArg Prod.fst eq).symm
    rw [world]
    have enabled := foreign_access_after _ _ _ _ _ _ _ _ _ own foreign different action e
    have audit := foreign_epoch_valid _ _ _ _ _ _ _ _ _ own foreign different audited action e
    simp only [Epoch.accept,enabled]
    simp [inside,audit,block]

theorem transactions_commute (supply : Supply) (a : Accounts) (key k : Token) (different : key≠k) :
    transact supply (transact supply a key) k=transact supply (transact supply a k) key := by
  cases a with
  | mk custody charge cursor =>
    simp only [transact,Accounts.mk.injEq]
    refine ⟨True.intro,?_,?_⟩
    · funext t
      by_cases left : t=key <;> by_cases right : t=k <;>
        simp_all [put]
    · funext t
      by_cases left : t=key <;> by_cases right : t=k <;>
        simp_all [put]

end CSTTT.FullNative02
