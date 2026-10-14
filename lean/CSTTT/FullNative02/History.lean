import CSTTT.FullNative02.NativeLaws
import CSTTT.FullNative02.OriginalReturn

namespace CSTTT.FullNative02
set_option autoImplicit false
set_option maxHeartbeats 16000000

def Ordered (w : World) : Prop :=
  ∀ x y, (x,y)∈ledgerEdges w → nodeRank x<nodeRank y

theorem authenticated_version_bound (w : World) (a : Nat) (r : Resident)
    (h : authenticVersion w a r=true) : nodeRank r.version<4*w.events.length := by
  cases hv : r.version <;> simp only [authenticVersion,hv] at h
  all_goals try contradiction
  all_goals rename_i n
  all_goals
    have hn : n<w.events.length := by
      by_cases good : n<w.events.length
      · exact good
      have bad : w.events.length≤n := by omega
      have none : w.events[n]?=none := List.getElem?_eq_none (by omega)
      rw [none] at h
      simp at h
    simp only [hv,nodeRank]
    omega

theorem binding_authenticated (w : World) (a : Nat) (r : Resident) (rom : ROM) (key : Token)
    (h : binding w a=some (r,rom,key)) : authenticVersion w a r=true := by
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
          simp only [Bool.and_eq_true] at hg
          exact hg.2
        · simp only [binding,hr,hd,hk,Bind.bind,Option.bind,if_neg hg] at h
          contradiction

theorem ordered_append (w v : World) (suffix : List Event)
    (events : v.events=w.events++suffix) (old : Ordered w)
    (new : ∀ x y, (x,y)∈ledgerEdgesFrom w.events.length suffix → nodeRank x<nodeRank y) :
    Ordered v := by
  intro x y edge
  simp only [ledgerEdges,events,ledger_append,Nat.zero_add] at edge
  rcases List.mem_append.mp edge with prior | added
  · exact old x y prior
  · exact new x y added

theorem advance_ordered (supply : Supply) (w : World) (a : Nat) (r : Resident)
    (rom : ROM) (key : Token) (action : Bool) (edge : FullNative.State × Nat)
    (conditional : Option Rat) (old : Ordered w)
    (bound : nodeRank r.version<4*w.events.length) :
    Ordered (advance supply w a r rom key action edge conditional) := by
  apply ordered_append w _ [.native r.version (makeReceipt supply w a r rom key action edge) conditional] rfl old
  intro x y member
  simp only [ledgerEdgesFrom,eventEdges,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp only [nodeRank] at * <;> omega

theorem native_ordered (supply : Supply) (w v : World) (a : Nat) (action : Bool)
    (weight : Nat) (member : (v,weight)∈nativeRows supply w a action) (old : Ordered w) :
    Ordered v := by
  cases ha : access w a with
  | none => simp [nativeRows,ha] at member
  | some data =>
    rcases data with ⟨r,rom,key⟩
    simp only [nativeRows,ha] at member
    obtain ⟨edge,_,eq⟩ := List.mem_map.mp member
    cases eq
    exact advance_ordered supply w a r rom key action edge none old
      (authenticated_version_bound w a r (binding_authenticated w a r rom key
        (access_facts w a r rom key ha).1))

theorem fusion_ordered (supply : Supply) (w : World) (q : FusionRequest) (p : Parents)
    (view : parentView w q=some p) (pair : Pair) (probability : Rat) (old : Ordered w) :
    Ordered (settle supply w q p pair probability).world := by
  have facts := fusion_guard_facts w q p view
  have left := authenticated_version_bound w q.left p.left
    (binding_authenticated w q.left p.left p.rom p.leftKey (access_facts _ _ _ _ _ facts.1).1)
  have right := authenticated_version_bound w q.right p.right
    (binding_authenticated w q.right p.right p.rom p.rightKey (access_facts _ _ _ _ _ facts.2.1).1)
  let first := advance supply w q.left p.left p.rom p.leftKey q.leftAction
    (pair.1.state,pair.1.weight) (some probability)
  let suffix := [Event.native p.left.version
    (makeReceipt supply w q.left p.left p.rom p.leftKey q.leftAction (pair.1.state,pair.1.weight))
    (some probability),Event.native p.right.version
    (makeReceipt supply first q.right p.right p.rom p.rightKey q.rightAction (pair.2.state,pair.2.weight))
    (some probability),Event.fusion (.version w.events.length) (.version (w.events.length+1))
    q.output p.rom (keys w.accounts q.left) (keys w.accounts q.right)
    (makeReceipt supply w q.left p.left p.rom p.leftKey q.leftAction (pair.1.state,pair.1.weight))
    (makeReceipt supply first q.right p.right p.rom p.rightKey q.rightAction (pair.2.state,pair.2.weight)) probability]
  refine ordered_append w _ suffix ?_ old ?_
  · simp [suffix,first,settle,paidParents,advance,List.append_assoc,Nat.add_assoc]
  · intro x y member
    simp only [suffix,
      ledgerEdgesFrom,eventEdges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      Prod.mk.injEq,or_assoc] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp only [nodeRank] at * <;> omega

def Footprint (w v : World) : Prop :=
  v.inventory=w.inventory ∧ (∀ a, v.fresh a=true → w.fresh a=true) ∧
    ∃ suffix, v.events=w.events++suffix

theorem footprint_refl (w : World) : Footprint w w := ⟨rfl,(fun _ h => h),[],by simp⟩

theorem footprint_trans (u w v : World) (first : Footprint u w) (next : Footprint w v) :
    Footprint u v := by
  obtain ⟨fi,ff,fs,fe⟩ := first
  obtain ⟨ni,nf,ns,ne⟩ := next
  exact ⟨ni.trans fi,(fun a h => ff a (nf a h)),fs++ns,by rw [ne,fe,List.append_assoc]⟩

theorem footprint_ancestry (w v : World) (h : Footprint w v) (x y : Node)
    (path : ancestry w x y) : ancestry v x y := by
  obtain ⟨_,_,suffix,events⟩ := h
  apply path_mono (es := ledgerEdges w) (x := x) (y := y) ?_ path
  intro e he
  simp only [ledgerEdges,events,ledger_append,Nat.zero_add]
  exact List.mem_append_left _ he

theorem advance_footprint (supply : Supply) (w : World) (a : Nat) (r : Resident)
    (rom : ROM) (key : Token) (action : Bool) (edge : FullNative.State × Nat)
    (conditional : Option Rat) : Footprint w (advance supply w a r rom key action edge conditional) :=
  ⟨rfl,(fun _ h => h),_,rfl⟩

theorem boot_history (w v : World) (a : Nat) (key : Token) (rom : ROM)
    (h : boot w a key rom=some v) (old : Ordered w) : Footprint w v ∧ Ordered v := by
  unfold boot at h
  split at h
  · cases Option.some.inj h
    constructor
    · refine ⟨rfl,?_,_,rfl⟩
      intro b hb
      by_cases same : b=a
      · simp [put,same] at hb
      · simpa [put,same] using hb
    · apply ordered_append w _ _ rfl old
      intro x y edge
      simp only [ledgerEdgesFrom,eventEdges,List.mem_append,List.mem_cons,List.not_mem_nil,
        or_false,Prod.mk.injEq] at edge
      obtain ⟨rfl,rfl⟩ := edge
      simp [nodeRank]
  · contradiction

theorem slot_event_bound (w : World) (slot : Slot) (h : authenticSlot w slot=true) :
    nodeRank slot.capture.event<4*w.events.length := by
  cases he : slot.capture.event <;> simp only [authenticSlot,he] at h
  all_goals try contradiction
  rename_i n
  have hn : n<w.events.length := by
    by_cases good : n<w.events.length
    · exact good
    have bad : w.events.length≤n := by omega
    have none : w.events[n]?=none := List.getElem?_eq_none (by omega)
    rw [none] at h
    simp at h
  simp only [he,nodeRank]
  omega

theorem activation_history (w v : World) (a : Nat) (h : activate w a=some v)
    (old : Ordered w) : Footprint w v ∧ Ordered v := by
  cases hs : w.slots a with
  | none => simp [activate,hs] at h
  | some slot =>
    simp only [activate,hs,Bind.bind,Option.bind] at h
    split at h
    · rename_i gate
      have auth : authenticSlot w slot=true := by
        simp only [Bool.and_eq_true,decide_eq_true_eq] at gate
        exact gate.2
      have bound := slot_event_bound w slot auth
      cases Option.some.inj h
      constructor
      · refine ⟨rfl,?_,_,rfl⟩
        intro b hb
        by_cases same : b=a
        · simp [put,same] at hb
        · simpa [put,same] using hb
      · apply ordered_append w _ _ rfl old
        intro x y edge
        simp only [ledgerEdgesFrom,eventEdges,List.mem_append,List.mem_cons,List.not_mem_nil,
          or_false,Prod.mk.injEq] at edge
        obtain ⟨rfl,rfl⟩ := edge
        simp only [nodeRank] at *
        omega
    · contradiction

theorem capture_version_bound (w : World) (a : Nat) (capture : Capture)
    (h : readCapture w a=some capture) : nodeRank capture.sourceVersion<4*w.events.length := by
  cases ha : access w a with
  | none => simp [readCapture,ha] at h
  | some data =>
    rcases data with ⟨r,rom,key⟩
    have bound := authenticated_version_bound w a r
      (binding_authenticated w a r rom key (access_facts _ _ _ _ _ ha).1)
    simp only [readCapture,ha,Bind.bind,Option.bind] at h
    split at h <;> try simp [Bind.bind,Option.bind] at h
    split at h <;> try simp [Bind.bind,Option.bind] at h
    split at h <;> try simp [Bind.bind,Option.bind] at h
    split at h <;> try simp [Bind.bind,Option.bind] at h
    cases h.2
    exact bound

theorem snapshot_history (w v : World) (source left right : Nat)
    (h : writeSnapshot w source left right=some v) (old : Ordered w) :
    Footprint w v ∧ Ordered v := by
  cases hc : readCapture w source with
  | none => simp [writeSnapshot,hc] at h
  | some capture =>
    have bound := capture_version_bound w source capture hc
    simp only [writeSnapshot,hc,Bind.bind,Option.bind] at h
    split at h
    · cases Option.some.inj h
      constructor
      · exact ⟨rfl,(fun _ h => h),_,rfl⟩
      · apply ordered_append w _ _ rfl old
        intro x y edge
        simp only [ledgerEdgesFrom,eventEdges,List.mem_append,List.mem_cons,List.not_mem_nil,
          or_false,Prod.mk.injEq] at edge
        obtain ⟨rfl,rfl⟩ := edge
        simp only [nodeRank] at *
        omega
    · contradiction

theorem partition_history (w v : World) (parent left right : Nat) (xs ys : List Token)
    (h : partition w parent left right xs ys=some v) (old : Ordered w) :
    Footprint w v ∧ Ordered v ∧
      ∃ r rom key, binding w parent=some (r,rom,key) ∧
        ancestry v r.version (.birth w.events.length) ∧
        ancestry v r.version (.birth (w.events.length+1)) ∧ v.residents parent=none := by
  cases hb : binding w parent with
  | none => simp [partition,hb] at h
  | some data =>
    rcases data with ⟨r,rom,key⟩
    have bound := authenticated_version_bound w parent r (binding_authenticated _ _ _ _ _ hb)
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
          have vacantLeft := fresh_is_unoccupied w left gate.1.1.1
          have vacantRight := fresh_is_unoccupied w right gate.1.1.2
          have read := (binding_facts w parent r rom key hb).1
          have pl : parent≠left := by intro eq; rw [eq,vacantLeft] at read; cases read
          have pr : parent≠right := by intro eq; rw [eq,vacantRight] at read; cases read
          cases Option.some.inj h
          constructor
          · refine ⟨rfl,?_,_,rfl⟩
            intro a ha
            by_cases al : a=left
            · simp [put,al] at ha
            · by_cases ar : a=right
              · simp [put,ar] at ha
              · simpa [put,al,ar] using ha
          constructor
          · apply ordered_append w _ _ rfl old
            intro a b edge
            simp only [ledgerEdgesFrom,eventEdges,List.mem_append,List.mem_cons,List.not_mem_nil,
              or_false,Prod.mk.injEq] at edge
            rcases edge with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp only [nodeRank] at * <;> omega
          · refine ⟨r,rom,key,rfl,Path.one ?_,Path.one ?_,?_⟩
            · simp [ledgerEdges,ledger_append,ledgerEdgesFrom,eventEdges]
            · simp [ledgerEdges,ledger_append,ledgerEdgesFrom,eventEdges]
            · simp [put,pl,pr]
        · contradiction

theorem settle_footprint (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (pair : Pair) (probability : Rat) :
    Footprint w (settle supply w q p pair probability).world := by
  refine ⟨rfl,?_,?_⟩
  · intro a h
    by_cases same : a=q.output
    · simp [settle,put,same] at h
    · simpa [settle,put,paidParents,advance,same] using h
  · simp only [settle,paidParents,advance,List.length_append,List.length_singleton,
      List.append_assoc]
    exact ⟨_,rfl⟩

/-- Supported interpreter histories. Request parameters are unrestricted;
successful worlds and probabilities must be members of the computed support.
Idle includes unavailable and empty attempts, whose world is unchanged. -/
inductive Step (supply : Supply) : World → World → Prop where
  | native {w v a action weight} : (v,weight)∈nativeRows supply w a action → Step supply w v
  | snapshot {w v source left right} : writeSnapshot w source left right=some v → Step supply w v
  | activation {w v address} : activate w address=some v → Step supply w v
  | partition {w v parent left right xs ys} : partition w parent left right xs ys=some v → Step supply w v
  | boot {w v address key rom} : boot w address key rom=some v → Step supply w v
  | fusion {w outcome probability q} : (outcome,probability)∈fusionRows supply w q → Step supply w outcome.world
  | retire (w) : Step supply w (sourceRetire w)
  | withdraw (w) : Step supply w (withdraw w)
  | idle (w) : Step supply w w

theorem step_invariants (supply : Supply) (w v : World) (step : Step supply w v)
    (old : Ordered w) : Footprint w v ∧ Ordered v := by
  cases step with
  | native member =>
    rename_i a action weight
    cases ha : access w a with
    | none => simp [nativeRows,ha] at member
    | some data =>
      rcases data with ⟨r,rom,key⟩
      have ordered := native_ordered supply w v a action weight member old
      simp only [nativeRows,ha] at member
      obtain ⟨edge,_,eq⟩ := List.mem_map.mp member
      cases eq
      exact ⟨advance_footprint supply w a r rom key action edge none,ordered⟩
  | snapshot h => exact snapshot_history _ _ _ _ _ h old
  | activation h => exact activation_history _ _ _ h old
  | partition h =>
    have result := partition_history _ _ _ _ _ _ _ h old
    exact ⟨result.1,result.2.1⟩
  | boot h => exact boot_history _ _ _ _ _ h old
  | fusion member =>
    rename_i outcome probability q
    cases view : parentView w q with
    | none => simp [fusionRows,view] at member
    | some p =>
      by_cases zero : meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction=0
      · rw [empty_same_world supply w q p view zero] at member
        cases List.mem_singleton.mp member
        exact ⟨footprint_refl w,old⟩
      · simp only [fusionRows,view,if_neg zero] at member
        obtain ⟨pair,_,eq⟩ := List.mem_map.mp member
        cases eq
        exact ⟨settle_footprint _ _ _ _ _ _,fusion_ordered _ _ _ _ view _ _ old⟩
  | retire => exact ⟨⟨rfl,(fun _ h => h),[],by simp [sourceRetire]⟩,old⟩
  | withdraw => exact ⟨⟨rfl,(fun _ h => h),[],by simp [withdraw,sourceRetire]⟩,old⟩
  | idle => exact ⟨footprint_refl w,old⟩

inductive History (supply : Supply) (inventory : Nat) (rom : ROM) : World → Prop where
  | initial : 4≤inventory → History supply inventory rom (initial inventory rom)
  | next {w v} : History supply inventory rom w → Step supply w v → History supply inventory rom v

theorem initial_ordered (inventory : Nat) (rom : ROM) : Ordered (initial inventory rom) := by
  intro x y member
  simp only [ledgerEdges,initial,ledgerEdgesFrom,eventEdges,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,Prod.mk.injEq] at member
  obtain ⟨rfl,rfl⟩ := member
  decide

/-- General protocol-history invariants, not only finite script checks. -/
theorem history_invariants (supply : Supply) (inventory : Nat) (rom : ROM) (w : World)
    (h : History supply inventory rom w) :
    Footprint (initial inventory rom) w ∧ Ordered w := by
  induction h with
  | initial _ => exact ⟨footprint_refl _,initial_ordered _ _⟩
  | next _ step ih =>
    have current := step_invariants supply _ _ step ih.2
    exact ⟨footprint_trans _ _ _ ih.1 current.1,current.2⟩

theorem history_ancestry_acyclic (supply : Supply) (inventory : Nat) (rom : ROM)
    (w : World) (history : History supply inventory rom w) (x y : Node)
    (path : ancestry w x y) : nodeRank x<nodeRank y :=
  ordered_ledger_acyclic w (history_invariants _ _ _ _ history).2 x y path

theorem history_inventory_and_capabilities (supply : Supply) (inventory : Nat) (rom : ROM)
    (w : World) (h : History supply inventory rom w) :
    w.inventory=inventory ∧ ∀ a, w.fresh a=true → a<inventory ∧ a≠0 := by
  have footprint := (history_invariants _ _ _ _ h).1
  refine ⟨footprint.1,?_⟩
  intro a fresh
  have original := footprint.2.1 a fresh
  simpa [initial] using original

theorem consumed_capability_never_returns (supply : Supply) (w v : World)
    (step : Step supply w v) (ordered : Ordered w) (a : Nat) (spent : w.fresh a=false) :
    v.fresh a=false := by
  have mono := (step_invariants _ _ _ step ordered).1.2.1
  cases hv : v.fresh a with
  | false => rfl
  | true => have impossible := mono a hv; rw [spent] at impossible; cases impossible

end CSTTT.FullNative02
