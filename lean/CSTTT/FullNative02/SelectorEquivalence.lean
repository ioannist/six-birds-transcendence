import CSTTT.FullNative02.EpochNative

namespace CSTTT.FullNative02.SelectorEquivalence
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

/-- A proof-only readout of selector membership, not a replacement ledger. -/
def canonicalKeys (xs : List Token) : List Token := tokens.filter fun t => decide (t∈xs)
def event : Event → Event
  | .partition parent owner rom xs state => .partition parent owner rom (canonicalKeys xs) state
  | e => e
abbrev events (es : List Event) : List Event := es.map event
abbrev world (w : World) : World := {w with events:=events w.events}

theorem canonical_keys_permutation (xs ys : List Token) (h : xs.Perm ys) : canonicalKeys xs=canonicalKeys ys := by
  have predicates : (fun t : Token => decide (t∈xs))=(fun t => decide (t∈ys)) := by
    funext t
    simp only [h.mem_iff]
  simp only [canonicalKeys,predicates]
theorem canonical_keys_mem (t : Token) (xs : List Token) : t∈canonicalKeys xs ↔ t∈xs := by
  simp only [canonicalKeys,List.mem_filter,decide_eq_true_eq]
  exact ⟨fun h => h.2,fun h => ⟨by
    rcases t with ⟨n,bound⟩
    have cases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simp [tokens],h⟩⟩
theorem canonical_keys_idempotent (xs : List Token) : canonicalKeys (canonicalKeys xs)=canonicalKeys xs := by
  change tokens.filter (fun t => decide (t∈canonicalKeys xs))=tokens.filter (fun t => decide (t∈xs))
  simp only [canonical_keys_mem]
theorem least_owned_canonical (xs : List Token) : leastOwned (canonicalKeys xs)=leastOwned xs := by
  simp only [leastOwned,canonical_keys_mem]
theorem events_length (es : List Event) : (events es).length=es.length := by simp [events]
theorem events_take (es : List Event) (n : Nat) : (events es).take n=events (es.take n) := List.map_take.symm

theorem owner_count (es : List Event) (owner : Nat) : Epoch.ownerCount (events es) owner=Epoch.ownerCount es owner := by
  simp only [Epoch.ownerCount,events,List.filter_map,List.length_map]
  congr 2
  funext e
  cases e <;> rfl
theorem token_count (es : List Event) (key : Token) : Epoch.tokenCount (events es) key=Epoch.tokenCount es key := by
  simp only [Epoch.tokenCount,events,List.filter_map,List.length_map]
  congr 2
  funext e
  cases e <;> rfl
theorem node_count (es : List Event) (node : Node) : Epoch.nodeCount (events es) node=Epoch.nodeCount es node := by
  cases node <;> simp only [Epoch.nodeCount]
  case version n =>
    simp only [events,List.getElem?_map]
    cases h : es[n]? with
    | none => rfl
    | some e => cases e <;> simp [event,←List.map_take,owner_count]
theorem birth (es : List Event) (owner ordinal : Nat) : Epoch.birth (events es) owner ordinal=Epoch.birth es owner ordinal := by
  simp only [Epoch.birth,events,List.getElem?_map]
  cases h : es[ordinal]? with
  | none => rfl
  | some e =>
    cases e <;> simp only [Option.map_some,event,Bind.bind,Option.bind]
    all_goals try rfl
    case activation snapshot a rom key cursor state =>
      cases snapshot <;> simp only [Bind.bind,Option.bind]
      case event n =>
        cases hs : es[n]? with
        | none => simp only [hs,Option.map_none]
        | some e => simp only [hs,Option.map_some]; cases e <;> rfl
    case partition parent a rom xs state =>
      rw [least_owned_canonical,node_count]
    case fusion left right a rom xs ys l r p => rw [node_count,node_count]

theorem token_charge (es : List Event) (key : Token) : Epoch.tokenCharge (events es) key=Epoch.tokenCharge es key := by
  simp only [Epoch.tokenCharge,events,List.foldl_map]
  congr 1
  funext charge e
  cases e <;> rfl
theorem step (owner : Nat) (b : Epoch.Birth) (a : Epoch.Audit) (entry : Event × Nat) :
    Epoch.step owner b a (event entry.1,entry.2)=Epoch.step owner b a entry := by
  rcases entry with ⟨e,n⟩
  cases e <;> rfl
theorem replay (owner ordinal cursor : Nat) (b : Epoch.Birth) (es : List Event) :
    Epoch.replay owner ordinal cursor b (events es)=Epoch.replay owner ordinal cursor b es := by
  simp only [Epoch.replay,events, List.zipIdx_map,←List.map_drop,List.foldl_map]
  have steps : (fun a entry => Epoch.step owner b a ((Prod.map event id) entry))=Epoch.step owner b := by
    funext a entry
    exact step owner b a entry
  rw [steps]
  simp only [←List.map_take,token_charge]

theorem authentic (w : World) (owner : Nat) (r : Resident) :
    authenticVersion (world w) owner r=authenticVersion w owner r := by
  cases node : r.version <;> simp only [authenticVersion,node,world,events,List.getElem?_map]
  all_goals try rfl
  all_goals rename_i n
  all_goals cases h : w.events[n]? with
  | none => simp only [h,Option.map_none]
  | some e => simp only [h,Option.map_some]; cases e <;> rfl

theorem binding (w : World) (owner : Nat) :
    FullNative02.binding (world w) owner=FullNative02.binding w owner := by
  simp only [FullNative02.binding,authentic]
theorem access (w : World) (owner : Nat) : FullNative02.access (world w) owner=FullNative02.access w owner := by
  simp only [FullNative02.access,binding]
theorem valid (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token) :
    Epoch.valid (world w) owner r rom key=Epoch.valid w owner r rom key := by
  cases node : r.birth <;> simp only [Epoch.valid,node]
  all_goals try rfl
  case birth n =>
    simp only [world,events_take,birth,authentic,events_length,token_count,replay]
theorem admission (w : World) (owner : Nat) : Epoch.accept (world w) owner=Epoch.accept w owner := by
  simp only [Epoch.accept,access]
  cases enabled : FullNative02.access w owner with
  | none => rfl
  | some data => rcases data with ⟨r,rom,key⟩; simp only [valid]

end CSTTT.FullNative02.SelectorEquivalence
