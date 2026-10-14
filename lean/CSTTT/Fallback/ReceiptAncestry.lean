import CSTTT.Fallback.CachedSeed
import CSTTT.Fallback.NativeDescendant

namespace CSTTT.FallbackTheory.ReceiptAncestry
open CSTTT.TransportTheory
open CSTTT.FallbackTheory.OperationalTrace
open CSTTT.FallbackTheory.SharedOperationalSeed
open CSTTT.FallbackTheory.NativeDescendant
open CSTTT.FallbackTheory.FiniteClosure
open CSTTT.FallbackTheory.FiniteHorn
variable {H S T E R SC TC RR M : Type} [DecidableEq S]
-- Class (b): receipts store actual intermediate computations; no receipt is a raw campaign input.
structure Receipt (S T : Type) where
  before : Store S T
  command : NativeDescendant.Command T
  after : Store S T
-- Class (b): actual successful primitive execution alone produces a receipt.
def recordedRun (b : RawBridge H S T E R SC TC RR M) :
    Store S T → List (NativeDescendant.Command T) → Option (Store S T × List (Receipt S T))
  | store,[] => some (store,[])
  | store,command::rest => do
      let next ← NativeDescendant.step b store command
      let (finished,receipts) ← recordedRun b next rest
      some (finished,⟨store,command,next⟩::receipts)
-- Class (b): recorded execution consumes the same computed source-checked prefix, never a supplied store.
def actualRecorded (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) : Option (Store S T × List (Receipt S T)) :=
  (computedStore inputs).bind (fun store => recordedRun b store commands)
-- Class (b): recording preserves every execution outcome on all stores and command lists.
theorem recorded_run_exact (b : RawBridge H S T E R SC TC RR M) (commands : List (NativeDescendant.Command T))
    (store : Store S T) : (recordedRun b store commands).map Prod.fst=NativeDescendant.run b store commands := by
  induction commands generalizing store with
  | nil => rfl
  | cons command rest ih =>
    cases first : NativeDescendant.step b store command with
    | none => simp [recordedRun,NativeDescendant.run,first]
    | some next =>
      cases tail : recordedRun b next rest with
      | none => simpa [recordedRun,NativeDescendant.run,first,tail] using ih next
      | some value =>
        obtain ⟨finished,receipts⟩ := value
        simpa [recordedRun,NativeDescendant.run,first,tail] using ih next
-- Class (b): actual recording preserves the full optional shared-prefix execution.
theorem actual_recorded_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) :
    (actualRecorded b inputs commands).map Prod.fst=extendActual b inputs commands := by
  cases prefixResult : computedStore inputs with
  | none => simp [actualRecorded,extendActual,prefixResult]
  | some store => simpa [actualRecorded,extendActual,prefixResult] using recorded_run_exact b commands store
-- Class (b): failed consumed prefix rejects the entire receipt readout on every partial input.
theorem missing_prefix_receipts (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (missing : computedStore inputs=none) :
    actualRecorded b inputs commands=none := by simp [actualRecorded,missing]
-- Class (b): each returned receipt is a genuine accepted step on its actual before/after stores.
theorem every_receipt_checked (b : RawBridge H S T E R SC TC RR M)
    (commands : List (NativeDescendant.Command T)) (store finished : Store S T) (receipts : List (Receipt S T))
    (executed : recordedRun b store commands=some (finished,receipts)) :
    ∀ receipt∈receipts,NativeDescendant.step b receipt.before receipt.command=some receipt.after := by
  induction commands generalizing store receipts with
  | nil =>
    have equal := Option.some.inj executed
    cases equal
    simp
  | cons command rest ih =>
    cases first : NativeDescendant.step b store command with
    | none => simp [recordedRun,first] at executed
    | some next =>
      cases tail : recordedRun b next rest with
      | none => simp [recordedRun,first,tail] at executed
      | some value =>
        obtain ⟨last,remaining⟩ := value
        have equal : (last,⟨store,command,next⟩::remaining)=(finished,receipts) := by
          simpa [recordedRun,first,tail] using executed
        cases equal
        intro receipt member
        rcases List.mem_cons.mp member with head|member
        · cases head; exact first
        · exact ih next remaining tail receipt member
-- Class (b): the receipt's proposed edge list is computed from its actual primitive command.
def receiptEdges (receipt : Receipt S T) : List (Nat × Nat) :=
  match receipt.command with
  | .advance parent target _ _ => [(parent,target)]
  | .fission parent left right => [(parent,left),(parent,right)]
-- Class (b): one checked receipt returns all guards and its exact actual successor, rather than supplied support.
theorem checked_receipt_shape (b : RawBridge H S T E R SC TC RR M) (receipt : Receipt S T)
    (checked : NativeDescendant.step b receipt.before receipt.command=some receipt.after) :
    (match receipt.command with
    | .advance parent target action outcome => ∃ payload,
        receipt.before.read parent=some (.target payload) ∧ receipt.before.active parent=true ∧
        receipt.before.read target=none ∧ 0<b.targetActionStep payload action outcome ∧
        receipt.after=advanced receipt.before parent target outcome
    | .fission parent left right => ∃ payload,
        receipt.before.read parent=some (.target payload) ∧ receipt.before.active parent=true ∧
        receipt.before.read left=none ∧ receipt.before.read right=none ∧ left≠right ∧
        receipt.after=split receipt.before parent left right payload) := by
  cases command : receipt.command with
  | advance parent target action outcome =>
    rw [command] at checked
    have present : (NativeDescendant.step b receipt.before (.advance parent target action outcome)).isSome := by rw [checked]; rfl
    obtain ⟨payload,read,active,fresh,support⟩ := (advance_present_iff _ _ _ _ _ _).mp present
    exact ⟨payload,read,active,fresh,support,(Option.some.inj (checked.symm.trans
      (advance_exact _ _ _ _ _ payload _ read active fresh support)))⟩
  | fission parent left right =>
    rw [command] at checked
    have present : (NativeDescendant.step b receipt.before (.fission parent left right)).isSome := by rw [checked]; rfl
    obtain ⟨payload,read,active,leftFresh,rightFresh,distinct⟩ := (fission_present_iff _ _ _ _ _).mp present
    exact ⟨payload,read,active,leftFresh,rightFresh,distinct,(Option.some.inj (checked.symm.trans
      (fission_exact _ _ _ _ _ payload read active leftFresh rightFresh distinct)))⟩
-- Class (b): genuine accepted-step receipts retain all prior edges and contain exactly their generated new edges.
theorem checked_receipt_edges (b : RawBridge H S T E R SC TC RR M) (receipt : Receipt S T)
    (checked : NativeDescendant.step b receipt.before receipt.command=some receipt.after) :
    (∀ edge∈receipt.before.edges,edge∈receipt.after.edges) ∧
    (∀ edge∈receiptEdges receipt,edge∈receipt.after.edges) := by
  have shape := checked_receipt_shape b receipt checked
  cases command : receipt.command with
  | advance parent target action outcome =>
    rw [command] at shape
    obtain ⟨_,_,_,_,_,after⟩ := shape
    rw [after]
    constructor
    · intro edge member; simp [advanced,member]
    · intro edge member
      have equal : edge=(parent,target) := by simpa [receiptEdges,command] using member
      subst edge
      simp [advanced]
  | fission parent left right =>
    rw [command] at shape
    obtain ⟨_,_,_,_,_,_,after⟩ := shape
    rw [after]
    constructor
    · intro edge member; simp [split,member]
    · intro edge member
      simp only [receiptEdges,command,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with equal|equal <;> subst edge <;> simp [split]
-- Class (b): every accepted finite execution retains its starting graph and all actual receipt-generated edges.
theorem recorded_edges_retained (b : RawBridge H S T E R SC TC RR M)
    (commands : List (NativeDescendant.Command T)) (store finished : Store S T) (receipts : List (Receipt S T))
    (executed : recordedRun b store commands=some (finished,receipts)) :
    (∀ edge∈store.edges,edge∈finished.edges) ∧
    (∀ receipt∈receipts,∀ edge∈receiptEdges receipt,edge∈finished.edges) := by
  induction commands generalizing store receipts with
  | nil =>
    have equal := Option.some.inj executed
    cases equal
    exact ⟨fun _ member => member,by simp⟩
  | cons command rest ih =>
    cases first : NativeDescendant.step b store command with
    | none => simp [recordedRun,first] at executed
    | some next =>
      cases tail : recordedRun b next rest with
      | none => simp [recordedRun,first,tail] at executed
      | some value =>
        obtain ⟨last,remaining⟩ := value
        have equal : (last,⟨store,command,next⟩::remaining)=(finished,receipts) := by
          simpa [recordedRun,first,tail] using executed
        cases equal
        have one := checked_receipt_edges b ⟨store,command,next⟩ first
        have later := ih next remaining tail
        constructor
        · intro edge member; exact later.1 edge (one.1 edge member)
        · intro receipt member edge contained
          rcases List.mem_cons.mp member with head|member
          · cases head; exact later.1 edge (one.2 edge contained)
          · exact later.2 receipt member edge contained
-- Class (b): the extension-edge ledger is computed only from the returned actual receipt list.
def ledgerEdges (receipts : List (Receipt S T)) : List (Nat × Nat) := receipts.flatMap receiptEdges
-- Class (b): every computed ledger edge occurs in the final actual graph.
theorem ledger_edges_realized (b : RawBridge H S T E R SC TC RR M)
    (commands : List (NativeDescendant.Command T)) (store finished : Store S T) (receipts : List (Receipt S T))
    (executed : recordedRun b store commands=some (finished,receipts)) :
    ∀ edge∈ledgerEdges receipts,edge∈finished.edges := by
  intro edge member
  obtain ⟨receipt,mem,contained⟩ := List.mem_flatMap.mp member
  exact (recorded_edges_retained b commands store finished receipts executed).2 receipt mem edge contained
-- Class (b): every successful prefix readout contains exactly that prefix's actual graph.
theorem read_at_graph_exact (inputs : RawInputs S T) (store : Store S T) (source target : Nat)
    (original : S) (decoded : T) (edges : List (Nat × Nat)) (computed : computedStore inputs=some store)
    (read : readAt inputs source target=some (original,decoded,edges)) : edges=store.edges := by
  cases first : store.read source with
  | none => simp [readAt,computed,first] at read
  | some content =>
    cases content with
    | record origin time payload => simp [readAt,computed,first] at read
    | target payload => simp [readAt,computed,first] at read
    | source payload =>
      cases second : store.read target with
      | none => simp [readAt,computed,first,second] at read
      | some content =>
        cases content with
        | source other => simp [readAt,computed,first,second] at read
        | record origin time other => simp [readAt,computed,first,second] at read
        | target other =>
          have equal : (payload,other,store.edges)=(original,decoded,edges) := by
            simpa [readAt,computed,first,second] using read
          exact (congrArg (fun value : S × T × List (Nat × Nat) => value.2.2) equal).symm
variable {N : Type} [DecidableEq N]
-- Class (b): raw predictive seed bits reject every unavailable/negative optional decision; they do not default a consumed primitive.
def seedBits (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T) (address : N → Nat)
    (pair : N × N) : Bool := decide (CachedSeed.seedDecision b inputs (address pair.1) (address pair.2)=some true)
-- Class (b): exact all-partial seed membership is the existing source-checked predictive Seed.
theorem seed_bits_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T) (address : N → Nat)
    (pair : N × N) : seedBits b inputs address pair=true ↔ Seed b inputs (address pair.1) (address pair.2) := by
  simp only [seedBits,decide_eq_true_eq,CachedSeed.seed_decision_exact]
-- Class (b): candidate native propagation rules have a single actually related predecessor and preserve the source coordinate.
def nativeRules (nodes : CSTTT.FiniteEnum N) : List (Rule (N × N)) :=
  nodes.elems.flatMap (fun root => nodes.elems.flatMap (fun parent =>
    nodes.elems.map (fun target => ⟨[(root,parent)],(root,target)⟩)))
-- Class (b): every generated candidate propagation rule has its exact nonempty one-predecessor shape.
theorem native_rule_shape (nodes : CSTTT.FiniteEnum N) (rule : Rule (N × N)) (member : rule∈nativeRules nodes) :
    ∃ root parent target,rule=⟨[(root,parent)],(root,target)⟩ := by
  obtain ⟨root,_,next⟩ := List.mem_flatMap.mp member
  obtain ⟨parent,_,last⟩ := List.mem_flatMap.mp next
  obtain ⟨target,_,equal⟩ := List.mem_map.mp last
  exact ⟨root,parent,target,equal.symm⟩
-- Class (b): every declared node triple supplies the actual candidate propagation instruction.
theorem native_rule_member (nodes : CSTTT.FiniteEnum N) (root parent target : N) :
    (⟨[(root,parent)],(root,target)⟩ : Rule (N × N))∈nativeRules nodes := by
  exact List.mem_flatMap.mpr ⟨root,nodes.complete root,List.mem_flatMap.mpr
    ⟨parent,nodes.complete parent,List.mem_map.mpr ⟨target,nodes.complete target,rfl⟩⟩⟩
-- Class (b): the guard consumes actual accepted-receipt edges and the rule's source/predecessor coordinates, not a supplied guard Bool.
def edgeEnabled (address : N → Nat) (edges : List (Nat × Nat)) (rule : Rule (N × N)) : Bool :=
  match rule.prerequisites with
  | [(root,parent)] => decide (rule.conclusion.1=root ∧ (address parent,address rule.conclusion.2)∈edges)
  | _ => false
-- Class (b): a generated rule is enabled exactly by its actual matching accepted native ledger edge.
theorem edge_enabled_exact (address : N → Nat) (edges : List (Nat × Nat)) (root parent target : N) :
    edgeEnabled address edges ⟨[(root,parent)],(root,target)⟩=true ↔ (address parent,address target)∈edges := by
  simp [edgeEnabled]
-- Class (b): actual stored-table ancestry is seeded only by computed predictive Seed and propagates only along receipt-matched edges.
def ancestryBit (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (receipts : List (Receipt S T)) : N × N → Bool :=
  CachedSeed.readCache (CachedSeed.iterateCache (ExecutableSeed.pairEnum nodes)
    (gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address (ledgerEdges receipts)))
    (seedBits b inputs address) (ExecutableSeed.pairEnum nodes).elems.length)
-- Class (b): actual table implementation equals the original exact bounded Horn closure at the unchanged frame bound.
theorem ancestry_bit_exact (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (receipts : List (Receipt S T)) :
    ancestryBit nodes address b inputs receipts=ancestry (ExecutableSeed.pairEnum nodes)
      (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address (ledgerEdges receipts)) := by
  simp only [ancestryBit,CachedSeed.cache_iterate_exact,ancestry,closure]
-- Class (b): the concretely coupled Seed/receipt ancestry is fixed and least among all relations closed under its actual guards.
theorem ancestry_least (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (receipts : List (Receipt S T)) :
    gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address (ledgerEdges receipts))
      (ancestryBit nodes address b inputs receipts)=ancestryBit nodes address b inputs receipts ∧
    ∀ upper,Below (seedBits b inputs address) upper →
      Below (gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address (ledgerEdges receipts)) upper) upper →
      Below (ancestryBit nodes address b inputs receipts) upper := by
  rw [ancestry_bit_exact]
  exact ancestry_least_fixed _ _ _ _
-- Class (b): each actual computed predictive Seed is retained in the coupled ancestry.
theorem ancestry_seed_retained (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (receipts : List (Receipt S T)) (root target : N)
    (seed : Seed b inputs (address root) (address target)) : ancestryBit nodes address b inputs receipts (root,target)=true := by
  rw [ancestry_bit_exact]
  exact ancestry_contains_seed _ _ _ _ _ ((seed_bits_exact b inputs address (root,target)).mpr seed)
-- Class (b): actual native receipt edges propagate an already-related predecessor under the computed fixed point.
theorem ancestry_receipt_descendant (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (receipts : List (Receipt S T)) (root parent target : N)
    (previous : ancestryBit nodes address b inputs receipts (root,parent)=true)
    (edge : (address parent,address target)∈ledgerEdges receipts) :
    ancestryBit nodes address b inputs receipts (root,target)=true := by
  have applied : gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address (ledgerEdges receipts))
      (ancestryBit nodes address b inputs receipts) (root,target)=true := by
    apply (gamma_iff _ _ _ _ _).mpr
    right; right
    refine ⟨⟨[(root,parent)],(root,target)⟩,native_rule_member nodes root parent target,rfl,by simp,?_,?_⟩
    · exact (edge_enabled_exact address (ledgerEdges receipts) root parent target).mpr edge
    · intro pair member
      have equal : pair=(root,parent) := by simpa using member
      exact equal ▸ previous
  have fixed := congrFun (ancestry_least nodes address b inputs receipts).1 (root,target)
  exact fixed ▸ applied
-- Class (b): all coupled ancestry members have a real positive-length path in the actual final graph.
theorem ancestry_path_sound (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (commands : List (NativeDescendant.Command T))
    (store finished : Store S T) (receipts : List (Receipt S T))
    (computed : computedStore inputs=some store) (executed : recordedRun b store commands=some (finished,receipts)) :
    ∀ pair,ancestryBit nodes address b inputs receipts pair=true → Path finished.edges (address pair.1) (address pair.2) := by
  have retained := recorded_edges_retained b commands store finished receipts executed
  have native := ledger_edges_realized b commands store finished receipts executed
  have seeded : ∀ pair,seedBits b inputs address pair=true → Path finished.edges (address pair.1) (address pair.2) := by
    intro pair member
    obtain ⟨original,decoded,edges,read,path,_⟩ := (seed_bits_exact b inputs address pair).mp member
    have equal := read_at_graph_exact inputs store _ _ original decoded edges computed read
    rw [equal] at path
    exact path_inclusion _ _ retained.1 _ _ path
  have sound : ∀ n pair,iterate
      (gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address (ledgerEdges receipts)))
      (seedBits b inputs address) n pair=true → Path finished.edges (address pair.1) (address pair.2) := by
    intro n
    induction n with
    | zero => exact seeded
    | succ n ih =>
      intro pair member
      rcases (gamma_iff _ _ _ _ _).mp member with seed|prior|⟨rule,mem,conclusion,_,guard,all⟩
      · exact seeded pair seed
      · exact ih pair prior
      · obtain ⟨root,parent,target,rfl⟩ := native_rule_shape nodes rule mem
        cases conclusion
        have edge := (edge_enabled_exact address (ledgerEdges receipts) root parent target).mp guard
        exact .extend (ih (root,parent) (all (root,parent) (by simp))) (native _ edge)
  simpa only [ancestryBit,CachedSeed.cache_iterate_exact] using sound (ExecutableSeed.pairEnum nodes).elems.length
-- Class (b): the actual finished execution supplies its own complete queried/edge address frame for the coupled bit.
def finishedBit (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (result : Store S T × List (Receipt S T)) (source target : Nat) : Bool :=
  let nodes := ExecutableSeed.graphEnum result.1.edges source target
  ancestryBit nodes Subtype.val b inputs result.2
    (⟨source,by simp [ExecutableSeed.graphAddresses]⟩,⟨target,by simp [ExecutableSeed.graphAddresses]⟩)
-- Class (b): the campaign first derives the actual execution and receipts, then observes their own coupled ancestry bit.
def actualAncestry (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat) : Option Bool :=
  (actualRecorded b inputs commands).map (fun result => finishedBit b inputs result source target)
-- Class (b): every partial raw assignment has exact unavailable-execution/None equivalence, without a default relation.
theorem actual_ancestry_none_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat) :
    actualAncestry b inputs commands source target=none ↔ actualRecorded b inputs commands=none := by
  cases read : actualRecorded b inputs commands with
  | none => simp [actualAncestry,read]
  | some value => obtain ⟨finished,receipts⟩ := value; simp [actualAncestry,read]
-- Class (b): actual source absence rejects every raw extension and every coupled ancestry query.
theorem missing_source_ancestry (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (missing : inputs.rawSource=none) : ∀ commands source target,actualAncestry b inputs commands source target=none := by
  intro commands source target
  apply (actual_ancestry_none_exact _ _ _ _ _).mpr
  apply missing_prefix_receipts
  simp [computedStore,SourceCheckedTrace.checkedExecute,missing]
-- Class (b): every partial input has exact some-true correspondence with the actually computed result and its coupled bit.
theorem actual_ancestry_true_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat) :
    actualAncestry b inputs commands source target=some true ↔
      ∃ result,actualRecorded b inputs commands=some result ∧ finishedBit b inputs result source target=true := by
  cases read : actualRecorded b inputs commands with
  | none => simp [actualAncestry,read]
  | some result => simp [actualAncestry,read]
-- Class (b): every partial input preserves the distinction between unavailable execution and present but excluded ancestry.
theorem actual_ancestry_false_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat) :
    actualAncestry b inputs commands source target=some false ↔
      (actualRecorded b inputs commands).isSome ∧ actualAncestry b inputs commands source target≠some true := by
  cases read : actualRecorded b inputs commands with
  | none => simp [actualAncestry,read]
  | some result => cases value : finishedBit b inputs result source target <;> simp [actualAncestry,read,value]
-- Class (b): a true bit for an actual recorded execution directly returns a real path in that execution's final graph.
theorem finished_bit_path (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (store finished : Store S T) (receipts : List (Receipt S T))
    (source target : Nat) (computed : computedStore inputs=some store)
    (executed : recordedRun b store commands=some (finished,receipts))
    (bit : finishedBit b inputs (finished,receipts) source target=true) : Path finished.edges source target :=
  ancestry_path_sound (ExecutableSeed.graphEnum finished.edges source target) Subtype.val b inputs commands
    store finished receipts computed executed
    (⟨source,by simp [ExecutableSeed.graphAddresses]⟩,⟨target,by simp [ExecutableSeed.graphAddresses]⟩) bit
-- Class (b): actual true ancestry returns actual prefix, receipts, final store and positive-length final graph path.
theorem actual_ancestry_path (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat)
    (positive : actualAncestry b inputs commands source target=some true) :
    ∃ store finished receipts,computedStore inputs=some store ∧
      recordedRun b store commands=some (finished,receipts) ∧ Path finished.edges source target := by
  obtain ⟨result,recorded,bit⟩ := (actual_ancestry_true_exact b inputs commands source target).mp positive
  obtain ⟨finished,receipts⟩ := result
  cases computed : computedStore inputs with
  | none => simp [actualRecorded,computed] at recorded
  | some store =>
    have executed : recordedRun b store commands=some (finished,receipts) := by
      simpa [actualRecorded,computed] using recorded
    exact ⟨store,finished,receipts,rfl,executed,
      finished_bit_path b inputs commands store finished receipts source target computed executed bit⟩
-- Class (b): every actual successful native extension gives a false coupled ancestry readout at an occupied disconnected twin.
theorem actual_twin_ancestry_false (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (store finished : Store S T) (receipts : List (Receipt S T))
    (source twin : Nat) (payload : T) (computed : computedStore inputs=some store)
    (occupied : store.read twin=some (.target payload)) (missing : ∀ predecessor,(predecessor,twin)∉store.edges)
    (executed : recordedRun b store commands=some (finished,receipts)) :
    actualAncestry b inputs commands source twin=some false := by
  have extension : NativeDescendant.run b store commands=some finished := by
    rw [← recorded_run_exact b commands store,executed]
    rfl
  have boundary := run_boundary_retained b commands store finished twin (.target payload) occupied missing extension
  have negative : finishedBit b inputs (finished,receipts) source twin=false := by
    cases bit : finishedBit b inputs (finished,receipts) source twin with
    | false => rfl
    | true => exact False.elim ((no_incoming_excludes finished.edges twin boundary.2 source)
        (finished_bit_path b inputs commands store finished receipts source twin computed executed bit))
  simp [actualAncestry,actualRecorded,computed,executed,negative]
-- Class (b): no predictive seed for a given source means no coupled descendant, since every native rule preserves that source coordinate.
theorem no_seed_source_excluded (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (receipts : List (Receipt S T)) (root : N)
    (missing : ∀ target,¬ Seed b inputs (address root) (address target)) :
    ∀ target,ancestryBit nodes address b inputs receipts (root,target)=false := by
  let blocked : N × N → Bool := fun pair => decide (pair.1=root)
  have seedOutside : ∀ pair,seedBits b inputs address pair=true → blocked pair=false := by
    intro pair member
    by_cases equal : pair.1=root
    · have impossible := missing pair.2
      have seed := (seed_bits_exact b inputs address pair).mp member
      rw [equal] at seed
      exact False.elim (impossible seed)
    · simp [blocked,equal]
  have ruleOutside : ∀ rule∈nativeRules nodes,edgeEnabled address (ledgerEdges receipts) rule=true →
      blocked rule.conclusion=true → ∃ predecessor∈rule.prerequisites,blocked predecessor=true := by
    intro rule member _ conclusion
    obtain ⟨source,parent,target,rfl⟩ := native_rule_shape nodes rule member
    exact ⟨(source,parent),by simp,conclusion⟩
  have excluded := component_exclusion (ExecutableSeed.pairEnum nodes) (seedBits b inputs address)
    (nativeRules nodes) (edgeEnabled address (ledgerEdges receipts)) blocked seedOutside ruleOutside
  intro target
  rw [ancestry_bit_exact]
  cases bit : ancestry (ExecutableSeed.pairEnum nodes) (seedBits b inputs address)
      (nativeRules nodes) (edgeEnabled address (ledgerEdges receipts)) (root,target) with
  | false => rfl
  | true => have impossible := excluded (root,target) bit; simp [blocked] at impossible
-- Class (b): every coupled member originates in an actual predictive Seed and then follows only accepted-receipt ledger edges.
theorem ancestry_origin (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (receipts : List (Receipt S T)) :
    ∀ pair,ancestryBit nodes address b inputs receipts pair=true → ∃ seeded : N,
      Seed b inputs (address pair.1) (address seeded) ∧
        (seeded=pair.2 ∨ Path (ledgerEdges receipts) (address seeded) (address pair.2)) := by
  have origin : ∀ n pair,iterate
      (gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address (ledgerEdges receipts)))
      (seedBits b inputs address) n pair=true → ∃ seeded : N,
        Seed b inputs (address pair.1) (address seeded) ∧
          (seeded=pair.2 ∨ Path (ledgerEdges receipts) (address seeded) (address pair.2)) := by
    intro n
    induction n with
    | zero =>
      intro pair member
      exact ⟨pair.2,(seed_bits_exact b inputs address pair).mp member,Or.inl rfl⟩
    | succ n ih =>
      intro pair member
      rcases (gamma_iff _ _ _ _ _).mp member with seed|prior|⟨rule,mem,conclusion,_,guard,all⟩
      · exact ⟨pair.2,(seed_bits_exact b inputs address pair).mp seed,Or.inl rfl⟩
      · exact ih pair prior
      · obtain ⟨root,parent,target,rfl⟩ := native_rule_shape nodes rule mem
        cases conclusion
        have edge := (edge_enabled_exact address (ledgerEdges receipts) root parent target).mp guard
        obtain ⟨seeded,seed,previous⟩ := ih (root,parent) (all (root,parent) (by simp))
        refine ⟨seeded,seed,Or.inr ?_⟩
        rcases previous with equal|path
        · cases equal; exact .one edge
        · exact .extend path edge
  simpa only [ancestryBit,CachedSeed.cache_iterate_exact] using origin (ExecutableSeed.pairEnum nodes).elems.length
-- Class (b): an actual checked fission receipt propagates both coupled branches and returns their equal actual payload/activity.
theorem actual_receipt_fission (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (commands : List (NativeDescendant.Command T))
    (store finished : Store S T) (receipts : List (Receipt S T)) (receipt : Receipt S T)
    (root parent left right : N) (executed : recordedRun b store commands=some (finished,receipts))
    (member : receipt∈receipts) (command : receipt.command=.fission (address parent) (address left) (address right))
    (previous : ancestryBit nodes address b inputs receipts (root,parent)=true) :
    ancestryBit nodes address b inputs receipts (root,left)=true ∧
    ancestryBit nodes address b inputs receipts (root,right)=true ∧
    receipt.after.read (address left)=receipt.after.read (address right) ∧
    receipt.after.active (address left)=true ∧ receipt.after.active (address right)=true := by
  have checked := every_receipt_checked b commands store finished receipts executed receipt member
  have shape := checked_receipt_shape b receipt checked
  rw [command] at shape
  obtain ⟨payload,_,_,_,_,distinct,after⟩ := shape
  have leftEdge : (address parent,address left)∈ledgerEdges receipts :=
    List.mem_flatMap.mpr ⟨receipt,member,by simp [receiptEdges,command]⟩
  have rightEdge : (address parent,address right)∈ledgerEdges receipts :=
    List.mem_flatMap.mpr ⟨receipt,member,by simp [receiptEdges,command]⟩
  have contents := fission_equal_readouts receipt.before (address parent) (address left) (address right) payload distinct
  refine ⟨ancestry_receipt_descendant nodes address b inputs receipts root parent left previous leftEdge,
    ancestry_receipt_descendant nodes address b inputs receipts root parent right previous rightEdge,?_,?_,?_⟩
  · rw [after]; exact contents.1.trans contents.2.1.symm
  · rw [after]; exact contents.2.2.1
  · rw [after]; exact contents.2.2.2.1
-- Class (b): an actual advance receipt propagates ancestry and exposes its matching native row/action/outcome, not just an arbitrary graph edge.
theorem actual_receipt_advance (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (commands : List (NativeDescendant.Command T))
    (store finished : Store S T) (receipts : List (Receipt S T)) (receipt : Receipt S T)
    (root parent target : N) (action : Nat) (outcome : T)
    (executed : recordedRun b store commands=some (finished,receipts)) (member : receipt∈receipts)
    (command : receipt.command=.advance (address parent) (address target) action outcome)
    (previous : ancestryBit nodes address b inputs receipts (root,parent)=true) :
    ancestryBit nodes address b inputs receipts (root,target)=true ∧
    (∃ payload,receipt.before.read (address parent)=some (.target payload) ∧
      0<b.targetActionStep payload action outcome) ∧
    receipt.after.read (address target)=some (.target outcome) ∧ receipt.after.active (address target)=true := by
  have checked := every_receipt_checked b commands store finished receipts executed receipt member
  have shape := checked_receipt_shape b receipt checked
  rw [command] at shape
  obtain ⟨payload,read,_,_,support,after⟩ := shape
  have edge : (address parent,address target)∈ledgerEdges receipts :=
    List.mem_flatMap.mpr ⟨receipt,member,by simp [receiptEdges,command]⟩
  exact ⟨ancestry_receipt_descendant nodes address b inputs receipts root parent target previous edge,
    ⟨payload,read,support⟩,by simp [after,advanced,put],by simp [after,advanced,switch]⟩
-- Class (b): a complete declared address frame lets every ledger path propagate coupled ancestry; no injectivity premise is needed.
theorem ancestry_ledger_complete (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (receipts : List (Receipt S T))
    (cover : ∀ edge∈ledgerEdges receipts,∃ parent : N,address parent=edge.1)
    (root first last : N) (previous : ancestryBit nodes address b inputs receipts (root,first)=true)
    (path : Path (ledgerEdges receipts) (address first) (address last)) :
    ancestryBit nodes address b inputs receipts (root,last)=true := by
  have lift : ∀ a c,Path (ledgerEdges receipts) a c → ∀ start stop : N,
      address start=a → address stop=c → ancestryBit nodes address b inputs receipts (root,start)=true →
        ancestryBit nodes address b inputs receipts (root,stop)=true := by
    intro a c path
    induction path with
    | one member =>
      intro start stop startEq stopEq prior
      apply ancestry_receipt_descendant nodes address b inputs receipts root start stop prior
      simpa [startEq,stopEq] using member
    | extend previous member ih =>
      intro start stop startEq stopEq prior
      obtain ⟨parent,parentEq⟩ := cover _ member
      apply ancestry_receipt_descendant nodes address b inputs receipts root parent stop
      · exact ih start parent startEq parentEq prior
      · simpa [parentEq,stopEq] using member
  exact lift _ _ path first last rfl rfl previous
-- Class (b): every positive-length actual path supplies endpoint membership in the complete runtime address frame.
theorem path_endpoint_in_frame (edges : List (Nat × Nat)) (source target start endpoint : Nat)
    (path : Path edges start endpoint) : endpoint∈ExecutableSeed.graphAddresses edges source target := by
  cases path with
  | one member => exact (ExecutableSeed.graph_endpoints edges source target _ member).2
  | extend previous member => exact (ExecutableSeed.graph_endpoints edges source target _ member).2
-- Class (b): each computed predictive seed has a real prefix path retained in every successful actual native execution.
theorem recorded_seed_path (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (store finished : Store S T) (receipts : List (Receipt S T))
    (source seeded : Nat) (computed : computedStore inputs=some store)
    (executed : recordedRun b store commands=some (finished,receipts)) (seed : Seed b inputs source seeded) :
    Path finished.edges source seeded := by
  obtain ⟨original,decoded,edges,read,path,_⟩ := seed
  have equal := read_at_graph_exact inputs store source seeded original decoded edges computed read
  rw [equal] at path
  exact path_inclusion _ _ (recorded_edges_retained b commands store finished receipts executed).1 _ _ path
-- Class (b): actual finite-frame ancestry is exactly an actual predictive seed followed by zero or more accepted native ledger edges.
theorem finished_bit_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (store finished : Store S T) (receipts : List (Receipt S T))
    (source target : Nat) (computed : computedStore inputs=some store)
    (executed : recordedRun b store commands=some (finished,receipts)) :
    finishedBit b inputs (finished,receipts) source target=true ↔ ∃ seeded : Nat,
      Seed b inputs source seeded ∧ (seeded=target ∨ Path (ledgerEdges receipts) seeded target) := by
  let nodes := ExecutableSeed.graphEnum finished.edges source target
  let root : ExecutableSeed.GraphNode finished.edges source target := ⟨source,by simp [ExecutableSeed.graphAddresses]⟩
  let last : ExecutableSeed.GraphNode finished.edges source target := ⟨target,by simp [ExecutableSeed.graphAddresses]⟩
  constructor
  · intro member
    obtain ⟨seeded,seed,path⟩ := ancestry_origin nodes Subtype.val b inputs receipts (root,last) member
    refine ⟨seeded.val,seed,?_⟩
    rcases path with equal|path
    · exact Or.inl (congrArg Subtype.val equal)
    · exact Or.inr path
  · rintro ⟨point,seed,path⟩
    have actualPath := recorded_seed_path b inputs commands store finished receipts source point computed executed seed
    let start : ExecutableSeed.GraphNode finished.edges source target :=
      ⟨point,path_endpoint_in_frame finished.edges source target source point actualPath⟩
    have initial : ancestryBit nodes Subtype.val b inputs receipts (root,start)=true :=
      ancestry_seed_retained nodes Subtype.val b inputs receipts root start seed
    rcases path with equal|path
    · have same : start=last := Subtype.ext equal
      change ancestryBit nodes Subtype.val b inputs receipts (root,last)=true
      rw [← same]
      exact initial
    · have cover : ∀ edge∈ledgerEdges receipts,∃ parent : ExecutableSeed.GraphNode finished.edges source target,parent.val=edge.1 := by
        intro edge member
        have realized := ledger_edges_realized b commands store finished receipts executed edge member
        exact ⟨⟨edge.1,(ExecutableSeed.graph_endpoints finished.edges source target edge realized).1⟩,rfl⟩
      exact ancestry_ledger_complete nodes Subtype.val b inputs receipts cover root start last initial path
-- Class (b): exact source-to-descendant readout for every partial campaign input; all intermediate objects are computed, never primitive snapshots.
theorem actual_ancestry_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat) :
    actualAncestry b inputs commands source target=some true ↔ ∃ store finished receipts,
      computedStore inputs=some store ∧ recordedRun b store commands=some (finished,receipts) ∧
        ∃ seeded : Nat,Seed b inputs source seeded ∧ (seeded=target ∨ Path (ledgerEdges receipts) seeded target) := by
  constructor
  · intro positive
    obtain ⟨result,recorded,bit⟩ := (actual_ancestry_true_exact b inputs commands source target).mp positive
    obtain ⟨finished,receipts⟩ := result
    cases computed : computedStore inputs with
    | none => simp [actualRecorded,computed] at recorded
    | some store =>
      have executed : recordedRun b store commands=some (finished,receipts) := by simpa [actualRecorded,computed] using recorded
      exact ⟨store,finished,receipts,rfl,executed,
        (finished_bit_exact b inputs commands store finished receipts source target computed executed).mp bit⟩
  · rintro ⟨store,finished,receipts,computed,executed,origin⟩
    apply (actual_ancestry_true_exact b inputs commands source target).mpr
    exact ⟨(finished,receipts),by simp [actualRecorded,computed,executed],
      (finished_bit_exact b inputs commands store finished receipts source target computed executed).mpr origin⟩
end CSTTT.FallbackTheory.ReceiptAncestry
