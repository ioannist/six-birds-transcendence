import CSTTT.Fallback.FiniteClosure
import CSTTT.Fallback.OperationalTrace
import CSTTT.Fallback.OperationalSeed

namespace CSTTT.FallbackTheory.ExecutableSeed
open CSTTT.FallbackTheory.FiniteClosure
open CSTTT.FallbackTheory.FiniteHorn
open CSTTT.FallbackTheory.OperationalTrace
variable {N : Type} [DecidableEq N]
-- Class (b): construct the finite pair presentation from declared raw nodes.
def pairEnum (nodes : CSTTT.FiniteEnum N) : CSTTT.FiniteEnum (N × N) where
  elems := nodes.elems.flatMap (fun x => nodes.elems.map (fun y => (x,y)))
  complete := by
    rintro ⟨x,y⟩
    exact List.mem_flatMap.mpr ⟨x,nodes.complete x,List.mem_map.mpr ⟨y,nodes.complete y,rfl⟩⟩
-- Class (b): all transitivity instructions are generated from finite raw nodes, without supplied ancestry.
def transRules (nodes : CSTTT.FiniteEnum N) : List (Rule (N × N)) :=
  nodes.elems.flatMap (fun x => nodes.elems.flatMap (fun y =>
    nodes.elems.map (fun z => ⟨[(x,y),(y,z)],(x,z)⟩)))
-- Class (b): every generated rule has its exact two-predecessor transitivity form.
theorem trans_rule_shape (nodes : CSTTT.FiniteEnum N) (rule : Rule (N × N))
    (member : rule∈transRules nodes) : ∃ x y z, rule=⟨[(x,y),(y,z)],(x,z)⟩ := by
  obtain ⟨x,_,hy⟩ := List.mem_flatMap.mp member
  obtain ⟨y,_,hz⟩ := List.mem_flatMap.mp hy
  obtain ⟨z,_,eq⟩ := List.mem_map.mp hz
  exact ⟨x,y,z,eq.symm⟩
-- Class (b): every declared node triple supplies the actual needed generated rule.
theorem trans_rule_member (nodes : CSTTT.FiniteEnum N) (x y z : N) :
    (⟨[(x,y),(y,z)],(x,z)⟩ : Rule (N × N))∈transRules nodes := by
  exact List.mem_flatMap.mpr ⟨x,nodes.complete x,List.mem_flatMap.mpr
    ⟨y,nodes.complete y,List.mem_map.mpr ⟨z,nodes.complete z,rfl⟩⟩⟩
-- Class (b): direct operational edges are computed seed bits, not supplied reachable pairs.
def edgeSeed (edges : List (N × N)) (pair : N × N) : Bool := decide (pair∈edges)
-- Class (b): actual bounded Horn reachability is a computable function of finite nodes and edges.
def reachable (nodes : CSTTT.FiniteEnum N) (edges : List (N × N)) : N × N → Bool :=
  ancestry (pairEnum nodes) (edgeSeed edges) (transRules nodes) (fun _ => true)
-- Class (b): raw address projection retains every actual edge in its original order.
def addressedEdges (address : N → Nat) (edges : List (N × N)) : List (Nat × Nat) :=
  edges.map (fun pair => (address pair.1,address pair.2))
-- Class (b): positive-length operational paths compose, without adding reflexivity.
theorem path_trans {edges : List (Nat × Nat)} {x y z : Nat}
    (first : Path edges x y) (second : Path edges y z) : Path edges x z := by
  induction second with
  | one member => exact .extend first member
  | extend previous member ih => exact .extend ih member
-- Class (b): every direct seed is retained in actual bounded reachability.
theorem edges_retained (nodes : CSTTT.FiniteEnum N) (edges : List (N × N)) (x y : N)
    (member : (x,y)∈edges) : reachable nodes edges (x,y)=true :=
  ancestry_contains_seed (pairEnum nodes) (edgeSeed edges) (transRules nodes) (fun _ => true) _ (by simp [edgeSeed,member])
-- Class (b): actual bounded reachability is transitive by its generated rules and computed fixed-point equation.
theorem reachable_trans (nodes : CSTTT.FiniteEnum N) (edges : List (N × N)) (x y z : N)
    (first : reachable nodes edges (x,y)=true) (second : reachable nodes edges (y,z)=true) :
    reachable nodes edges (x,z)=true := by
  have fixed := (ancestry_least_fixed (pairEnum nodes) (edgeSeed edges) (transRules nodes) (fun _ => true)).1
  have applied : gamma (edgeSeed edges) (transRules nodes) (fun _ => true) (reachable nodes edges) (x,z)=true := by
    apply (gamma_iff _ _ _ _ _).mpr
    right; right
    refine ⟨⟨[(x,y),(y,z)],(x,z)⟩,trans_rule_member nodes x y z,rfl,?_,rfl,?_⟩
    · simp
    · intro pair member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      · exact first
      · exact second
  have eq : gamma (edgeSeed edges) (transRules nodes) (fun _ => true) (reachable nodes edges) (x,z)=
      reachable nodes edges (x,z) := congrFun fixed (x,z)
  exact eq ▸ applied
-- Class (b): every computed reachability bit supplies an actual positive-length path on the emitted address graph.
theorem reachable_sound (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (edges : List (N × N)) :
    ∀ pair, reachable nodes edges pair=true → Path (addressedEdges address edges) (address pair.1) (address pair.2) := by
  have seeded : ∀ pair, edgeSeed edges pair=true → Path (addressedEdges address edges) (address pair.1) (address pair.2) := by
    intro pair member
    apply Path.one
    apply List.mem_map.mpr
    exact ⟨pair,by simpa [edgeSeed] using member,rfl⟩
  have sound : ∀ n pair, iterate (gamma (edgeSeed edges) (transRules nodes) (fun _ => true)) (edgeSeed edges) n pair=true →
      Path (addressedEdges address edges) (address pair.1) (address pair.2) := by
    intro n
    induction n with
    | zero => exact seeded
    | succ n ih =>
      intro pair member
      rcases (gamma_iff _ _ _ _ _).mp member with hs|hp|⟨rule,mem,conclusion,_,_,all⟩
      · exact seeded pair hs
      · exact ih pair hp
      · obtain ⟨x,y,z,rfl⟩ := trans_rule_shape nodes rule mem
        cases conclusion
        have first := ih (x,y) (all (x,y) (by simp))
        have second := ih (y,z) (all (y,z) (by simp))
        exact path_trans first second
  exact sound _
-- Class (b): every actual addressed path returns computed reachability under an injective declared node addressing.
theorem reachable_complete (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (injective : Function.Injective address)
    (edges : List (N × N)) (x z : N)
    (path : Path (addressedEdges address edges) (address x) (address z)) : reachable nodes edges (x,z)=true := by
  have lift : ∀ a c, Path (addressedEdges address edges) a c →
      ∀ first last, address first=a → address last=c → reachable nodes edges (first,last)=true := by
    intro a c path
    induction path with
    | one member =>
      intro first last hf hl
      obtain ⟨pair,mem,eq⟩ := List.mem_map.mp member
      have left : pair.1=first := injective ((congrArg Prod.fst eq).trans hf.symm)
      have right : pair.2=last := injective ((congrArg Prod.snd eq).trans hl.symm)
      have pairEq : pair=(first,last) := Prod.ext left right
      rw [pairEq] at mem
      exact edges_retained nodes edges first last mem
    | extend previous member ih =>
      intro first last hf hl
      obtain ⟨pair,mem,eq⟩ := List.mem_map.mp member
      have right : pair.2=last := injective ((congrArg Prod.snd eq).trans hl.symm)
      have prior := ih first pair.1 hf (congrArg Prod.fst eq)
      have final := edges_retained nodes edges pair.1 pair.2 mem
      rw [right] at final
      exact reachable_trans nodes edges first pair.1 last prior final
  exact lift _ _ path x z rfl rfl
-- Class (b): exact all-input executable reachability/path correspondence, including disconnected and empty graphs.
theorem reachable_iff_path (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (injective : Function.Injective address)
    (edges : List (N × N)) (x z : N) :
    reachable nodes edges (x,z)=true ↔ Path (addressedEdges address edges) (address x) (address z) :=
  ⟨reachable_sound nodes address edges (x,z),reachable_complete nodes address injective edges x z⟩

-- Class (b): finite runtime addresses are generated from the actual graph and queried endpoints.
def graphAddresses (edges : List (Nat × Nat)) (source target : Nat) : List Nat :=
  source :: target :: edges.flatMap (fun edge => [edge.1,edge.2])
-- Class (b): runtime nodes are actual addresses with membership evidence, not arbitrary copied node identifiers.
@[reducible] def GraphNode (edges : List (Nat × Nat)) (source target : Nat) :=
  { address : Nat // address∈graphAddresses edges source target }
-- Class (b): complete finite runtime presentation is computed by attaching membership to the actual address list.
def graphEnum (edges : List (Nat × Nat)) (source target : Nat) :
    CSTTT.FiniteEnum (GraphNode edges source target) where
  elems := (graphAddresses edges source target).attach
  complete := List.mem_attach _
-- Class (b): every actual emitted edge's two endpoints belong to the computed address frame.
theorem graph_endpoints (edges : List (Nat × Nat)) (source target : Nat) (edge : Nat × Nat)
    (member : edge∈edges) : edge.1∈graphAddresses edges source target ∧ edge.2∈graphAddresses edges source target := by
  constructor <;> simp only [graphAddresses,List.mem_cons] <;> right <;> right
  · exact List.mem_flatMap.mpr ⟨edge,member,by simp⟩
  · exact List.mem_flatMap.mpr ⟨edge,member,by simp⟩
-- Class (b): typed runtime edges are computed from actual edges and derived endpoint membership.
def graphEdges (edges : List (Nat × Nat)) (source target : Nat) :
    List (GraphNode edges source target × GraphNode edges source target) :=
  edges.attach.map (fun edge =>
    (⟨edge.val.1,(graph_endpoints edges source target edge.val edge.property).1⟩,
     ⟨edge.val.2,(graph_endpoints edges source target edge.val edge.property).2⟩))
-- Class (b): address projection of the computed typed graph is exactly the original emitted graph.
theorem graph_edges_exact (edges : List (Nat × Nat)) (source target : Nat) :
    addressedEdges Subtype.val (graphEdges edges source target)=edges := by
  simp only [addressedEdges,graphEdges,List.map_map,Function.comp_def]
  change edges.attach.map Subtype.val=edges
  exact List.attach_map_subtype_val edges
-- Class (b): executable positive-length reachability needs no supplied path proof or externally complete node frame.
def pathBit (edges : List (Nat × Nat)) (source target : Nat) : Bool :=
  reachable (graphEnum edges source target) (graphEdges edges source target)
    (⟨source,by simp [graphAddresses]⟩,⟨target,by simp [graphAddresses]⟩)
-- Class (b): every input graph, including empty/disconnected graphs and equal endpoints, has exact Boolean/path correspondence.
theorem path_bit_exact (edges : List (Nat × Nat)) (source target : Nat) :
    pathBit edges source target=true ↔ Path edges source target := by
  have exactness := reachable_iff_path (graphEnum edges source target) Subtype.val
    (fun _ _ eq => Subtype.ext eq) (graphEdges edges source target)
    ⟨source,by simp [graphAddresses]⟩ ⟨target,by simp [graphAddresses]⟩
  simpa only [pathBit,graph_edges_exact] using exactness

open CSTTT.TransportTheory
open CSTTT.FallbackTheory.RawPredictiveQuotient
open CSTTT.FallbackTheory.SharedOperationalSeed
variable {H S T E R SC TC RR M : Type} [DecidableEq S]
-- Class (b): optional executable Seed consumes typed reads from the same computed store; missing reads reject directly.
def seedDecision (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (source target : Nat) : Option Bool := do
  let (original,decoded,edges) ← readAt inputs source target
  some (pathBit edges source target &&
    decide (sourceSignature b (classQueries b) original=targetSignature b (classQueries b) decoded))
-- Class (b): every partial input assignment has exact executable/shared Seed equivalence, without extra frame assumptions.
theorem seed_decision_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (source target : Nat) : seedDecision b inputs source target=some true ↔ Seed b inputs source target := by
  cases read : readAt inputs source target with
  | none => simp [seedDecision,Seed,read]
  | some value =>
    obtain ⟨original,decoded,edges⟩ := value
    simp only [seedDecision,read]
    change some (pathBit edges source target && decide (sourceSignature b (classQueries b) original=
      targetSignature b (classQueries b) decoded))=some true ↔ Seed b inputs source target
    simp only [Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq]
    rw [path_bit_exact]
    constructor
    · rintro ⟨path,pred⟩
      exact ⟨original,decoded,edges,read,path,pred⟩
    · rintro ⟨otherOriginal,otherDecoded,otherEdges,otherRead,path,pred⟩
      have equality := Option.some.inj (read.symm.trans otherRead)
      cases equality
      exact ⟨path,pred⟩
-- Class (b): unavailable consumed execution/readout gives None on every partial assignment, never a default verdict.
theorem missing_read_decision (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (source target : Nat) (missing : readAt inputs source target=none) :
    seedDecision b inputs source target=none := by simp [seedDecision,missing]
-- Class (b): missing source excludes every optional Seed decision directly, regardless of all other primitive fields.
theorem missing_source_decision (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (missing : inputs.rawSource=none) : ∀ source target, seedDecision b inputs source target=none := by
  intro source target
  apply missing_read_decision
  simp [readAt,computedStore,SourceCheckedTrace.checkedExecute,missing]

-- Class (b): exact missing-read/None equivalence on every partial shared assignment.
theorem seed_decision_none_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (source target : Nat) : seedDecision b inputs source target=none ↔ readAt inputs source target=none := by
  cases read : readAt inputs source target with
  | none => simp [seedDecision,read]
  | some value =>
    obtain ⟨original,decoded,edges⟩ := value
    simp [seedDecision,read]
-- Class (b): exact available-but-negative decision; absence and negative classification remain separate outcomes.
theorem seed_decision_false_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (source target : Nat) : seedDecision b inputs source target=some false ↔
      (readAt inputs source target).isSome ∧ ¬ Seed b inputs source target := by
  rw [← seed_decision_exact]
  have presence : (readAt inputs source target).isSome=(seedDecision b inputs source target).isSome := by
    cases read : readAt inputs source target with
    | none => simp [seedDecision,read]
    | some value => obtain ⟨original,decoded,edges⟩ := value; simp [seedDecision,read]
  rw [presence]
  cases decision : seedDecision b inputs source target with
  | none => simp
  | some value => cases value <;> simp
-- Class (b): failed actual execution gives no decisions for any queried pair, regardless of all remaining raw fields.
theorem failed_store_decisions (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (failed : computedStore inputs=none) : ∀ source target, seedDecision b inputs source target=none := by
  intro source target
  exact missing_read_decision b inputs source target (by simp [readAt,failed])
-- Class (b): no incoming raw operational edges directly refutes the executable path bit.
theorem no_incoming_bit_false (edges : List (Nat × Nat)) (source target : Nat)
    (missing : ∀ predecessor, (predecessor,target)∉edges) : pathBit edges source target=false := by
  cases bit : pathBit edges source target with
  | false => rfl
  | true => exact False.elim (no_incoming_excludes edges target missing source ((path_bit_exact _ _ _).mp bit))
-- Class (b): actual typed readouts at a disconnected target give a false decision, even if the predictive signatures coincide.
theorem disconnected_read_decision_false (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (source target : Nat) (original : S) (decoded : T) (edges : List (Nat × Nat))
    (read : readAt inputs source target=some (original,decoded,edges))
    (missing : ∀ predecessor, (predecessor,target)∉edges) :
    seedDecision b inputs source target=some false := by
  simp [seedDecision,read,no_incoming_bit_false edges source target missing]
-- Class (b): successful executable Seed returns actual typed readouts, path and every predictive query under the complete raw laws.
theorem decision_predictive_sound (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (sourceComplete : ∀ x, x∈b.sourceStates) (targetComplete : ∀ y, y∈b.targetStates)
    (bisim : SourceActionBisim b) (inputs : RawInputs S T) (source target : Nat)
    (decision : seedDecision b inputs source target=some true) :
    ∃ original decoded edges, readAt inputs source target=some (original,decoded,edges) ∧
      Path edges source target ∧ ∀ query, sourceFuture b original query=targetFuture b decoded query :=
  shared_seed_sound b laws sourceComplete targetComplete bisim inputs source target
    ((seed_decision_exact b inputs source target).mp decision)
end CSTTT.FallbackTheory.ExecutableSeed
