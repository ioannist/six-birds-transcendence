import CSTTT.POS04.Assigned.C6FrozenLinks
import CSTTT.Package.FiniteGluing

/-! G2c: generic staging/gluing of arbitrary assignments in the shared typed
primitive-cell namespace. C4–C7 retain their surrogate grades. Clause rules
are the assigned evaluators, never `Index → Prop` inputs. No lineage,
corridor, receiver transfer or post-withdrawal autonomy premise is used.
C8 operational package viability remains clause content. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.PackageTheory

def clauseAccept (a : Assignment) (tag : Tag) : Clause → Prop
  | .c1 => C1Accept a tag | .c2 => C2Accept a tag | .c3 => C3Accept a tag
  | .c4 => C4Accept a tag | .c5 => C5Accept a tag | .c6 => C6Accept a tag
  | .c7 => C7Accept a tag | .c8 => C8Accept a tag
def clauseGate (a : Assignment) (tag : Tag) : Clause → Prop
  | .c1 => C1Gate a tag | .c2 => C2Gate a tag | .c3 => C3Gate a tag
  | .c4 => C4Gate a tag | .c5 => C5Gate a tag | .c6 => C6Gate a tag
  | .c7 => C7Gate a tag | .c8 => C8Gate a tag
def AssignedPackagePass (a : Assignment) (tag : Tag) : Prop := ∀ c, clauseAccept a tag c

theorem clause_accept_locality {a b : Assignment} (tag : Tag) (c : Clause)
    (h : Agrees (clauseScope tag c) a b) : clauseAccept a tag c ↔ clauseAccept b tag c := by
  cases c
  · exact c1_acceptance_locality h
  · exact c2_acceptance_locality h
  · exact c3_acceptance_locality h
  · exact c4_acceptance_locality h
  · exact c5_acceptance_locality h
  · exact c6_accept_locality h
  · exact c7_acceptance_locality h
  · exact c8_accept_locality h

theorem clause_accept_implies_gate {a : Assignment} {tag : Tag} (c : Clause)
    (h : clauseAccept a tag c) : clauseGate a tag c := by cases c <;> exact h.1

/-- Raw list scopes, parent map and ranks. All structural evidence is checked
separately; adjacency is determined by parent, not an independent field. -/
structure RawPackageCover where
  root : Clause
  parent : Clause → Option Clause
  rank : Clause → Nat
  scopes : Clause → List Cell

def RawPackageCover.adjacent (r : RawPackageCover) (i j : Clause) : Prop :=
  r.parent i = some j ∨ r.parent j = some i
structure CoverCheck (r : RawPackageCover) (tag : Tag) : Prop where
  rootParent : r.parent r.root = none
  totalParent : ∀ i, i ≠ r.root → ∃ p, r.parent i = some p
  decreasing : ∀ i p, r.parent i = some p → r.rank p < r.rank i
  covers : ∀ k : Cell, ∃ i, k ∈ r.scopes i
  running : ∀ i j k, k ∈ r.scopes i → k ∈ r.scopes j →
    ScopedReach r.adjacent (fun c k => k ∈ r.scopes c) k i j
  dependencies : ∀ c k, k ∈ clauseScope tag c → k ∈ r.scopes c

def checkedTree (r : RawPackageCover) (tag : Tag) (h : CoverCheck r tag) : RootedJoinTree Clause Cell :=
  ⟨r.root,r.parent,h.rootParent,h.totalParent,r.rank,h.decreasing,
    (fun c k => k ∈ r.scopes c),h.covers,h.running⟩

theorem checked_tree_adjacency (r : RawPackageCover) (tag : Tag) (h : CoverCheck r tag) (i j : Clause) :
    (checkedTree r tag h).adjacent i j ↔ r.adjacent i j := Iff.rfl

/-- Typed source-reference and raw value operation. Missing arrows reject.
The operation's codomain is the destination cell's primitive type. -/
structure CellArrow (target : Cell) where
  source : Cell
  operation : Value source → Option (Value target)
structure RawStageMap where
  arrows : Clause → (target : Cell) → Option (CellArrow target)

/-- Fixed tag exchange of coordinate identity, preserving primitive families. -/
def swapTag : Tag → Tag | .source => .target | .target => .source
def swapCell : Cell → Cell
  | .rows t => .rows (swapTag t) | .lower t => .lower (swapTag t)
  | .protocols t => .protocols (swapTag t) | .ticks t => .ticks (swapTag t)
  | .joint t => .joint (swapTag t) | .resources t => .resources (swapTag t)
  | k => k

theorem swap_cell_involution (k : Cell) : swapCell (swapCell k) = k := by
  cases k <;> first | rfl | (rename_i tag; cases tag <;> rfl)
def stagedSourceScope (r : RawPackageCover) (c : Clause) := (r.scopes c).map swapCell

def swapProvenance : ProvenanceOwner → ProvenanceOwner
  | .source => .target | .target => .source | .external => .external | .none => .none
/-- Typed preservation recipe: unchanged factor primitives, translated carrier
ownership/provenance, and translated writer index. No clause verdict is read. -/
def translatedValue : (k : Cell) → Value (swapCell k) → Value k
  | .resources _, v => ⟨swapTag v.owner,v.rechargeAvailable⟩
  | .protocols _, v => ⟨v.edges,(fun p => swapProvenance (v.owner p)),
      (fun p => swapProvenance (v.housing p))⟩
  | .writers, v => fun t r => v (swapTag t) r
  | .rows _, v => v | .lower _, v => v | .ticks _, v => v | .joint _, v => v
  | .positions,v => v | .hazards,v => v | .policy,v => v | .prototypes,v => v
  | .publishedP,v => v | .publishedC,v => v | .publishedU,v => v | .publishedM,v => v
  | .audit,v => v | .channels,v => v | .interface,v => v | .maintenance,v => v
  | .histories,v => v | .eventTable,v => v | .realized,v => v | .receiverInput,v => v
  | .routeTable,v => v

def canonicalStage : RawStageMap := ⟨fun _ k => some ⟨swapCell k,fun v => some (translatedValue k v)⟩⟩

def mappedLocal (source : Assignment) (stage : RawStageMap) (r : RawPackageCover)
    (c : Clause) : Assignment := fun k =>
  if k ∈ r.scopes c then
    (stage.arrows c k).bind (fun arrow => (source arrow.source).bind arrow.operation)
  else none

def MapTotal (source : Assignment) (stage : RawStageMap) (r : RawPackageCover) : Prop :=
  ∀ c k, k ∈ r.scopes c → ∃ arrow, stage.arrows c k = some arrow ∧
    arrow.source = swapCell k ∧ (source arrow.source).isSome = true ∧
    ∀ v, arrow.operation v ≠ none
/-- Target coverage also yields total source-coordinate coverage, using the
checked typed inverse, rather than silently dropping a source quantifier. -/
theorem stage_source_coverage {source : Assignment} {stage : RawStageMap} {r : RawPackageCover}
    (h : MapTotal source stage r) (c : Clause) (s : Cell) (hs : s ∈ stagedSourceScope r c) :
    ∃ t, t ∈ r.scopes c ∧ ∃ arrow, stage.arrows c t = some arrow ∧ arrow.source = s := by
  obtain ⟨t,ht,he⟩ := List.mem_map.mp hs
  obtain ⟨arrow,ha,hsource,_⟩ := h c t ht
  exact ⟨t,ht,arrow,ha,hsource.trans he⟩

/-- Compare actual mapped primitives with the declared typed translation;
this is an equation of raw values, not an acceptance assumption. -/
def ValuePreserving (source : Assignment) (stage : RawStageMap) (r : RawPackageCover) : Prop :=
  ∀ c k, k ∈ r.scopes c →
    mappedLocal source stage r c k = (source (swapCell k)).map (translatedValue k)
def TargetLocalChecks (source : Assignment) (stage : RawStageMap) (r : RawPackageCover)
    (tag : Tag) : Prop := ∀ c, clauseAccept (mappedLocal source stage r c) tag c

def EdgeCompatible (source : Assignment) (stage : RawStageMap) (r : RawPackageCover) : Prop :=
  ∀ i j k, r.adjacent i j → k ∈ r.scopes i → k ∈ r.scopes j →
    mappedLocal source stage r i k = mappedLocal source stage r j k

/-- Dependent-valued gluing, checked through TTH-01's ordinary Sigma-valued
assignment. The chosen index is defined from coverage, not supplied. -/
noncomputable def assembledAssignment (source : Assignment) (stage : RawStageMap)
    (r : RawPackageCover) (tag : Tag) (hc : CoverCheck r tag) : Assignment :=
  fun k => mappedLocal source stage r (Classical.choose (hc.covers k)) k

theorem assembled_restricts (source : Assignment) (stage : RawStageMap)
    (r : RawPackageCover) (tag : Tag) (hc : CoverCheck r tag)
    (he : EdgeCompatible source stage r) (c : Clause) (k : Cell) (hk : k ∈ r.scopes c) :
    assembledAssignment source stage r tag hc k = mappedLocal source stage r c k := by
  let locals : Clause → Cell → Sigma (fun k => Option (Value k)) :=
    fun c k => ⟨k,mappedLocal source stage r c k⟩
  have h := gluedAssignmentAgrees (checkedTree r tag hc) locals
    (fun i j k hij hi hj => congrArg (Sigma.mk k) (he i j k hij hi hj)) c k hk
  change (⟨k,assembledAssignment source stage r tag hc k⟩ : Sigma (fun k => Option (Value k))) =
    ⟨k,mappedLocal source stage r c k⟩ at h
  exact eq_of_heq (Sigma.mk.inj h).2

theorem mapped_local_complete {source : Assignment} {stage : RawStageMap} {r : RawPackageCover}
    (h : MapTotal source stage r) (c : Clause) (k : Cell) (hk : k ∈ r.scopes c) :
    (mappedLocal source stage r c k).isSome = true := by
  obtain ⟨arrow,ha,_,hv,hop⟩ := h c k hk
  simp only [mappedLocal,hk,if_true,ha,Option.bind_some]
  cases hs : source arrow.source with
  | none => rw [hs] at hv; contradiction
  | some v =>
    simp only [Option.bind_some]
    cases he : arrow.operation v with
    | none => exact False.elim (hop v he)
    | some w => rfl

theorem assembled_complete {source : Assignment} {stage : RawStageMap} {r : RawPackageCover}
    {tag : Tag} (hc : CoverCheck r tag) (hm : MapTotal source stage r)
    (he : EdgeCompatible source stage r) (k : Cell) :
    (assembledAssignment source stage r tag hc k).isSome = true := by
  obtain ⟨c,hk⟩ := hc.covers k
  rw [assembled_restricts source stage r tag hc he c k hk]
  exact mapped_local_complete hm c k hk

structure AssembledPackage (source : Assignment) (stage : RawStageMap) (r : RawPackageCover)
    (tag : Tag) (hc : CoverCheck r tag) : Prop where
  restrictions : ∀ c k, k ∈ r.scopes c →
    assembledAssignment source stage r tag hc k = mappedLocal source stage r c k
  complete : ∀ k, (assembledAssignment source stage r tag hc k).isSome = true
  accepted : AssignedPackagePass (assembledAssignment source stage r tag hc) tag
  gates : ∀ c, clauseGate (assembledAssignment source stage r tag hc) tag c
  mapped : ValuePreserving source stage r
  total : MapTotal source stage r

/-- Faithful TTH-02 on the assignment substrate: all verdicts are computed
by clause rules on defined mapped/glued assignments. Source package content
is checked independently. No lineage/autonomy or free accepted predicate. -/
theorem stagedHeterogeneousPackageAssembly_generic
    (source : Assignment) (stage : RawStageMap) (cover : RawPackageCover)
    (targetTag : Tag) (hc : CoverCheck cover targetTag)
    (_hsource : AssignedPackagePass source (swapTag targetTag))
    (hmap : MapTotal source stage cover) (hvalues : ValuePreserving source stage cover)
    (htarget : TargetLocalChecks source stage cover targetTag)
    (hcompat : EdgeCompatible source stage cover) :
    AssembledPackage source stage cover targetTag hc := by
  have hr := assembled_restricts source stage cover targetTag hc hcompat
  have ha : AssignedPackagePass (assembledAssignment source stage cover targetTag hc) targetTag := by
    intro c
    apply (clause_accept_locality targetTag c (fun k hk => hr c k (hc.dependencies c k hk))).mpr
    exact htarget c
  exact ⟨hr,assembled_complete hc hmap hcompat,ha,fun c => clause_accept_implies_gate c (ha c),hvalues,hmap⟩

/-- Explicit package readout of the defined global; no local verdict is merely
stored under a global label. The clauses actually evaluate on this assignment. -/
theorem assembled_global_package {source : Assignment} {stage : RawStageMap}
    {r : RawPackageCover} {tag : Tag} {hc : CoverCheck r tag}
    (h : AssembledPackage source stage r tag hc) :
    ∃ global : Assignment,
      (∀ c k, k ∈ r.scopes c → global k = mappedLocal source stage r c k) ∧
      AssignedPackagePass global tag ∧ (∀ c, clauseGate global tag c) :=
  ⟨assembledAssignment source stage r tag hc,h.restrictions,h.accepted,h.gates⟩

end CSTTT.POS04.Assigned
