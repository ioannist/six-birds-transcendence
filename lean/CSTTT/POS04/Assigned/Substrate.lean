import CSTTT.POS04.Assembly

/-! G2a: typed, immutable primitive assignments. Tables are cells (not verdicts).
Global JSON references have one global cell identity; tag-specific action tables
have one identity per tag, shared by every clause. The 160 Data coordinates are
views, not duplicate stores. Clause scopes below close the old primitive-reference
lists under the actual dependencies of their assigned evaluators.
C6 evaluation is reserved for the remaining G2b-2 work; assigned C8 is defined
in Assigned/C8.lean.
Source: frozen POS-04 JSON, imported and checked in Data/Export/WellFormed. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit

structure AuditParameters where
  tau : Nat
  epsilon : Rat
  retention : Rat
  deriving DecidableEq

structure ProtocolData where
  edges : ProtocolId → List ProtocolEdge
  owner : ProtocolId → ProvenanceOwner
  housing : ProtocolId → ProvenanceOwner

structure JointData where
  left : Fin 2 → HistoryId
  right : Fin 2 → HistoryId
  coupling : AssemblageId → List (Fin 2 × Fin 2)
  reassembly : AssemblageId → AssemblageId
  observables : List JointObservable

structure ResourceData where
  owner : Tag
  rechargeAvailable : Bool

inductive Cell where
  | rows (tag : Tag) | lower (tag : Tag)
  | positions | hazards | policy | prototypes | publishedP | publishedC
  | publishedU | publishedM | audit
  | channels | protocols (tag : Tag) | ticks (tag : Tag) | interface
  | joint (tag : Tag) | resources (tag : Tag) | maintenance
  | histories | eventTable | realized | receiverInput | routeTable | writers
  deriving DecidableEq

def Value : Cell → Type
  | .rows _ => KState → Action → List (Ambient × Nat)
  | .lower _ => LowerRule
  | .positions => KState → Nat
  | .hazards => Ambient → Bool
  | .policy => KState → Action
  | .prototypes => List KState
  | .publishedP => I → I → Nat
  | .publishedC => I → J → Nat
  | .publishedU => J → I → Nat
  | .publishedM => KState → Nat
  | .audit => AuditParameters
  | .channels => List CurrentChannel
  | .protocols _ => ProtocolData
  | .ticks _ => KState → Action → Nat
  | .interface => List FutureObservable
  | .joint _ => JointData
  | .resources _ => ResourceData
  | .maintenance => Ledger
  | .histories => HistoryId → List KState
  | .eventTable => List Event
  | .realized => List Stage
  | .receiverInput => Receiver
  | .routeTable => List Route
  | .writers => Tag → RouteId → Bool

abbrev Assignment := (k : Cell) → Option (Value k)

/-- Immutable replacement of one typed primitive cell. -/
def put (a : Assignment) (k : Cell) (v : Option (Value k)) : Assignment :=
  fun j => if h : j = k then h.symm ▸ v else a j

@[simp] theorem put_same (a : Assignment) (k : Cell) (v : Option (Value k)) :
    put a k v k = v := by simp [put]
@[simp] theorem put_other (a : Assignment) (k j : Cell)
    (v : Option (Value k)) (h : j ≠ k) : put a k v j = a j := by simp [put,h]

/-- The decoder itself enforces scope; missing and out-of-scope reads stay absent. -/
def decode (scope : List Cell) (a : Assignment) : Assignment :=
  fun k => if k ∈ scope then a k else none

def Agrees (scope : List Cell) (a b : Assignment) : Prop :=
  ∀ k ∈ scope, a k = b k

theorem decoder_locality {scope : List Cell} {a b : Assignment}
    (h : Agrees scope a b) : decode scope a = decode scope b := by
  funext k
  by_cases hk : k ∈ scope
  · simp [decode,hk,h k hk]
  · simp [decode,hk]

theorem decoder_outside (scope : List Cell) (a : Assignment) (k : Cell)
    (h : k ∉ scope) : decode scope a k = none := by simp [decode,h]

def Complete (scope : List Cell) (a : Assignment) : Prop :=
  ∀ k ∈ scope, (a k).isSome = true

def commonScope (tag : Tag) : List Cell :=
  [.rows tag,.positions,.hazards]
def clauseScope (tag : Tag) : Clause → List Cell
  | .c1 => commonScope tag ++ [.policy,.prototypes,.publishedP,.publishedC,
      .publishedU,.audit]
  | .c2 => commonScope tag ++ [.lower tag,.publishedM]
  | .c3 => commonScope tag ++ [.lower tag,.publishedM]
  | .c4 => commonScope tag ++ [.channels,.policy,.histories,.publishedM]
  | .c5 => [.protocols tag,.rows tag,.policy,.histories]
  | .c6 => commonScope tag ++ [.ticks tag,.interface,.resources tag,.maintenance,
      .policy,.publishedP,.publishedM,.histories,.eventTable,.realized,
      .receiverInput,.routeTable,.writers]
  | .c7 => [.joint tag,.rows tag,.policy,.histories,.publishedP,
      .eventTable,.realized,.receiverInput]
  | .c8 => [.rows tag,.policy,.resources tag,.maintenance]

def viewScope (x : Coordinate) : List Cell := clauseScope x.tag x.clause

theorem views_share_cells (tag : Tag) (s t : KState) (c : Clause) :
    viewScope ⟨tag,s,c⟩ = viewScope ⟨tag,t,c⟩ := rfl

theorem shared_rows (tag : Tag) :
    Cell.rows tag ∈ clauseScope tag .c1 ∧
    Cell.rows tag ∈ clauseScope tag .c2 ∧
    Cell.rows tag ∈ clauseScope tag .c3 := by simp [clauseScope,commonScope]

theorem global_P_shared :
    Cell.publishedP ∈ clauseScope .source .c1 ∧
    Cell.publishedP ∈ clauseScope .target .c1 := by decide

/-- Canonical raw values, never acceptance flags. All constants resolve to
already transcribed Data tables or their computed raw rule. -/
def canonicalValue : (k : Cell) → Value k
  | .rows tag => actionRow tag
  | .lower tag => positiveLowerRule tag
  | .positions => publicPosition
  | .hazards => isLethalHazard
  | .policy => canonicalAction
  | .prototypes => c1ColumnRepresentatives
  | .publishedP => pNum
  | .publishedC => cIndicator
  | .publishedU => uPrototypeNum
  | .publishedM => fun s => mClass (index s)
  | .audit => ⟨c1Tau,c1Epsilon,c1RetentionThreshold⟩
  | .channels => currentChannels
  | .protocols tag => ⟨protocolEdges,protocolOwner tag,protocolHousing tag⟩
  | .ticks tag => tickIncrement tag
  | .interface => futureInterface
  | .joint tag => ⟨leftBranch,rightBranch,coupling,reassembly tag,jointObservables tag⟩
  | .resources tag => ⟨resourceOwner tag,rechargeAvailableAfterWithdrawal tag⟩
  | .maintenance => ledger
  | .histories => sourceHistory
  | .eventTable => events
  | .realized => realizedStages
  | .receiverInput => receiver
  | .routeTable => routes
  | .writers => recordWriterAvailable

def canonical : Assignment := fun k => some (canonicalValue k)

theorem canonical_complete (scope : List Cell) : Complete scope canonical := by
  intro k _
  rfl

theorem missing_cell_rejected (scope : List Cell) (a : Assignment) (k : Cell)
    (hk : k ∈ scope) : ¬ Complete scope (put a k none) := by
  intro h
  have := h k hk
  simp at this

/-- A scope that drops a required read cannot decode that read, even when the
unrestricted assignment contains it. -/
theorem dropped_scope_read (scope : List Cell) (k : Cell) (hk : k ∉ scope) :
    decode scope canonical k = none ∧ canonical k ≠ none := by
  exact ⟨decoder_outside scope canonical k hk, by simp [canonical]⟩

/-- Every original JSON primitive pointer resolves to this one namespace.
Additional scope entries above are transitive algorithm dependencies. -/
def resolveRef (tag : Tag) : PrimitiveRef → Cell
  | .actionDistributions => .rows tag
  | .publishedP => .publishedP
  | .publishedC => .publishedC
  | .publishedU => .publishedU
  | .publicChannelRule => .lower tag
  | .publishedMClasses => .publishedM
  | .currentChannels => .channels
  | .protocols => .protocols tag
  | .tickIncrement => .ticks tag
  | .futureInterface => .interface
  | .assemblages => .joint tag
  | .resources => .resources tag
  | .maintenance => .maintenance

theorem view_references_resolve (x : Coordinate) :
    ∀ ref ∈ primitiveRefs x.tag x.clause, resolveRef x.tag ref ∈ viewScope x := by
  rcases x with ⟨tag,s,c⟩
  change ∀ ref ∈ primitiveRefs tag c, resolveRef tag ref ∈ clauseScope tag c
  cases tag <;> cases c <;> decide

theorem views_160 : coordinates.length = 160 ∧ coordinates.Nodup ∧
    (∀ tag : Tag, ∀ s : KState, ∀ c : Clause, ⟨tag,s,c⟩ ∈ coordinates) :=
  ⟨coordinates_count,coordinates_distinct,clause_coordinates_complete⟩

theorem shared_reference_identity (tag : Tag) :
    resolveRef tag .actionDistributions = Cell.rows tag ∧
    resolveRef .source .publishedP = resolveRef .target .publishedP ∧
    resolveRef .source .publishedC = resolveRef .target .publishedC ∧
    resolveRef .source .publishedU = resolveRef .target .publishedU ∧
    resolveRef .source .publishedMClasses = resolveRef .target .publishedMClasses :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

end CSTTT.POS04.Assigned
