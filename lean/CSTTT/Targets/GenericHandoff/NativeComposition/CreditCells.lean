import CSTTT.Targets.GenericHandoff.NativeComposition.PackageBundle

/-! Computed three-role C5 credit shares actual native safe rows and supported
histories. Local ownership/housing instructions read the actual resource owner;
their transport follows the actual native publication operation. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeCreditCells
open RegisterInterpreter NativePackagePrimitives NativePackageBundle

def protocols : List Protocol := [.selfCycle,.externalCycle,.null]
def vertices : List Vertex := [0,1,2]
def anchor (v : Vertex) : Factor :=
  if v.val=0 then (false,false,false) else if v.val=1 then (false,false,true) else (false,true,false)
def expected : Protocol → ProtocolCreditRules.Credit
  | .selfCycle => .self | .externalCycle => .other | .null => .none
def schema (owner : Owner) : ProtocolCreditRules.Schema Factor Bool Factor Vertex Bool Protocol Factor CreditOwner Edge :=
  ⟨factors,[false,true],factors,vertices,protocols,vertices,Prod.fst,(fun e => e.2.1),(fun e => e.2.2),
    false,true,some,1,anchor,.inl owner,.inr (),expected⟩
def data (b : Bundle) : ProtocolCreditRules.Raw Factor Bool Factor Protocol Factor CreditOwner Edge :=
  ⟨creditTables b.native b.supplement,b.native.temporal.rows,b.native.temporal.policy,b.native.temporal.histories⟩
def bindings (cell : Owner) (copy : Bool) : ProtocolCreditRules.Bindings Owner NativePackageBundle.Value
    Factor Bool Factor Protocol Factor CreditOwner Edge :=
  let get := NativePackageBundle.select copy
  ⟨⟨cell,fun p => creditTables (get p).native (get p).supplement⟩,
    ⟨cell,fun p => (get p).native.temporal.rows⟩,
    ⟨cell,fun p => (get p).native.temporal.policy⟩,
    ⟨cell,fun p => (get p).native.temporal.histories⟩⟩
def canonicalData (cell : Owner) (copy : Bool) :=
  data ⟨AvailabilityPublication.selected cell copy,supplement⟩

theorem decoded (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    ProtocolCreditRules.decoded (bindings cell copy) a=(a cell).map (fun p => data (select copy p)) := by
  cases ha : a cell <;> simp [ProtocolCreditRules.decoded,bindings,CellView.read,ha,data]
theorem acceptance_iff (owner cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    ProtocolCreditRules.AssignedAccept (schema owner) (bindings cell copy) a ↔
      ∃ p, a cell=some p ∧ ProtocolCreditRules.Accept (schema owner) (data (select copy p)) := by
  simp only [ProtocolCreditRules.AssignedAccept,decoded]
  cases a cell <;> simp
theorem missing_rejected (owner cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value)
    (hm : a cell=none) : ¬ ProtocolCreditRules.AssignedAccept (schema owner) (bindings cell copy) a := by
  rw [acceptance_iff]
  simp [hm]
theorem publication_source_decoded (a : Assignment Owner NativePackageBundle.Value) (o : Owner) :
    ProtocolCreditRules.decoded (bindings (swapOwner o) true) (NativePackageBundle.image a)=
      ProtocolCreditRules.decoded (bindings o false) a := by
  rw [decoded,decoded]
  have h := congrArg (fun z : Option Bundle => z.map data) (copied_source a o)
  simpa [Option.map_map] using h
theorem publication_source_accept_iff (owner : Owner) (a : Assignment Owner NativePackageBundle.Value) (o : Owner) :
    ProtocolCreditRules.AssignedAccept (schema owner) (bindings (swapOwner o) true) (NativePackageBundle.image a) ↔
      ProtocolCreditRules.AssignedAccept (schema owner) (bindings o false) a := by
  simp only [ProtocolCreditRules.AssignedAccept,publication_source_decoded]

theorem domain (owner : Owner) : ProtocolCreditRules.DomainCheck (schema owner) := by
  change factors.Nodup ∧ (∀ s : Factor,s∈factors) ∧ ([false,true] : List Bool).Nodup ∧
    (∀ a : Bool,a∈[false,true]) ∧ factors.Nodup ∧ (∀ o : Factor,o∈factors) ∧ vertices.Nodup ∧
    (∀ v : Vertex,v∈vertices) ∧ protocols.Nodup ∧ (∀ id : Protocol,id∈protocols)
  refine ⟨by decide +kernel,factor_mem,by decide +kernel,?_,by decide +kernel,factor_mem,
    by decide +kernel,by decide +kernel,by decide +kernel,?_⟩
  · intro a; cases a <;> decide +kernel
  · intro id; cases id <;> decide +kernel
theorem credit_coverage (owner : Owner) : ProtocolCreditRules.CreditCoverage (schema owner) := by
  change ∀ c ∈ [ProtocolCreditRules.Credit.self,.other,.none], ∃ id ∈ protocols, expected id=c
  intro c hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ⟨.selfCycle,by decide +kernel,rfl⟩
  · exact ⟨.externalCycle,by decide +kernel,rfl⟩
  · exact ⟨.null,by decide +kernel,rfl⟩
theorem gate (cell : Owner) (copy : Bool) :
    ProtocolCreditRules.Gate (schema (AvailabilityPublication.dataOwner cell copy)) (canonicalData cell copy) := by
  refine ⟨domain _,credit_coverage _,?_,?_,?_⟩
  · change vertices.length≥2; decide +kernel
  · change (false : Bool)≠true; decide +kernel
  · cases cell <;> cases copy <;> simp only [ProtocolCreditRules.RowsValid] <;> decide +kernel
theorem rule (cell : Owner) (copy : Bool) :
    ProtocolCreditRules.Rule (schema (AvailabilityPublication.dataOwner cell copy)) (canonicalData cell copy) := by
  cases cell <;> cases copy
  all_goals refine ⟨?_,?_,?_⟩
  all_goals first
    | (intro id hi; cases id <;> decide +kernel)
    | (decide +kernel)
theorem canonical_decoded (cell : Owner) (copy : Bool) :
    ProtocolCreditRules.decoded (bindings cell copy) NativePackageBundle.canonical=some (canonicalData cell copy) := by
  cases cell <;> cases copy <;> rfl
theorem c5 (cell : Owner) (copy : Bool) :
    ProtocolCreditRules.AssignedAccept (schema (AvailabilityPublication.dataOwner cell copy))
      (bindings cell copy) NativePackageBundle.canonical :=
  ⟨_,canonical_decoded cell copy,gate cell copy,rule cell copy⟩

def cutSelfEdges (b : Bundle) : Bundle :=
  {b with supplement := {b.supplement with credit :=
    {b.supplement.credit with edges := fun id =>
      if id=.selfCycle then [] else b.supplement.credit.edges id}}}
theorem cut_actual_credit (owner : Owner) (b : Bundle) :
    ProtocolCreditRules.credit (schema owner) (data (cutSelfEdges b)) .selfCycle=.none := by
  apply ProtocolCreditRules.empty_edges_credit
  simp [data,cutSelfEdges,creditTables]
theorem cut_actual_c5_rejected (owner : Owner) (b : Bundle) :
    ¬ ProtocolCreditRules.Accept (schema owner) (data (cutSelfEdges b)) := by
  apply ProtocolCreditRules.wrong_credit_rejected _ _ .selfCycle
  · change Protocol.selfCycle ∈ protocols
    decide +kernel
  · rw [cut_actual_credit]
    change ProtocolCreditRules.Credit.none≠.self
    decide +kernel

def externalizeOwner (b : Bundle) : Bundle :=
  {b with supplement := {b.supplement with credit :=
    {b.supplement.credit with owner := fun id =>
      if id=.selfCycle then .external else b.supplement.credit.owner id}}}
theorem externalized_actual_credit (cell : Owner) (copy : Bool) :
    ProtocolCreditRules.credit (schema (AvailabilityPublication.dataOwner cell copy))
      (data (externalizeOwner ⟨AvailabilityPublication.selected cell copy,supplement⟩)) .selfCycle=.self := by
  cases cell <;> cases copy <;> rfl
theorem externalized_owner_readout (b : Bundle) :
    (data (externalizeOwner b)).tables.owner .selfCycle=.inr () := rfl
theorem externalized_actual_c5_rejected (cell : Owner) (copy : Bool) :
    ¬ ProtocolCreditRules.Accept (schema (AvailabilityPublication.dataOwner cell copy))
      (data (externalizeOwner ⟨AvailabilityPublication.selected cell copy,supplement⟩)) := by
  apply ProtocolCreditRules.wrong_self_owner_rejected _ _ .selfCycle
  · change Protocol.selfCycle ∈ protocols; decide +kernel
  · exact externalized_actual_credit cell copy
  · rw [externalized_owner_readout]
    intro he
    cases he

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeCreditCells
