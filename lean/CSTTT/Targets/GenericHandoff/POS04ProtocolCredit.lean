import CSTTT.Targets.GenericHandoff.ProtocolCreditRules
import CSTTT.Targets.GenericHandoff.POS04ObjecthoodProtocol
import CSTTT.POS04.Assigned.C457Guards

/-! POS-04 specialization of the generic protocol-credit surrogate.
The equivalence is for arbitrary partial assignments, not only canonical data.
Housing is raw provenance transported separately; it is not used to infer credit. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ProtocolCredit
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

abbrev PRaw := ProtocolCreditRules.Raw KState Action Ambient ProtocolId HistoryId
  ProvenanceOwner ProtocolEdge
abbrev PSchema := ProtocolCreditRules.Schema KState Action Ambient Vertex Channel
  ProtocolId HistoryId ProvenanceOwner ProtocolEdge

def schema (tag : Tag) : PSchema :=
  ⟨kernel,actions,ambientStates,vertices,protocolIds,[.u,.v,.w],
    ProtocolEdge.fromVertex,ProtocolEdge.toVertex,ProtocolEdge.channel,.self,.other,
    (fun o => match o with | .inK s => some s | _ => none),4,historyAnchor,
    (if tag = .source then .source else .target),.external,
    (fun id => match id with | .clockwise => .self | .scheduled => .other | _ => .none)⟩

def raw (d : ExtraInputs) : PRaw :=
  ⟨⟨d.protocols.edges,d.protocols.owner,d.protocols.housing⟩,
    d.base.rows,d.base.policy,d.histories⟩

def creditImage : C5Credit → ProtocolCreditRules.Credit
  | .self => .self | .other => .other | .none => .none | .ambiguous => .ambiguous

@[simp] theorem credit_image_iff (a b : C5Credit) : creditImage a = creditImage b ↔ a = b := by
  cases a <;> cases b <;> simp [creditImage]

theorem count_eq (d : ExtraInputs) (tag : Tag) (id : ProtocolId) (a b : Vertex) (ch : Channel) :
    ProtocolCreditRules.count (schema tag) (raw d) id a b ch = count5 d id a b ch := rfl

theorem forward_eq (d : ExtraInputs) (tag : Tag) (id : ProtocolId) (ch : Channel) :
    ProtocolCreditRules.forward (schema tag) (raw d) id ch = forward5 d id ch := by
  change ProtocolCreditRules.count (schema tag) (raw d) id .u .v ch *
    (ProtocolCreditRules.count (schema tag) (raw d) id .v .w ch *
      (ProtocolCreditRules.count (schema tag) (raw d) id .w .u ch * 1)) = _
  rw [count_eq,count_eq,count_eq]
  simp only [forward5,Nat.mul_one,Nat.mul_assoc]

theorem reverse_eq (d : ExtraInputs) (tag : Tag) (id : ProtocolId) (ch : Channel) :
    ProtocolCreditRules.reverse (schema tag) (raw d) id ch = reverse5 d id ch := by
  change ProtocolCreditRules.count (schema tag) (raw d) id .v .u ch *
    (ProtocolCreditRules.count (schema tag) (raw d) id .w .v ch *
      (ProtocolCreditRules.count (schema tag) (raw d) id .u .w ch * 1)) = _
  rw [count_eq,count_eq,count_eq]
  simp only [reverse5,Nat.mul_one,Nat.mul_assoc]

theorem credit_eq (d : ExtraInputs) (tag : Tag) (id : ProtocolId) :
    ProtocolCreditRules.credit (schema tag) (raw d) id = creditImage (credit5 d id) := by
  unfold ProtocolCreditRules.credit
  rw [forward_eq,reverse_eq,forward_eq,reverse_eq]
  simp only [schema,credit5]
  split <;> simp_all [creditImage]
  split <;> simp_all
  split <;> simp_all

theorem weight_eq (d : ExtraInputs) (tag : Tag) (s t : KState) :
    ProtocolCreditRules.weight (schema tag) (raw d) s t =
      rowWeight (d.base.rows s (d.base.policy s)) t := by
  rw [POS04ObjecthoodQuotient.rowWeight_sum]
  unfold ProtocolCreditRules.weight
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  cases e.1 <;> simp [schema]

theorem supported_eq (d : ExtraInputs) (tag : Tag) (h : HistoryId) :
    ProtocolCreditRules.supported (schema tag) (raw d) h = historySupported d h := by
  have hw : (fun e : KState × KState => decide
      (ProtocolCreditRules.weight (schema tag) (raw d) e.1 e.2 > 0)) =
    fun e => decide (rowWeight (d.base.rows e.1 (d.base.policy e.1)) e.2 > 0) := by
    funext e
    rw [weight_eq]
  unfold ProtocolCreditRules.supported historySupported pathSupported
  change (! (d.histories h).isEmpty &&
    ((d.histories h).zip ((d.histories h).drop 1)).all _) = _
  rw [hw]

theorem rule_iff (d : ExtraInputs) (tag : Tag) :
    ProtocolCreditRules.Rule (schema tag) (raw d) ↔ C5Rule d tag := by
  let expected : ProtocolId → C5Credit := fun id => match id with
    | .clockwise => .self | .scheduled => .other | _ => .none
  have hex : ∀ id, (schema tag).expected id = creditImage (expected id) := by
    intro id; cases id <;> rfl
  have hc : ∀ id, ProtocolCreditRules.credit (schema tag) (raw d) id =
    creditImage (credit5 d id) := credit_eq d tag
  change ((∀ id ∈ protocolIds, ProtocolCreditRules.credit (schema tag) (raw d) id =
      (schema tag).expected id) ∧
    (∀ id ∈ protocolIds,
      (ProtocolCreditRules.credit (schema tag) (raw d) id = creditImage .self →
        d.protocols.owner id = if tag = .source then .source else .target) ∧
      (ProtocolCreditRules.credit (schema tag) (raw d) id = creditImage .other →
        d.protocols.owner id = .external)) ∧
    (∀ vertex ∈ vertices, ProtocolCreditRules.supported (schema tag) (raw d)
      (historyAnchor vertex) = true)) ↔ _
  simp only [hc,hex,credit_image_iff,supported_eq]
  unfold C5Rule Owner5 Anchors5
  have haudit : (∀ id ∈ protocolIds, credit5 d id = expected id) ↔
      credit5 d .clockwise = .self ∧ credit5 d .scheduled = .other ∧
      credit5 d .internalized = .none ∧ credit5 d .null = .none := by
    simp [protocolIds,expected]
  rw [haudit]
  grind

theorem rows_iff (d : ExtraInputs) (tag : Tag) :
    ProtocolCreditRules.RowsValid (schema tag) (raw d) ↔ RowsValid d.base := Iff.rfl

theorem domain_checked (tag : Tag) : ProtocolCreditRules.DomainCheck (schema tag) := by
  unfold ProtocolCreditRules.DomainCheck
  simp only [schema]
  refine ⟨by decide,(by intro s; cases s <;> decide),by decide,
    (by intro a; cases a <;> decide),by decide,?_,by decide,
    (by intro vertex; cases vertex <;> decide),by decide,(by intro id; cases id <;> decide)⟩
  intro o
  cases o with
  | inK s => cases s <;> decide
  | p2w0 => decide
  | p5w1 => decide

theorem gate_iff (d : ExtraInputs) (tag : Tag) :
    ProtocolCreditRules.Gate (schema tag) (raw d) ↔ RowsValid d.base := by
  unfold ProtocolCreditRules.Gate
  rw [rows_iff]
  have hcover : ProtocolCreditRules.CreditCoverage (schema tag) := by
    intro c hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with h | h | h <;> subst c
    · exact ⟨.clockwise,(by change ProtocolId.clockwise ∈ protocolIds; decide),rfl⟩
    · exact ⟨.scheduled,(by change ProtocolId.scheduled ∈ protocolIds; decide),rfl⟩
    · exact ⟨.null,(by change ProtocolId.null ∈ protocolIds; decide),rfl⟩
  have hcycle : (schema tag).cycle.length ≥ 2 := by change [Vertex.u,.v,.w].length ≥ 2; decide
  have hch : (schema tag).selfChannel ≠ (schema tag).otherChannel := by change Channel.self ≠ .other; decide
  simp only [domain_checked,hcover,hcycle,true_and]
  exact and_iff_right hch

def bindings (tag : Tag) : ProtocolCreditRules.Bindings Cell Value KState Action Ambient
    ProtocolId HistoryId ProvenanceOwner ProtocolEdge :=
  ⟨⟨.protocols tag,fun p => ⟨p.edges,p.owner,p.housing⟩⟩,
    ⟨.rows tag,id⟩,⟨.policy,id⟩,⟨.histories,id⟩⟩

theorem scope_eq (tag : Tag) : (bindings tag).scope = clauseScope tag .c5 := rfl

open Classical in
theorem decoded_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ProtocolCreditRules.decoded (bindings tag) a =
      if CSTTT.POS04.Assigned.Complete (clauseScope tag .c5) a then
        some (raw (extraInputs a tag)) else none := by
  cases ht : a (.protocols tag) <;> cases hr : a (.rows tag) <;>
    cases hp : a .policy <;> cases hh : a .histories <;>
    simp [ProtocolCreditRules.decoded,bindings,CellView.read,raw,extraInputs,inputs,
      CSTTT.POS04.Assigned.Complete,clauseScope,ht,hr,hp,hh]

theorem raw_scoped (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    raw (extraInputs a tag) = raw (clauseExtra a tag .c5) := by cases tag <;> rfl

theorem generic_c5_gate_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ProtocolCreditRules.AssignedGate (schema tag) (bindings tag) a ↔ C5Gate a tag := by
  unfold ProtocolCreditRules.AssignedGate C5Gate Ready
  rw [decoded_eq,raw_scoped]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c5) a <;>
    simp [h,gate_iff,clauseExtra,extraInputs,clauseInputs]

theorem generic_c5_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag) a ↔ C5Accept a tag := by
  unfold ProtocolCreditRules.AssignedAccept C5Accept C5Gate Ready
  rw [decoded_eq,raw_scoped]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c5) a <;>
    simp [h,ProtocolCreditRules.Accept,gate_iff,rule_iff,clauseExtra,extraInputs,clauseInputs]

def Transport (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  ProtocolCreditRules.AssignedGate (schema .source) (bindings .source) a ∧
  ProtocolCreditRules.AssignedGate (schema .target) (bindings .target) a ∧
  ProtocolCreditRules.Transport (raw (clauseExtra a .source .c5)).tables
    (raw (clauseExtra a .target .c5)).tables protocolIds id id c5TranslateOwner

theorem generic_transport_iff (a : CSTTT.POS04.Assigned.Assignment) :
    Transport a ↔ C5Transport a := by
  simp only [Transport,generic_c5_gate_iff,ProtocolCreditRules.Transport,raw,
    C5Transport,List.map_id]
  rfl

theorem canonical_accept (tag : Tag) :
    ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag) canonical :=
  (generic_c5_iff _ _).mpr (canonical_c457 tag).2.1

theorem canonical_transport : Transport canonical :=
  (generic_transport_iff _).mpr canonical_staged57.1

theorem controls_equivalence (v : C5Variant) (tag : Tag) :
    ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag) (controls5 v) ↔
      C5Surrogate v tag := (generic_c5_iff _ _).trans (c5_controls_equivalence v tag)

theorem external_control :
    ProtocolCreditRules.AssignedAccept (schema .source) (bindings .source) (external5 canonical) ∧
    ¬ ProtocolCreditRules.AssignedAccept (schema .target) (bindings .target) (external5 canonical) :=
  ⟨(generic_c5_iff _ _).mpr neg_c5_external_outcomes.1,
    fun h => neg_c5_external_outcomes.2.1 ((generic_c5_iff _ _).mp h)⟩

theorem internalized_control :
    (∀ tag, ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag) (internalized5 canonical)) ∧
    ¬ Transport (internalized5 canonical) :=
  ⟨fun tag => (generic_c5_iff _ _).mpr (by
      cases tag
      · exact neg_c5_internalized_outcomes.1
      · exact neg_c5_internalized_outcomes.2.1),
    fun h => neg_c5_internalized_outcomes.2.2.1 ((generic_transport_iff _).mp h)⟩

theorem edges_guard (tag : Tag) :
    ¬ ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag) (noGenerators canonical tag) :=
  fun h => c5_edges_guard tag ((generic_c5_iff _ _).mp h)

theorem owners_guard (tag : Tag) :
    ¬ ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag) (noGeneratorOwner canonical tag) :=
  fun h => c5_owner_guard tag ((generic_c5_iff _ _).mp h)

theorem histories_guard (tag : Tag) :
    ¬ ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag) (emptyHistories canonical) :=
  fun h => c5_histories_guard tag ((generic_c5_iff _ _).mp h)

theorem housing_guard : ¬ Transport (noTargetHousing canonical) :=
  fun h => c5_housing_guard ((generic_transport_iff _).mp h)

theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c5) :
    ¬ ProtocolCreditRules.AssignedGate (schema tag) (bindings tag)
        (CSTTT.POS04.Assigned.put a k none) ∧
    ¬ ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag)
        (CSTTT.POS04.Assigned.put a k none) := by
  apply ProtocolCreditRules.missing_rejected _ _ _ k
  · simpa only [scope_eq] using hk
  · simp

theorem rows_guard (tag : Tag) :
    ¬ ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag) (noRows canonical tag) := by
  intro h
  rcases ((generic_c5_iff _ _).mp h).2 with ⟨_,_,_,_,_,ha⟩
  have he := ha .u (by decide)
  have hn : historySupported (clauseExtra (noRows canonical tag) tag .c5) .repA = false := by
    cases tag <;> decide +kernel
  change historySupported (clauseExtra (noRows canonical tag) tag .c5) .repA = true at he
  rw [hn] at he
  contradiction

theorem policy_guard (tag : Tag) :
    ¬ ProtocolCreditRules.AssignedAccept (schema tag) (bindings tag) (stayPolicy canonical) := by
  intro h
  rcases ((generic_c5_iff _ _).mp h).2 with ⟨_,_,_,_,_,ha⟩
  have he := ha .u (by decide)
  have hn : historySupported (clauseExtra (stayPolicy canonical) tag .c5) .repA = false := by
    cases tag <;> decide +kernel
  change historySupported (clauseExtra (stayPolicy canonical) tag .c5) .repA = true at he
  rw [hn] at he
  contradiction

theorem edge_from_guard (tag : Tag) :
    ¬ ProtocolCreditRules.Accept {schema tag with edgeFrom := fun _ => .u}
      (raw (canonicalExtra tag)) := by
  apply ProtocolCreditRules.wrong_credit_rejected _ _ .clockwise
  · change ProtocolId.clockwise ∈ protocolIds; decide
  · cases tag <;> decide +kernel

theorem edge_to_guard (tag : Tag) :
    ¬ ProtocolCreditRules.Accept {schema tag with edgeTo := fun _ => .u}
      (raw (canonicalExtra tag)) := by
  apply ProtocolCreditRules.wrong_credit_rejected _ _ .clockwise
  · change ProtocolId.clockwise ∈ protocolIds; decide
  · cases tag <;> decide +kernel

theorem edge_channel_guard (tag : Tag) :
    ¬ ProtocolCreditRules.Accept {schema tag with edgeChannel := fun _ => .self}
      (raw (canonicalExtra tag)) := by
  apply ProtocolCreditRules.wrong_credit_rejected _ _ .scheduled
  · change ProtocolId.scheduled ∈ protocolIds; decide
  · cases tag <;> decide +kernel

end CSTTT.TargetTheory.GenericHandoff.POS04ProtocolCredit
