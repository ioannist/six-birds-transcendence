import CSTTT.POS04.C2C3

/-! The C4 and C5 surrogate ceilings follow frozen
`audit/M3_model_spec.md:20-21,34`. No full HIDD or T5 claim is made. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

inductive C4Variant where | positive | negExpose | brokenConnector
  deriving DecidableEq, Repr

def c4Channels (v : C4Variant) : List CurrentChannel :=
  if v = .negExpose then currentChannels ++ [expandedChannel] else currentChannels

def c4Availability (tag : Tag) (s : KState) : List Action :=
  actions.filter fun a => !(actionRow tag s a).isEmpty

def c4Channel (tag : Tag) (c : CurrentChannel) (s : KState) :
    (Nat × List Action) × Option (Nat × List (List Bool)) :=
  match c with
  | .publicPosition => ((publicPosition s, []), none)
  | .deadlineAvailability => ((0, c4Availability tag s), none)
  | .canonicalM => ((0, []), some (rawM tag s))

def c4Current (v : C4Variant) (tag : Tag) (s : KState) :
    List ((Nat × List Action) × Option (Nat × List (List Bool))) :=
  (c4Channels v).map fun c => c4Channel tag c s

def c4ConnectorWeight (v : C4Variant) (tag : Tag)
    (s t : KState) : Nat :=
  if v = .brokenConnector && s = .p1w0 && t = .p2w1 then 0
  else rowWeight (actionRow tag s (canonicalAction s)) t

def C4Collision (v : C4Variant) (tag : Tag) : Prop :=
  c4Current v tag hiddenPair.1 = c4Current v tag hiddenPair.2 ∧
  rawM tag hiddenPair.1 ≠ rawM tag hiddenPair.2

def C4Connector (v : C4Variant) (tag : Tag) : Prop :=
  ((connectorHistory.zip (connectorHistory.drop 1)).all fun pair =>
    decide (c4ConnectorWeight v tag pair.1 pair.2 > 0)) = true ∧
  c4Current v tag .p1w0 = c4Current v tag .p1w1 ∧
  rawM tag .p1w0 ≠ rawM tag .p1w1

/-- A nonconstant current channel is exposed when it factors through the
raw predictive M readout. This is the full HIDD test, not the narrow pair. -/
def C4Exposed (v : C4Variant) (tag : Tag) : Prop :=
  ∃ c ∈ c4Channels v,
    (∃ s t : KState, c4Channel tag c s ≠ c4Channel tag c t) ∧
    (∀ s t : KState, rawM tag s = rawM tag t →
      c4Channel tag c s = c4Channel tag c t)

def C4Surrogate (v : C4Variant) (tag : Tag) : Prop :=
  C4Collision v tag ∧ C4Connector v tag ∧ C4Exposed v tag

theorem c4_predictive_readout_link (tag : Tag) (s t : KState) :
    (rawM tag s = rawM tag t) ↔
      (taggedMClass tag s = taggedMClass tag t) :=
  rawM_iff_imported_M tag s t

theorem c4_collision_each_tag (tag : Tag) : C4Collision .positive tag := by
  cases tag <;> simp only [C4Collision] <;> decide

theorem c4_connector_each_tag (tag : Tag) : C4Connector .positive tag := by
  cases tag <;> simp only [C4Connector] <;> decide

theorem c4_public_position_exposes_M (v : C4Variant) (tag : Tag) :
    C4Exposed v tag := by
  refine ⟨.publicPosition, ?_, ⟨.p0w0, .p1w0, ?_⟩, ?_⟩
  · cases v <;> decide
  · cases tag <;> decide
  · intro s t h
    have hp := congrArg Prod.fst h
    simpa [c4Channel, rawM] using hp

/-- The full HIDD non-exposure target is false on each tagged T1 factor. -/
theorem c4_full_HIDD_nonexposure_fails (tag : Tag) :
    ¬ (¬ C4Exposed .positive tag) := by
  intro h
  exact h (c4_public_position_exposes_M .positive tag)

theorem c4_surrogate_each_tag (tag : Tag) : C4Surrogate .positive tag :=
  ⟨c4_collision_each_tag tag, c4_connector_each_tag tag,
   c4_public_position_exposes_M .positive tag⟩

theorem neg_c4_expose_loses_collision (tag : Tag) :
    ¬ C4Collision .negExpose tag := by
  cases tag <;> simp only [C4Collision] <;> decide

theorem c4_broken_connector_fails (tag : Tag) :
    ¬ C4Connector .brokenConnector tag := by
  cases tag <;> simp only [C4Connector] <;> decide

inductive C5Variant where | positive | negExternal | negInternalized | missingSelfEdge
  deriving DecidableEq, Repr

def c5Edges (v : C5Variant) (tag : Tag) (id : ProtocolId) :
    List ProtocolEdge :=
  if v = .negExternal && tag = .target && id = .clockwise then
    forwardEdges .other
  else if v = .missingSelfEdge && id = .clockwise then
    (forwardEdges .self).drop 1
  else protocolEdges id

def c5Owner (v : C5Variant) (tag : Tag) (id : ProtocolId) :
    ProvenanceOwner :=
  if v = .negExternal && tag = .target && id = .clockwise then .external
  else protocolOwner tag id

def c5Housing (v : C5Variant) (tag : Tag) (id : ProtocolId) :
    ProvenanceOwner :=
  if v = .negInternalized && tag = .target && id = .scheduled then .target
  else protocolHousing tag id

def c5Count (v : C5Variant) (tag : Tag) (id : ProtocolId)
    (a b : Vertex) (ch : Channel) : Nat :=
  ((c5Edges v tag id).filter fun e =>
    e.fromVertex == a && e.toVertex == b && e.channel == ch).length

def c5ForwardProduct (v : C5Variant) (tag : Tag)
    (id : ProtocolId) (ch : Channel) : Nat :=
  c5Count v tag id .u .v ch * c5Count v tag id .v .w ch *
    c5Count v tag id .w .u ch

def c5ReverseProduct (v : C5Variant) (tag : Tag)
    (id : ProtocolId) (ch : Channel) : Nat :=
  c5Count v tag id .v .u ch * c5Count v tag id .w .v ch *
    c5Count v tag id .u .w ch

inductive C5Credit where | self | other | none | ambiguous
  deriving DecidableEq, Repr

def c5Credit (v : C5Variant) (tag : Tag) (id : ProtocolId) : C5Credit :=
  let selfAsym := c5ForwardProduct v tag id .self !=
    c5ReverseProduct v tag id .self
  let otherAsym := c5ForwardProduct v tag id .other !=
    c5ReverseProduct v tag id .other
  if selfAsym && otherAsym then .ambiguous
  else if selfAsym then .self
  else if otherAsym then .other
  else .none

def C5AnchorsSupported (tag : Tag) : Prop :=
  ∀ vertex ∈ vertices, supportedHistory tag (historyAnchor vertex) = true

def C5OwnerConsistent (v : C5Variant) (tag : Tag) : Prop :=
  ∀ id ∈ protocolIds,
    (c5Credit v tag id = .self → c5Owner v tag id =
      if tag = .source then .source else .target) ∧
    (c5Credit v tag id = .other → c5Owner v tag id = .external)

def C5Surrogate (v : C5Variant) (tag : Tag) : Prop :=
  c5Credit v tag .clockwise = .self ∧
  c5Credit v tag .scheduled = .other ∧
  c5Credit v tag .internalized = .none ∧
  c5Credit v tag .null = .none ∧
  C5OwnerConsistent v tag ∧ C5AnchorsSupported tag

def C5StagedHousing (v : C5Variant) : Prop :=
  c5Housing v .source .scheduled = c5Housing v .target .scheduled

def c5TranslateOwner : ProvenanceOwner → ProvenanceOwner
  | .source => .target
  | other => other

/-- The full raw protocol table equation used by the staged C5 check in
`scripts/evaluate_fiach_pos04.py:716-725`. -/
def C5RawTransport (v : C5Variant) : Prop :=
  ∀ id ∈ protocolIds,
    c5Edges v .source id = c5Edges v .target id ∧
    c5TranslateOwner (c5Owner v .source id) = c5Owner v .target id ∧
    c5TranslateOwner (c5Housing v .source id) = c5Housing v .target id

theorem c5_products_each_tag (tag : Tag) :
    c5ForwardProduct .positive tag .clockwise .self = 1 ∧
    c5ReverseProduct .positive tag .clockwise .self = 0 ∧
    c5ForwardProduct .positive tag .scheduled .other = 1 ∧
    c5ReverseProduct .positive tag .scheduled .other = 0 := by
  cases tag <;> decide

theorem c5_surrogate_each_tag (tag : Tag) : C5Surrogate .positive tag := by
  cases tag <;> simp only [C5Surrogate, C5OwnerConsistent,
    C5AnchorsSupported] <;> decide

theorem c5_staged_housing : C5StagedHousing .positive := by
  simp only [C5StagedHousing]
  decide

theorem c5_raw_staged_transport : C5RawTransport .positive := by
  simp only [C5RawTransport]
  decide

theorem neg_c5_external_credit_is_other :
    c5Credit .negExternal .target .clockwise = .other := by decide

theorem neg_c5_external_fails :
    ¬ C5Surrogate .negExternal .target := by
  intro h
  have hc := h.1
  have hn : c5Credit .negExternal .target .clockwise ≠ .self := by decide
  exact hn hc

theorem neg_c5_internalized_credit_still_other :
    c5Credit .negInternalized .target .scheduled = .other := by decide

theorem neg_c5_internalized_local_still_holds :
    C5Surrogate .negInternalized .target := by
  simp only [C5Surrogate, C5OwnerConsistent, C5AnchorsSupported]
  decide

theorem neg_c5_internalized_breaks_staged_housing :
    ¬ C5StagedHousing .negInternalized := by
  simp only [C5StagedHousing]
  decide

theorem neg_c5_internalized_breaks_raw_transport :
    ¬ C5RawTransport .negInternalized := by
  simp only [C5RawTransport]
  decide

theorem c5_missing_self_edge_fails (tag : Tag) :
    ¬ C5Surrogate .missingSelfEdge tag := by
  intro h
  have hc := h.1
  have hn : c5Credit .missingSelfEdge tag .clockwise ≠ .self := by
    cases tag <;> decide
  exact hn hc

end CSTTT.POS04
