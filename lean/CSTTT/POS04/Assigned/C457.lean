import CSTTT.POS04.Assigned.Guards

/-! G2b-1, M3_model_spec.md:20,21,23,30–35. Assigned C4/C5/C7 remain
surrogates, not HIDD/T5/joint-history upgrades. Derived histories, readouts,
credits, distributions, displays and route registers are never arguments.
The C4 connector is the shared history `split`; the frozen connector table
agrees with that history. C5's graph anchors are fixed views of the same
history cells. Future route/writer dependencies are prepared for G2b-2. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit

structure ExtraInputs where
  base : Inputs
  channels : List CurrentChannel
  protocols : ProtocolData
  joint : JointData
  histories : HistoryId → List KState
  events : List Event
  realized : List Stage
  receiver : Receiver
  routes : List Route
  writers : Tag → RouteId → Bool

def extraInputs (d : Assignment) (tag : Tag) : ExtraInputs :=
  ⟨inputs d tag,
   (d .channels).getD (canonicalValue .channels),
   (d (.protocols tag)).getD (canonicalValue (.protocols tag)),
   (d (.joint tag)).getD (canonicalValue (.joint tag)),
   (d .histories).getD (canonicalValue .histories),
   (d .eventTable).getD (canonicalValue .eventTable),
   (d .realized).getD (canonicalValue .realized),
   (d .receiverInput).getD (canonicalValue .receiverInput),
   (d .routeTable).getD (canonicalValue .routeTable),
   (d .writers).getD (canonicalValue .writers)⟩

def clauseExtra (a : Assignment) (tag : Tag) (c : Clause) : ExtraInputs :=
  extraInputs (decode (clauseScope tag c) a) tag

theorem extra_locality {a b : Assignment} {tag : Tag} {c : Clause}
    (h : Agrees (clauseScope tag c) a b) : clauseExtra a tag c = clauseExtra b tag c := by
  unfold clauseExtra
  rw [decoder_locality h]

def pathSupported (d : ExtraInputs) (path : List KState) : Bool :=
  !path.isEmpty && ((path.zip (path.drop 1)).all fun edge =>
    decide (rowWeight (d.base.rows edge.1 (d.base.policy edge.1)) edge.2 > 0))
def historySupported (d : ExtraInputs) (id : HistoryId) := pathSupported d (d.histories id)

/-- Fixed connector/anchor identities are views; their raw paths live in the
shared history cell. The decode does not accept an independent connector proof. -/
def connector (d : ExtraInputs) := d.histories .split

def currentChannel (d : ExtraInputs) (c : CurrentChannel) (s : KState) :
    (Nat × List Action) × Option (Nat × List (List Bool)) :=
  match c with
  | .publicPosition => ((d.base.positions s,[]),none)
  | .deadlineAvailability => ((0,actions.filter fun a => !(d.base.rows s a).isEmpty),none)
  | .canonicalM => ((0,[]),some (predictive d.base s))
def current (d : ExtraInputs) (s : KState) := d.channels.map (fun c => currentChannel d c s)

def Collision4 (d : ExtraInputs) : Prop :=
  current d hiddenPair.1 = current d hiddenPair.2 ∧
  predictive d.base hiddenPair.1 ≠ predictive d.base hiddenPair.2

def Connector4 (d : ExtraInputs) : Prop :=
  ((connector d).zip ((connector d).drop 1)).all (fun edge =>
    decide (rowWeight (d.base.rows edge.1 (d.base.policy edge.1)) edge.2 > 0)) = true ∧
  current d .p1w0 = current d .p1w1 ∧ predictive d.base .p1w0 ≠ predictive d.base .p1w1

def Exposed4 (d : ExtraInputs) : Prop :=
  ∃ c ∈ d.channels,
    (∃ s t : KState, currentChannel d c s ≠ currentChannel d c t) ∧
    (∀ s t : KState, predictive d.base s = predictive d.base t →
      currentChannel d c s = currentChannel d c t)

def C4Gate (a : Assignment) (tag : Tag) : Prop :=
  Ready a tag .c4 ∧ MLinked (clauseExtra a tag .c4).base ∧
  (connector (clauseExtra a tag .c4)).head? = some hiddenPair.1 ∧
  (connector (clauseExtra a tag .c4)).getLast? = some hiddenPair.2 ∧
  (connector (clauseExtra a tag .c4)).length ≥ 2

def C4Accept (a : Assignment) (tag : Tag) : Prop :=
  C4Gate a tag ∧ Collision4 (clauseExtra a tag .c4) ∧
    Connector4 (clauseExtra a tag .c4) ∧ Exposed4 (clauseExtra a tag .c4)

def count5 (d : ExtraInputs) (id : ProtocolId) (a b : Vertex) (ch : Channel) : Nat :=
  ((d.protocols.edges id).filter fun e =>
    e.fromVertex == a && e.toVertex == b && e.channel == ch).length
def forward5 (d : ExtraInputs) (id : ProtocolId) (ch : Channel) :=
  count5 d id .u .v ch * count5 d id .v .w ch * count5 d id .w .u ch
def reverse5 (d : ExtraInputs) (id : ProtocolId) (ch : Channel) :=
  count5 d id .v .u ch * count5 d id .w .v ch * count5 d id .u .w ch

def credit5 (d : ExtraInputs) (id : ProtocolId) : C5Credit :=
  let selfAsym := forward5 d id .self != reverse5 d id .self
  let otherAsym := forward5 d id .other != reverse5 d id .other
  if selfAsym && otherAsym then .ambiguous
  else if selfAsym then .self else if otherAsym then .other else .none

def Owner5 (d : ExtraInputs) (tag : Tag) : Prop :=
  ∀ id ∈ protocolIds,
    (credit5 d id = .self → d.protocols.owner id =
      if tag = .source then .source else .target) ∧
    (credit5 d id = .other → d.protocols.owner id = .external)
def Anchors5 (d : ExtraInputs) : Prop :=
  ∀ vertex ∈ vertices, historySupported d (historyAnchor vertex) = true

def C5Gate (a : Assignment) (tag : Tag) : Prop := Ready a tag .c5
def C5Rule (d : ExtraInputs) (tag : Tag) : Prop :=
  credit5 d .clockwise = .self ∧ credit5 d .scheduled = .other ∧
  credit5 d .internalized = .none ∧ credit5 d .null = .none ∧ Owner5 d tag ∧ Anchors5 d

def C5Accept (a : Assignment) (tag : Tag) : Prop :=
  C5Gate a tag ∧ C5Rule (clauseExtra a tag .c5) tag

def C5Transport (a : Assignment) : Prop :=
  C5Gate a .source ∧ C5Gate a .target ∧
  ∀ id ∈ protocolIds,
    (clauseExtra a .source .c5).protocols.edges id = (clauseExtra a .target .c5).protocols.edges id ∧
    c5TranslateOwner ((clauseExtra a .source .c5).protocols.owner id) =
      (clauseExtra a .target .c5).protocols.owner id ∧
    c5TranslateOwner ((clauseExtra a .source .c5).protocols.housing id) =
      (clauseExtra a .target .c5).protocols.housing id

def pairCount7 (d : ExtraInputs) (id : AssemblageId) (l r : HistoryId) : Nat :=
  ((d.joint.coupling id).filter fun p => d.histories (d.joint.left p.1) == d.histories l &&
      d.histories (d.joint.right p.2) == d.histories r).length
def pairing7 (d : ExtraInputs) (id : AssemblageId) (l r : HistoryId) : Rat :=
  (pairCount7 d id l r : Rat) / (d.joint.coupling id).length

def branchwise7 (d : ExtraInputs) (_id : AssemblageId) :
    List (List KState) × List (List KState) :=
  ([d.histories (d.joint.left 0),d.histories (d.joint.left 1)],
   [d.histories (d.joint.right 0),d.histories (d.joint.right 1)])
def distribution7 (d : ExtraInputs) (id : AssemblageId) : List (Nat × Nat) :=
  historyIds.flatMap fun l => historyIds.map fun r =>
    (pairCount7 d id l r,(d.joint.coupling id).length)
def display7 (d : ExtraInputs) (id : AssemblageId) : List (Nat × Nat) :=
  if .jointPairing ∈ d.joint.observables then distribution7 d id else []
def recombination7 (d : ExtraInputs) (id : AssemblageId) :=
  (branchwise7 d id,display7 d id)
def Strict7 (d : ExtraInputs) : Prop :=
  AssemblageId.diagonal ≠ .crossed ∧ branchwise7 d .diagonal = branchwise7 d .crossed ∧
  recombination7 d .diagonal ≠ recombination7 d .crossed

def Local7 (d : ExtraInputs) : Prop :=
  ∀ id ∈ assemblageIds, d.joint.coupling id = coupling (d.joint.reassembly id) ∧
    (d.joint.coupling id).length = 2 ∧ (d.joint.coupling id).Nodup

def Histories7 (d : ExtraInputs) : Prop := ∀ id ∈ historyIds, historySupported d id = true

def mixed7 (d : ExtraInputs) : Bool :=
  d.events.any fun e => e.id != .exit && e.atomic && e.sourceSupport &&
    e.targetSupport && decide (e.fromStage ∈ d.realized) && decide (e.toStage ∈ d.realized)
def active7 (d : ExtraInputs) : Bool :=
  d.receiver.sourcePresent && d.receiver.targetReceiverFunded && d.receiver.funded &&
    (!d.receiver.mixedEventRequired || mixed7 d)

/-- Actual pre-exit receiver output is unavailable without a realized mix
and activation. This is derived from raw inputs, never a stored display. -/
def receiverDisplay7 (d : ExtraInputs) (id : AssemblageId) : List (Nat × Nat) :=
  if mixed7 d && active7 d then display7 d id else []

def Operational7 (d : ExtraInputs) : Prop :=
  mixed7 d = true ∧ active7 d = true ∧ receiverDisplay7 d .diagonal ≠ receiverDisplay7 d .crossed ∧
  (∀ s ∈ kernel, ∀ t ∈ kernel,
    rowWeight (d.base.rows s (d.base.policy s)) t = d.base.publishedP (index s) (index t))

theorem operational7_iff_raw (d : ExtraInputs) :
    Operational7 d ↔ mixed7 d = true ∧ active7 d = true ∧
      display7 d .diagonal ≠ display7 d .crossed ∧
      (∀ s ∈ kernel, ∀ t ∈ kernel,
        rowWeight (d.base.rows s (d.base.policy s)) t = d.base.publishedP (index s) (index t)) := by
  unfold Operational7
  constructor <;> rintro ⟨hm,ha,hd,hp⟩ <;> refine ⟨hm,ha,?_,hp⟩
  · simpa [receiverDisplay7,hm,ha] using hd
  · simpa [receiverDisplay7,hm,ha] using hd

def C7Gate (a : Assignment) (tag : Tag) : Prop :=
  Ready a tag .c7 ∧ (clauseExtra a tag .c7).base.publishedP = pNum ∧
  (historyIds.map (clauseExtra a tag .c7).histories).Nodup

def C7Rule (d : ExtraInputs) : Prop := Local7 d ∧ Histories7 d ∧ Strict7 d ∧ Operational7 d

def C7Accept (a : Assignment) (tag : Tag) : Prop :=
  C7Gate a tag ∧ C7Rule (clauseExtra a tag .c7)

def C7Transport (a : Assignment) : Prop :=
  C7Gate a .source ∧ C7Gate a .target ∧
  (clauseExtra a .source .c7).joint.observables = (clauseExtra a .target .c7).joint.observables ∧
  ∀ id ∈ assemblageIds,
    branchwise7 (clauseExtra a .source .c7) id = branchwise7 (clauseExtra a .target .c7) id ∧
    (clauseExtra a .source .c7).joint.coupling id = (clauseExtra a .target .c7).joint.coupling id ∧
    distribution7 (clauseExtra a .source .c7) id = distribution7 (clauseExtra a .target .c7) id

/-- The retained route register is a defined readout of the raw tuple and
history tables, not an independent assigned candidate. -/
def routeTuple (d : ExtraInputs) (id : RouteId) : Option (List KState × List EventId) :=
  (d.routes.find? fun r => r.id == id).map fun r => (d.histories r.sourceHistory,r.eventPath)

/-- Preparatory reference gate for C6's new dependencies. It is deliberately
not a C6 acceptance theorem: funded future dynamics belong to G2b-2. -/
def FutureReferenceGate (a : Assignment) (tag : Tag) : Prop :=
  Complete (clauseScope tag .c6) a ∧
  let d := clauseExtra a tag .c6
  (routeIds.all fun id =>
    (d.routes.any fun r => r.id == id && !r.eventPath.isEmpty &&
      historySupported d r.sourceHistory) && d.writers tag id) = true


end CSTTT.POS04.Assigned
