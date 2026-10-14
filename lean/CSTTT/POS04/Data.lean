import CSTTT.Objecthood.T1Audit

/-!
FIACH-POS-04 raw finite data. Source: `audit/proposed_models/FIACH-POS-04.model.json`
at declaration commit `8ba44df`. No verdict fields are represented here. The exact
T1 kernel, canonical P, M-class table, and C1 audit are imported from `T1Audit`.
-/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

/-! L6–L8 transition rule: every transition-based lane uses `actionRow` and
`taggedPNum`, or proves its alternative table equal to them. Any M readout
computed from raw action supports and hazards must be proved equal, as a
partition, to the imported T1 `mClass` before it is used as a lane premise. -/

inductive Tag where | source | target deriving DecidableEq, Repr
def tags : List Tag := [.source, .target]
abbrev TaggedState := Tag × KState
abbrev TaggedIndex := Tag × I
def swapTag : Tag → Tag | .source => .target | .target => .source
def swapTagged (x : TaggedState) : TaggedState := (swapTag x.1, x.2)

def index : KState → I
  | .p0w0 => 0 | .p0w1 => 1 | .p1w0 => 2 | .p1w1 => 3
  | .p2w1 => 4 | .p3w0 => 5 | .p3w1 => 6
  | .p4w0 => 7 | .p4w1 => 8 | .p5w0 => 9

def indices : List I := [0,1,2,3,4,5,6,7,8,9]
def taggedPNum (_tag : Tag) (s t : KState) : Nat := pNum (index s) (index t)
def taggedMClass (_tag : Tag) (s : KState) : Nat := mClass (index s)
def taggedPi (x : TaggedIndex) : Rat := pi x.2
def taggedCoreMass (tag : Tag) : Rat := coreMass (fun i => taggedPi (tag,i))
def taggedTV (tag : Tag) : Rat := tvFromCoreUniform (fun i => taggedPi (tag,i))
def taggedDefect (_tag : Tag) : Rat := defect E2eps

/-! `t1_import.C`, `U`, `hazards`, `slip_hold`, `slip_advance`, and `C1` in
`audit/proposed_models/FIACH-POS-04.model.json` (declared at `8ba44df`).
The seven prototype classes are in the JSON's C-column order, distinct from
their first-occurrence numeric identifiers in `T1Audit.mClasses`. C and U are
computed from that order and the imported M fibers, then checked separately
against the frozen JSON. -/
abbrev J := Fin 7
def declaredClassOrder : List Nat := [0,2,1,3,4,5,6]
def cIndicator (i : I) (k : J) : Nat :=
  if mClass i = declaredClassOrder.getD k.val 0 then 1 else 0
def uPrototypeNum (k : J) (j : I) : Nat :=
  if mClass j = declaredClassOrder.getD k.val 0 then 2 / classSize j else 0
def sum7 (f : J → Nat) : Nat :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6
def hazardPositions : List Nat := [2,5]
def slipDen : Nat := 4
def slipHoldNum : Nat := 1
def slipAdvanceNum : Nat := 3
def c1Tau : Nat := 2
def c1Epsilon : Rat := 1/16
def c1RetentionThreshold : Rat := 3/4

def TaggedProbability (tag : Tag) (μ : TaggedIndex → Rat) : Prop :=
  IsProbability (fun i => μ (tag,i))
def TaggedFixed (tag : Tag) (μ : TaggedIndex → Rat) : Prop :=
  IsFixed E2eps (fun i => μ (tag,i))

/-! `new_data.raw_inputs.by_tag.*.action_distributions`: the canonical action
row is computed from imported T1 `P`; only noncanonical action supports below
are transcribed. The ambient exits p2w0 and p5w1 are outside T1 K. Every
weight has denominator four, as in the JSON and T1's raw action table. -/
inductive Ambient where
  | inK (state : KState) | p2w0 | p5w1
  deriving DecidableEq, Repr
def ambientStates : List Ambient :=
  [.inK .p0w0,.inK .p0w1,.inK .p1w0,.inK .p1w1,.p2w0,
   .inK .p2w1,.inK .p3w0,.inK .p3w1,.inK .p4w0,.inK .p4w1,
   .inK .p5w0,.p5w1]

def canonicalAction (s : KState) : Action := canonicalPolicy.getD (index s).val .stay
def canonicalRow (s : KState) : List (Ambient × Nat) :=
  indices.filterMap fun j =>
    let n := pNum (index s) j
    if n == 0 then none else some (.inK (stateAt j), n)

def halfP1 : List (Ambient × Nat) := [(.inK .p1w0,2),(.inK .p1w1,2)]
def noncanonicalRow (s : KState) (a : Action) : List (Ambient × Nat) :=
  match s, a with
  | .p0w0, _ | .p0w1, _ | .p3w0, _ | .p3w1, _
  | .p4w0, _ | .p4w1, _ => halfP1
  | .p1w0, .stay | .p1w1, .stay => []
  | .p1w0, .cw => [(.inK .p2w1,4)]
  | .p1w0, .ccw => [(.p5w1,4)]
  | .p1w1, .cw => [(.p2w0,4)]
  | .p1w1, .ccw => [(.inK .p5w0,4)]
  | .p2w1, .stay => [(.inK .p1w0,3),(.inK .p1w1,1)]
  | .p2w1, _ => [(.p2w0,4)]
  | .p5w0, .stay => [(.inK .p1w1,3),(.inK .p1w0,1)]
  | .p5w0, _ => [(.p5w1,4)]

def actionRow (_tag : Tag) (s : KState) (a : Action) : List (Ambient × Nat) :=
  if a = canonicalAction s then canonicalRow s else noncanonicalRow s a
def rowWeight (row : List (Ambient × Nat)) (t : KState) : Nat :=
  (row.filter fun entry => entry.1 == Ambient.inK t).foldl
    (fun total entry => total + entry.2) 0

def actions : List Action := [.stay,.cw,.ccw]
def tickIncrement (_tag : Tag) (_s : KState) (_a : Action) : Nat := 1
inductive PublicChannelRule where | position deriving DecidableEq, Repr
def publicChannelRule (_tag : Tag) : PublicChannelRule := .position
def publicPosition (s : KState) : Nat :=
  match s with
  | .p0w0 | .p0w1 => 0 | .p1w0 | .p1w1 => 1 | .p2w1 => 2
  | .p3w0 | .p3w1 => 3 | .p4w0 | .p4w1 => 4 | .p5w0 => 5
def ambientPosition : Ambient → Nat
  | .inK s => publicPosition s | .p2w0 => 2 | .p5w1 => 5
def ambientPhase : Ambient → Nat
  | .inK .p0w0 | .inK .p1w0 | .inK .p3w0 | .inK .p4w0
  | .inK .p5w0 | .p2w0 => 0
  | .inK .p0w1 | .inK .p1w1 | .inK .p2w1 | .inK .p3w1
  | .inK .p4w1 | .p5w1 => 1
def isLethalHazard (s : Ambient) : Bool :=
  decide (ambientPosition s ∈ hazardPositions ∧
    ambientPhase s = ambientPosition s % 2)

/-! `new_data.corridor`: stages, events, realization, and two raw paths.
Every constructor corresponds to a JSON enumerand, not to a truth value. -/
inductive Stage where | sourceLive | mix1 | mix2 | targetExit
  deriving DecidableEq, Repr, Inhabited
def stages : List Stage := [.sourceLive,.mix1,.mix2,.targetExit]
def realizedStages : List Stage := [.sourceLive,.mix1,.mix2,.targetExit]

inductive EventId where | mix1 | mix2 | exit deriving DecidableEq, Repr, Inhabited
structure Event where
  id : EventId
  fromStage : Stage
  toStage : Stage
  sourceSupport : Bool
  targetSupport : Bool
  atomic : Bool
  strictStep : Bool
  deriving DecidableEq, Repr, Inhabited

def events : List Event :=
  [⟨.mix1,.sourceLive,.mix1,true,true,true,true⟩,
   ⟨.mix2,.mix1,.mix2,true,true,true,true⟩,
   ⟨.exit,.mix2,.targetExit,false,true,true,true⟩]
def eventIds : List EventId := [.mix1,.mix2,.exit]
def eventOf : EventId → Event
  | .mix1 => events[0]!
  | .mix2 => events[1]!
  | .exit => events[2]!

inductive HistoryId where | repA | repB | classB | split
  deriving DecidableEq, Repr, Inhabited
def historyIds : List HistoryId := [.repA,.repB,.classB,.split]
/-! `new_data.histories`, four exact source paths; target histories are the
pointwise tag images of these paths. -/
def sourceHistory : HistoryId → List KState
  | .repA => [.p1w0,.p2w1,.p1w0]
  | .repB => [.p1w1,.p5w0,.p1w0]
  | .classB => [.p1w1,.p5w0,.p1w1]
  | .split => [.p1w0,.p2w1,.p1w1]
def taggedHistory (tag : Tag) (id : HistoryId) : List TaggedState :=
  (sourceHistory id).map (tag,·)
def bridgeFrontier : List HistoryId := historyIds
def strictSourceEdge : KState × KState := (.p1w0,.p2w1)
def sameClassPair : HistoryId × HistoryId := (.repA,.repB)
def differentClassPair : HistoryId × HistoryId := (.repA,.classB)

inductive RouteId where | a | b deriving DecidableEq, Repr, Inhabited
def routeIds : List RouteId := [.a,.b]
structure Route where
  id : RouteId
  sourceHistory : HistoryId
  eventPath : List EventId
  deriving DecidableEq, Repr, Inhabited
def routes : List Route :=
  [⟨.a,.repA,[.mix1,.mix2,.exit]⟩,
   ⟨.b,.repB,[.mix1,.mix2,.exit]⟩]
def routeOf : RouteId → Route
  | .a => routes[0]!
  | .b => routes[1]!
/-! `new_data.receiver.route_register_write`: raw history and event path,
not a route name or a stored status. -/
def routeRegister (id : RouteId) : List KState × List EventId :=
  (sourceHistory (routeOf id).sourceHistory, (routeOf id).eventPath)
def recordWriterAvailable (_tag : Tag) (_route : RouteId) : Bool := true
def contentCounterfactuals : List HistoryId := [.repA,.classB]
inductive SupportIntervention where | removeSource | removeTarget
  deriving DecidableEq, Repr
def supportInterventions : List SupportIntervention := [.removeSource,.removeTarget]
inductive RouteReadout where | firstSourcePhaseAfterFundedStep
  deriving DecidableEq, Repr
def routeReadout : RouteReadout := .firstSourcePhaseAfterFundedStep
def routeReadoutOwner : Tag := .target

/-! `new_data.receiver`: fixed latent target, source-dependent activation,
coordinate-copy content, and raw route-tuple write. -/
inductive ContentRule where | copyTerminalPositionPhase deriving DecidableEq, Repr
inductive RegisterRule where | copyRawRouteTuple deriving DecidableEq, Repr
structure Receiver where
  latentFactor : KState
  funded : Bool
  initialBudget : Nat
  sourcePresent : Bool
  targetReceiverFunded : Bool
  mixedEventRequired : Bool
  contentRule : ContentRule
  registerRule : RegisterRule
  deriving DecidableEq, Repr
def receiver : Receiver :=
  ⟨.p0w0,true,1,true,true,true,.copyTerminalPositionPhase,.copyRawRouteTuple⟩

/-! `new_data.maintenance` and per-tag resources. These are raw one-token
ledger values; no viable or autonomy verdict is stored. -/
structure Ledger where
  actionCost : Nat
  rechargePerAction : Nat
  initialBudget : Nat
  sourceAvailableAfterWithdrawal : Bool
  deriving DecidableEq, Repr
def ledger : Ledger := ⟨1,1,1,false⟩
def rechargeAvailableAfterWithdrawal (_tag : Tag) : Bool := true
def resourceOwner : Tag → Tag | .source => .source | .target => .target
inductive RecognitionStatus where | notAddressed deriving DecidableEq, Repr
def recognitionStatus : RecognitionStatus := .notAddressed

/-! Clause-local raw inputs from JSON, for L6. -/
inductive CurrentChannel where | publicPosition | deadlineAvailability | canonicalM
  deriving DecidableEq, Repr
def currentChannels : List CurrentChannel := [.publicPosition,.deadlineAvailability]
def expandedChannel : CurrentChannel := .canonicalM
def connectorHistory : List KState := [.p1w0,.p2w1,.p1w1]
def hiddenPair : KState × KState := (.p1w0,.p1w1)

/-! `new_data.c5`: the independent three-vertex protocol graph, including
the internally housed scheduled control. It is a raw graph, not a C5 verdict.
The source and target rows differ only in their owner/housing tag. -/
inductive Vertex where | u | v | w deriving DecidableEq, Repr
inductive ProtocolId where | clockwise | scheduled | internalized | null
  deriving DecidableEq, Repr
inductive Channel where | self | other deriving DecidableEq, Repr
inductive ProvenanceOwner where | source | target | external | none
  deriving DecidableEq, Repr
structure ProtocolEdge where
  fromVertex : Vertex
  toVertex : Vertex
  channel : Channel
  deriving DecidableEq, Repr
def protocolIds : List ProtocolId := [.clockwise,.scheduled,.internalized,.null]
def vertices : List Vertex := [.u,.v,.w]
def forwardEdges (channel : Channel) : List ProtocolEdge :=
  [⟨.u,.v,channel⟩,⟨.v,.w,channel⟩,⟨.w,.u,channel⟩]
def reverseEdges (channel : Channel) : List ProtocolEdge :=
  [⟨.v,.u,channel⟩,⟨.w,.v,channel⟩,⟨.u,.w,channel⟩]
def protocolEdges : ProtocolId → List ProtocolEdge
  | .clockwise => forwardEdges .self
  | .scheduled => forwardEdges .other
  | .internalized => forwardEdges .self ++ forwardEdges .other ++
      reverseEdges .self ++ reverseEdges .other
  | .null => []
def protocolOwner (tag : Tag) : ProtocolId → ProvenanceOwner
  | .clockwise => if tag = .source then .source else .target
  | .scheduled | .internalized => .external
  | .null => .none
def protocolHousing (tag : Tag) : ProtocolId → ProvenanceOwner
  | .clockwise | .internalized => if tag = .source then .source else .target
  | .scheduled => .external
  | .null => .none
def protocolChannel : ProtocolId → String
  | .clockwise => "self" | .scheduled => "other"
  | .internalized => "self-and-other-balanced" | .null => "none"
def protocolKind : ProtocolId → String
  | .clockwise => "native-policy" | .scheduled => "external-schedule"
  | .internalized => "internalized-schedule" | .null => "no-generator"
def historyAnchor : Vertex → HistoryId
  | .u => .repA | .v => .split | .w => .classB

inductive FutureObservable where
  | predictiveNow | eventOrder | tickPhase | cumulativeProgress
  | endogenousRecordCount | routeResidue | maintenanceState | owner
  deriving DecidableEq, Repr
def futureInterface : List FutureObservable :=
  [.predictiveNow,.eventOrder,.tickPhase,.cumulativeProgress,
   .endogenousRecordCount,.routeResidue,.maintenanceState,.owner]
def futureAlphabet : List Action := actions
def candidateMergedPair : KState × KState := (.p0w0,.p0w1)
def routeRecordOwner : Tag := .target

inductive AssemblageId where | diagonal | crossed deriving DecidableEq, Repr
def assemblageIds : List AssemblageId := [.diagonal,.crossed]
def leftBranch : Fin 2 → HistoryId | 0 => .repA | _ => .repB
def rightBranch : Fin 2 → HistoryId | 0 => .classB | _ => .split
def coupling : AssemblageId → List (Fin 2 × Fin 2)
  | .diagonal => [(0,0),(1,1)]
  | .crossed => [(0,1),(1,0)]
def reassembly (_tag : Tag) (id : AssemblageId) : AssemblageId := id
inductive JointObservable where | jointPairing deriving DecidableEq, Repr
def jointObservables (_tag : Tag) : List JointObservable := [.jointPairing]

inductive Clause where | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8
  deriving DecidableEq, Repr
def clauses : List Clause := [.c1,.c2,.c3,.c4,.c5,.c6,.c7,.c8]
structure Coordinate where
  tag : Tag
  state : KState
  clause : Clause
  deriving DecidableEq, Repr
/-! `new_data.local_assignments`: the JSON enumerates exactly the Cartesian
product of two tags, ten K states, and eight clauses, in this order. -/
def coordinates : List Coordinate :=
  tags.flatMap fun tag => kernel.flatMap fun state =>
    clauses.map fun clause => ⟨tag,state,clause⟩
def stagedClauseMap : List (Clause × Tag × Tag) :=
  clauses.map fun clause => (clause,.source,.target)

inductive PrimitiveRef where
  | actionDistributions | publishedP | publishedC | publishedU
  | publicChannelRule | publishedMClasses | currentChannels | protocols
  | tickIncrement | futureInterface | assemblages | resources | maintenance
  deriving DecidableEq, Repr
def primitiveRefs (_tag : Tag) : Clause → List PrimitiveRef
  | .c1 => [.actionDistributions,.publishedP,.publishedC,.publishedU]
  | .c2 => [.publicChannelRule,.publishedMClasses]
  | .c3 => [.actionDistributions,.publishedMClasses]
  | .c4 => [.currentChannels]
  | .c5 => [.protocols]
  | .c6 => [.tickIncrement,.futureInterface]
  | .c7 => [.assemblages]
  | .c8 => [.resources,.maintenance]

/-! Names below are the JSON spellings used by the read-only transcription
check. They are not classification or verdict fields. -/
def tagName : Tag → String | .source => "source" | .target => "target"
def stateName : KState → String
  | .p0w0 => "p0w0" | .p0w1 => "p0w1" | .p1w0 => "p1w0"
  | .p1w1 => "p1w1" | .p2w1 => "p2w1" | .p3w0 => "p3w0"
  | .p3w1 => "p3w1" | .p4w0 => "p4w0" | .p4w1 => "p4w1"
  | .p5w0 => "p5w0"
def ambientName : Ambient → String
  | .inK s => stateName s | .p2w0 => "p2w0" | .p5w1 => "p5w1"
def actionName : Action → String | .stay => "stay" | .cw => "cw" | .ccw => "ccw"
def publicChannelRuleName : PublicChannelRule → String | .position => "position"
def supportInterventionName : SupportIntervention → String
  | .removeSource => "remove_source_support"
  | .removeTarget => "remove_target_support"
def routeReadoutRuleName : RouteReadout → String
  | .firstSourcePhaseAfterFundedStep =>
      "phase of first source WheelState in retained raw route tuple after one funded target step"
def contentRulePositionName : ContentRule → String
  | .copyTerminalPositionPhase => "copy_source_terminal_p"
def contentRulePhaseName : ContentRule → String
  | .copyTerminalPositionPhase => "copy_source_terminal_w"
def registerRuleName : RegisterRule → String
  | .copyRawRouteTuple => "copy_raw_route_tuple"
def recognitionStatusName : RecognitionStatus → String
  | .notAddressed => "notAddressed"
def stageName : Stage → String
  | .sourceLive => "source_live" | .mix1 => "mix_1"
  | .mix2 => "mix_2" | .targetExit => "target_exit"
def eventName : EventId → String | .mix1 => "mix_1" | .mix2 => "mix_2" | .exit => "exit"
def historyName : HistoryId → String
  | .repA => "h_rep_a" | .repB => "h_rep_b"
  | .classB => "h_class_b" | .split => "h_split"
def routeName : RouteId → String | .a => "route_a" | .b => "route_b"
def channelName : CurrentChannel → String
  | .publicPosition => "public_position"
  | .deadlineAvailability => "deadline_action_availability"
  | .canonicalM => "canonical_M"
def observableName : FutureObservable → String
  | .predictiveNow => "PredictiveNow" | .eventOrder => "event_order"
  | .tickPhase => "tick_phase" | .cumulativeProgress => "cumulative_progress"
  | .endogenousRecordCount => "endogenous_record_count"
  | .routeResidue => "route_residue" | .maintenanceState => "maintenance_state"
  | .owner => "owner"
def assemblageName : AssemblageId → String
  | .diagonal => "diagonal" | .crossed => "crossed"
def jointObservableName : JointObservable → String
  | .jointPairing => "jointPairing"
def clauseName : Clause → String
  | .c1 => "C1" | .c2 => "C2" | .c3 => "C3" | .c4 => "C4"
  | .c5 => "C5" | .c6 => "C6" | .c7 => "C7" | .c8 => "C8"
def vertexName : Vertex → String | .u => "u" | .v => "v" | .w => "w"
def protocolName : ProtocolId → String
  | .clockwise => "clockwise" | .scheduled => "scheduled"
  | .internalized => "internalized" | .null => "null"
def creditChannelName : Channel → String | .self => "self" | .other => "other"
def provenanceOwnerName : ProvenanceOwner → Option String
  | .source => some "source" | .target => some "target"
  | .external => some "external" | .none => none
def primitivePath (tag : Tag) : PrimitiveRef → String
  | .actionDistributions => "/new_data/raw_inputs/by_tag/" ++ tagName tag ++ "/action_distributions"
  | .publishedP => "/t1_import/P" | .publishedC => "/t1_import/C"
  | .publishedU => "/t1_import/U"
  | .publicChannelRule => "/new_data/raw_inputs/by_tag/" ++ tagName tag ++ "/public_channel_rule"
  | .publishedMClasses => "/t1_import/M_class_labels"
  | .currentChannels => "/new_data/c4/current_channels"
  | .protocols => "/new_data/c5/protocols"
  | .tickIncrement => "/new_data/raw_inputs/by_tag/" ++ tagName tag ++ "/tick_increment"
  | .futureInterface => "/new_data/c6/future_interface"
  | .assemblages => "/new_data/c7/by_tag/" ++ tagName tag ++ "/assemblages"
  | .resources => "/new_data/raw_inputs/by_tag/" ++ tagName tag ++ "/resources"
  | .maintenance => "/new_data/maintenance"
def coordinateLabel (c : Coordinate) : String :=
  tagName c.tag ++ ":" ++ stateName c.state ++ ":" ++ clauseName c.clause

end CSTTT.POS04
