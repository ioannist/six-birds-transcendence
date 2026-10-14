import CSTTT.POS04.WellFormed
import Lean

/-! Machine-readable view of evaluated Lean data for the read-only JSON
transcription check. All entries below call the typed definitions in `Data`;
this module contains no independent data tables or verdicts. -/

namespace CSTTT.POS04

open Lean CSTTT.Objecthood.T1Audit

private def obj := Json.mkObj
private def str := Json.str
private def arr (xs : List Json) : Json := Json.arr xs.toArray
private def nat (n : Nat) : Json := Lean.toJson n
private def bool (b : Bool) : Json := Lean.toJson b
private def stringList (xs : List String) : Json := Lean.toJson xs
private def twoSlots : List (Fin 2) := [0,1]
private def sevenSlots : List J := [0,1,2,3,4,5,6]
private def rat (x : Rat) : Json := str (toString x)

private def weightString : Nat → String
  | 1 => "1/4" | 2 => "1/2" | 3 => "3/4" | 4 => "1/1" | n => toString n ++ "/4"

def exportActionRow (tag : Tag) (s : KState) (a : Action) : Json :=
  obj ((actionRow tag s a).map fun (dst,w) => (ambientName dst,str (weightString w)))

def exportRawInputs (tag : Tag) : Json :=
  obj [
    ("action_distributions",obj (kernel.map fun s =>
      (stateName s,obj (actions.map fun a => (actionName a,exportActionRow tag s a))))),
    ("public_channel_rule",str (publicChannelRuleName (publicChannelRule tag))),
    ("tick_increment",obj (kernel.map fun s =>
      (stateName s,obj (actions.map fun a => (actionName a,nat (tickIncrement tag s a)))))),
    ("record_writer_available",obj (routeIds.map fun id =>
      (routeName id,bool (recordWriterAvailable tag id)))),
    ("resources",obj [("recharge_available_after_withdrawal",
      bool (rechargeAvailableAfterWithdrawal tag))])]

def exportEvent (e : Event) : Json := obj [
  ("id",str (eventName e.id)),("from",str (stageName e.fromStage)),
  ("to",str (stageName e.toStage)),("source_support",bool e.sourceSupport),
  ("target_support",bool e.targetSupport),("atomic",bool e.atomic),
  ("strict_step",bool e.strictStep)]

def exportRoute (r : Route) : Json := obj [
  ("id",str (routeName r.id)),("source_history",str (historyName r.sourceHistory)),
  ("events",stringList (r.eventPath.map eventName))]

def exportCorridor : Json := obj [
  ("stages",stringList (stages.map stageName)),
  ("events",arr (events.map exportEvent)),
  ("paths",arr (routes.map exportRoute)),
  ("content_counterfactuals",arr (contentCounterfactuals.map fun h =>
    obj [("source_history",str (historyName h))])),
  ("interventions",stringList (supportInterventions.map supportInterventionName)),
  ("realized_stages",stringList (realizedStages.map stageName)),
  ("future_route_readout",obj [
    ("rule",str (routeReadoutRuleName routeReadout)),
    ("owner",str (tagName routeReadoutOwner))])]

def exportReceiver : Json := obj [
  ("latent_target",obj [
    ("factor_state",str (stateName receiver.latentFactor)),
    ("funded_receiver",bool receiver.funded),
    ("initial_budget_tokens",nat receiver.initialBudget)]),
  ("activation",obj [
    ("source_present",bool receiver.sourcePresent),
    ("target_receiver_funded",bool receiver.targetReceiverFunded),
    ("mixed_event_required",bool receiver.mixedEventRequired)]),
  ("content",obj [
    ("position_rule",str (contentRulePositionName receiver.contentRule)),
    ("phase_rule",str (contentRulePhaseName receiver.contentRule)),
    ("history_overrides",obj [])]),
  ("route_register_write",obj [("rule",str (registerRuleName receiver.registerRule))])]

def exportLedger : Json := obj [
  ("action_cost_tokens",nat ledger.actionCost),
  ("recharge_tokens_per_action",nat ledger.rechargePerAction),
  ("initial_budget_tokens",nat ledger.initialBudget),
  ("source_available_after_withdrawal",bool ledger.sourceAvailableAfterWithdrawal),
  ("owner_by_tag",obj (tags.map fun tag => (tagName tag,str (tagName (resourceOwner tag)))))]

def exportC4 : Json := obj [
  ("current_channels",stringList (currentChannels.map channelName)),
  ("candidate_connector_history",stringList (connectorHistory.map stateName)),
  ("candidate_hidden_pair",stringList [stateName hiddenPair.1,stateName hiddenPair.2]),
  ("expanded_channel",str (channelName expandedChannel))]

def exportProtocolEdge (e : ProtocolEdge) : Json := obj [
  ("from",str (vertexName e.fromVertex)),("to",str (vertexName e.toVertex)),
  ("channel",str (creditChannelName e.channel))]

def exportProtocol (tag : Tag) (id : ProtocolId) : Json := obj [
  ("tag",str (tagName tag)),("id",str (protocolName id)),
  ("owner",Lean.toJson (provenanceOwnerName (protocolOwner tag id))),
  ("housing",Lean.toJson (provenanceOwnerName (protocolHousing tag id))),
  ("channel",str (protocolChannel id)),("kind",str (protocolKind id)),
  ("edges",arr ((protocolEdges id).map exportProtocolEdge))]

def exportC5 : Json := obj [
  ("vertices",stringList (vertices.map vertexName)),
  ("history_anchor",obj [
    ("u",str (historyName (historyAnchor .u))),
    ("v",str (historyName (historyAnchor .v))),
    ("w",str (historyName (historyAnchor .w)))]),
  ("protocols",arr (tags.flatMap fun tag =>
    protocolIds.map (exportProtocol tag)))]

def exportC6 : Json := obj [
  ("future_alphabet",stringList (futureAlphabet.map fun a =>
    "canonical_action_" ++ actionName a)),
  ("candidate_merged_pair",stringList [stateName candidateMergedPair.1,
    stateName candidateMergedPair.2]),
  ("route_record_owner",str (tagName routeRecordOwner)),
  ("future_interface",stringList (futureInterface.map observableName))]

private def exportCoupling (id : AssemblageId) : Json :=
  arr ((coupling id).map fun (i,j) => arr [nat i.val,nat j.val])
private def exportAssemblage (id : AssemblageId) : Json := obj [
  ("id",str (assemblageName id)),
  ("left",stringList (twoSlots.map fun i => historyName (leftBranch i))),
  ("right",stringList (twoSlots.map fun i => historyName (rightBranch i))),
  ("coupling",exportCoupling id)]

def exportC7Tag (tag : Tag) : Json := obj [
  ("assemblages",arr (assemblageIds.map exportAssemblage)),
  ("joint_observables",stringList ((jointObservables tag).map jointObservableName)),
  ("reassembly",arr (assemblageIds.map fun id => obj [
    ("assemblage",str (assemblageName id)),
    ("coupling",str (assemblageName (reassembly tag id)))])),
  ("branches",obj [
    ("left",stringList (twoSlots.map fun i => historyName (leftBranch i))),
    ("right",stringList (twoSlots.map fun i => historyName (rightBranch i)))]),
  ("admissible_couplings",obj (assemblageIds.map fun id =>
    (assemblageName id,Lean.toJson ((coupling id).map fun pair => pair.2.val))))]

def exportCoordinate (c : Coordinate) : Json := obj [
  ("tag",str (tagName c.tag)),("state",str (stateName c.state)),
  ("clause",str (clauseName c.clause)),("coordinate",str (coordinateLabel c)),
  ("primitive_refs",stringList ((primitiveRefs c.tag c.clause).map
    (primitivePath c.tag)))]

def exportStagedMap (row : Clause × Tag × Tag) : Json := obj [
  ("clause",str (clauseName row.1)),
  ("source_ref",str (tagName row.2.1 ++ ":*:" ++ clauseName row.1)),
  ("target_ref",str (tagName row.2.2 ++ ":*:" ++ clauseName row.1))]

def exportTaggedPNums : Json :=
  obj (tags.map fun tag =>
    (tagName tag, Lean.toJson (kernel.map fun s => kernel.map (taggedPNum tag s))))

def exportT1Inputs : Json := obj [
  ("C",Lean.toJson (indices.map fun i => sevenSlots.map (cIndicator i))),
  ("U",Lean.toJson (sevenSlots.map fun k =>
    indices.map fun j => toString ((uPrototypeNum k j : Rat) / 2))),
  ("hazards",Lean.toJson hazardPositions),
  ("hazard_flags",obj (ambientStates.map fun s =>
    (ambientName s,bool (isLethalHazard s)))),
  ("slip_hold",rat ((slipHoldNum : Rat) / slipDen)),
  ("slip_advance",rat ((slipAdvanceNum : Rat) / slipDen)),
  ("C1",obj [
    ("tau",nat c1Tau),("epsilon",rat c1Epsilon),
    ("retention_threshold",rat c1RetentionThreshold),
    ("published_pi",stringList (indices.map fun i => toString (pi i))),
    ("published_core_mass",rat (coreMass pi)),
    ("published_tv",rat (tvFromCoreUniform pi)),
    ("published_defect",rat (defect E2eps))])]

def snapshot : Json := obj [
  ("t1_inputs",exportT1Inputs),
  ("carrier",obj [
    ("tags",stringList (tags.map tagName)),
    ("kernel",stringList (kernel.map stateName)),
    ("core",stringList (core.map stateName)),
    ("ambient_states",stringList (ambientStates.map ambientName)),
    ("public_f",Lean.toJson (kernel.map publicPosition)),
    ("canonical_policy",stringList (kernel.map fun s => actionName (canonicalAction s))),
    ("m_classes",Lean.toJson (indices.map mClass)),
    ("p_num",Lean.toJson (indices.map fun i => indices.map (pNum i))),
    ("cu_num",Lean.toJson (indices.map fun i => indices.map (CU.num i))),
    ("tagged_p_num",exportTaggedPNums)]),
  ("histories",obj (historyIds.map fun id =>
    (historyName id,stringList ((sourceHistory id).map stateName)))),
  ("bridge_frontier",stringList (bridgeFrontier.map historyName)),
  ("strict_source_edge",stringList [stateName strictSourceEdge.1,
    stateName strictSourceEdge.2]),
  ("same_class_pair",stringList [historyName sameClassPair.1,
    historyName sameClassPair.2]),
  ("different_class_pair",stringList [historyName differentClassPair.1,
    historyName differentClassPair.2]),
  ("corridor",exportCorridor),("receiver",exportReceiver),
  ("recognition_status",str (recognitionStatusName recognitionStatus)),
  ("maintenance",exportLedger),("c4",exportC4),("c5",exportC5),
  ("c6",exportC6),("c7",obj (tags.map fun tag =>
    (tagName tag,exportC7Tag tag))),
  ("raw_inputs",obj (tags.map fun tag =>
    (tagName tag,exportRawInputs tag))),
  ("local_assignments",arr (coordinates.map exportCoordinate)),
  ("staged_clause_map",arr (stagedClauseMap.map exportStagedMap)),
  ("route_register",obj (routeIds.map fun id =>
    (routeName id,obj [
      ("source_history",stringList ((routeRegister id).1.map stateName)),
      ("events",stringList ((routeRegister id).2.map eventName))])))]

end CSTTT.POS04
