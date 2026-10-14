import CSTTT.POS04.RouteMemory
import CSTTT.POS04.C4C5
import CSTTT.POS04.C6

/-! POS-04 history bridge and endpoint link, frozen
`audit/M3_model_spec.md:30-31,40-48`. The frontier and all laws below are
computed from T1 action support, event paths, the raw receiver factor map,
and resources. Corridor realization belongs to the typed endpoint link.
The linked endpoint is a target factor state at a realized target-only exit,
with equal *computed* source/target M and target-owned funding. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

def bridgeHistoriesSupported : Bool :=
  !bridgeFrontier.isEmpty && bridgeFrontier.all (fun id =>
    (sourceHistory id).length ≥ 2 &&
    supportedHistory .source id && supportedHistory .target id)

def bridgeStrictEdge : Bool :=
  strictSourceEdge.1 != strictSourceEdge.2 &&
  taggedPNum .source strictSourceEdge.1 strictSourceEdge.2 > 0 &&
  bridgeFrontier.any (fun id =>
    strictSourceEdge ∈ ((sourceHistory id).zip ((sourceHistory id).drop 1)))

def bridgeSuccessorLaw : Bool :=
  kernel.all (fun s => actions.all (fun a =>
    actionRow .source s a == actionRow .target s a)) &&
  bridgeFrontier.all (fun id =>
    ((sourceHistory id).zip ((sourceHistory id).drop 1)).all
      (fun pair => taggedPNum .source pair.1 pair.2 > 0 &&
        taggedPNum .source pair.1 pair.2 ==
          taggedPNum .target pair.1 pair.2))

def bridgeTickLaw : Bool :=
  kernel.all fun s => actions.all fun a =>
    tickIncrement .source s a == tickIncrement .target s a &&
    tickIncrement .source s a == 1

def historyProgress (tag : Tag) (id : HistoryId) : Nat :=
  (((sourceHistory id).zip ((sourceHistory id).drop 1)).filter
    (fun pair => taggedPNum tag pair.1 pair.2 > 0)).length

def bridgeProgressLaw : Bool :=
  bridgeFrontier.all (fun id =>
    historyProgress .source id == (sourceHistory id).length - 1 &&
    historyProgress .target id == historyProgress .source id)

def historyOccurrences (tag : Tag) (id : HistoryId) :
    List (Nat × Option TaggedState) :=
  (List.range (sourceHistory id).length).map fun i =>
    (i, (sourceHistory id)[i]?.map (tag,·))

def bridgeOrderLaw : Bool :=
  bridgeFrontier.all (fun id =>
    historyOccurrences .target id ==
      (historyOccurrences .source id).map
        (fun pair => (pair.1,pair.2.map swapTagged)))

def bridgeRecordLaw : Bool :=
  !routeIds.isEmpty && routeIds.all (fun id =>
    recordWriterAvailable .source id && recordWriterAvailable .target id)

def bridgeRouteLaw (routeV : RouteVariant) : Prop :=
  RouteMemoryPass routeV ∧
  (∀ id ∈ routeIds,
    (routeOf id).sourceHistory ∈ bridgeFrontier ∧
    routeReferencesResolve id = true ∧ routeEventsCompose id = true)

def bridgeOwnerLaw : Bool :=
  resourceOwner .source == .source &&
  resourceOwner .target == .target &&
  swapTag (resourceOwner .source) == resourceOwner .target &&
  routeReadoutOwner == .target

def bridgeMappedFrontier (rv : ReceiverVariant) : Bool :=
  bridgeFrontier.all fun id =>
    match sourceTerminalM id, receiverFactor rv id with
    | some sourceM, some target => decide (sourceM = rawM .target target)
    | _, _ => false

def BridgePass (rv : ReceiverVariant) (routeV : RouteVariant) : Prop :=
  RepresentativeIndependence rv ∧
  bridgeHistoriesSupported = true ∧ bridgeStrictEdge = true ∧
  bridgeSuccessorLaw = true ∧ bridgeTickLaw = true ∧
  bridgeProgressLaw = true ∧ bridgeOrderLaw = true ∧
  bridgeRecordLaw = true ∧ bridgeRouteLaw routeV ∧
  bridgeOwnerLaw = true ∧ bridgeMappedFrontier rv = true

theorem bridge_support_and_strict_edge :
    bridgeHistoriesSupported = true ∧ bridgeStrictEdge = true := by decide

theorem bridge_transition_tick_progress_order_laws :
    bridgeSuccessorLaw = true ∧ bridgeTickLaw = true ∧
    bridgeProgressLaw = true ∧ bridgeOrderLaw = true := by decide

theorem bridge_canonical_successor_probabilities (s t : KState) :
    rowWeight (actionRow .source s (canonicalAction s)) t =
      taggedPNum .target s t := by
  rw [canonical_action_row_agrees_with_tagged_P .source s t]
  exact tag_swap_preserves_P .source s t

theorem bridge_record_owner_route_laws :
    bridgeRecordLaw = true ∧ bridgeOwnerLaw = true ∧
    bridgeRouteLaw .positive := by
  refine ⟨by decide, by decide, route_memory_positive, ?_⟩
  intro id _
  cases id <;> decide

theorem bridge_mapped_frontier :
    bridgeMappedFrontier .positive = true := by decide

theorem bridge_positive : BridgePass .positive .positive := by
  refine ⟨representative_independence_positive,
    bridge_support_and_strict_edge.1, bridge_support_and_strict_edge.2,
    bridge_transition_tick_progress_order_laws.1,
    bridge_transition_tick_progress_order_laws.2.1,
    bridge_transition_tick_progress_order_laws.2.2.1,
    bridge_transition_tick_progress_order_laws.2.2.2,
    bridge_record_owner_route_laws.1,
    bridge_record_owner_route_laws.2.2,
    bridge_record_owner_route_laws.2.1,
    bridge_mapped_frontier⟩

def routeExitLinked (rv : ReceiverVariant) (cv : CorridorVariant)
    (id : RouteId) : Bool :=
  let path := (routeOf id).eventPath
  let exitEvent := corridorEvent cv .exit
  match path.getLast?, (sourceHistory (routeOf id).sourceHistory).getLast?,
      receiverOutput rv cv (routeOf id).sourceHistory with
  | some last, some sourceEnd, some targetEnd =>
      last == .exit && exitEvent.id == last && exitEvent.atomic &&
      !exitEvent.sourceSupport && exitEvent.targetSupport &&
      exitEvent.toStage == .targetExit &&
      exitEvent.fromStage ∈ corridorRealized cv &&
      exitEvent.toStage ∈ corridorRealized cv &&
      sourceEnd ∈ kernel && targetEnd ∈ c8Greatest .funded .target &&
      decide (rawM .source sourceEnd = rawM .target targetEnd) &&
      resourceOwner .target == .target
  | _, _, _ => false

/-- Typed link: each corridor path ends in the realized target-only exit;
its covered source terminal and the receiver's target factor state share the
computed predictive class, while the target is in its funded viable kernel. -/
def TypedEndpointLink (rv : ReceiverVariant) (cv : CorridorVariant)
    (routeV : RouteVariant) : Prop :=
  CorridorPass cv ∧ BridgePass rv routeV ∧ ContentSensitivity rv cv ∧
  receiverActive rv cv = true ∧
  routeIds.length ≥ 2 ∧
  (∀ id ∈ routeIds, routeExitLinked rv cv id = true)

theorem route_exit_links_positive :
    ∀ id ∈ routeIds, routeExitLinked .positive .positive id = true := by
  intro id _
  cases id <;> decide

theorem typed_endpoint_link_positive :
    TypedEndpointLink .positive .positive .positive := by
  exact ⟨corridor_positive, bridge_positive, content_sensitive_positive,
    receiver_positive_active, by decide, route_exit_links_positive⟩

theorem neg_bridge_rep_fails : ¬ BridgePass .bridgeRep .positive := by
  intro h
  exact neg_bridge_rep_independence_fails h.1

/-- `NEG-PRELOADED-COPY` edits only raw receiver content rules. Isolation
holds by structural independence: clause predicates take no receiver-content
argument. This theorem is not an independent sensitivity test. -/
theorem neg_preloaded_copy_no_clause_side_effects :
    receiverFor .preloadedCopy = receiver ∧
    (∀ tag : Tag,
      taggedCoreMass tag = 77/80 ∧
      C2Pass (positiveLowerRule tag) tag ∧
      C3Pass .positive (positiveLowerRule tag) tag ∧
      C4Surrogate .positive tag ∧ C5Surrogate .positive tag ∧
      C6Pass .positive tag ∧ C7Pass .positive tag ∧
      C8Pass .funded tag) := by
  refine ⟨neg_preloaded_copy_activation_unchanged.1, ?_⟩
  intro tag
  exact ⟨c1_core_mass_each_tag tag, c2_split_each_tag tag,
    c3_each_tag tag, c4_surrogate_each_tag tag,
    c5_surrogate_each_tag tag, c6_each_tag tag,
    c7_each_tag tag, c8_funded_each_tag tag⟩

theorem bridge_gap_preserves_local_laws : BridgePass .positive .positive :=
  bridge_positive

theorem typed_link_source_absent_fails :
    ¬ TypedEndpointLink .sourceAbsent .positive .positive := by
  intro h
  have ha := h.2.2.2.1
  rw [neg_activation_source_absent] at ha
  contradiction

theorem bridge_route_memory_fails : ¬ BridgePass .positive .negMemory := by
  intro h
  rcases h with ⟨_,_,_,_,_,_,_,_,hr,_,_⟩
  exact neg_route_memory_fails hr.1

theorem bridge_underfund_fails : ¬ BridgePass .sourceAbsent .underfund := by
  intro h
  rcases h with ⟨_,_,_,_,_,_,_,_,hr,_,_⟩
  exact route_underfund_fails hr.1

theorem bridge_preloaded_copy_fails : ¬ BridgePass .preloadedCopy .positive := by
  intro h
  have hn : bridgeMappedFrontier .preloadedCopy = false := by decide
  rcases h with ⟨_,_,_,_,_,_,_,_,_,_,hp⟩
  rw [hn] at hp
  contradiction

theorem bridge_source_absent_preserves_local_laws :
    BridgePass .sourceAbsent .positive := by
  simpa [BridgePass, RepresentativeIndependence, bridgeMappedFrontier,
    receiverFactor, receiverRaw, receiverOverride,
    receiverPositionRule, receiverPhaseRule] using bridge_positive

def TargetAutonomy (v : C8Variant) (r : Receiver) : Prop :=
  r.sourcePresent = false ∧ C8ReceiverPass r v .target ∧
  c8ReceiverGreatest r v .target ≠ []

theorem target_only_autonomy_positive :
    TargetAutonomy .funded c8WithdrawnReceiver := by
  refine ⟨c8_target_only_after_withdrawal.1,
    c8_target_only_after_withdrawal.2.2.2, ?_⟩
  rw [c8_target_only_after_withdrawal.2.1]
  decide

theorem neg_autonomy_withdraw_empty :
    c8ReceiverGreatest c8WithdrawnReceiver .negUnderfund .target = [] := by
  rw [c8_target_receiver_greatest_independent_of_source]
  exact neg_c8_underfund_empty

theorem neg_autonomy_withdraw_fails :
    ¬ TargetAutonomy .negUnderfund c8WithdrawnReceiver := by
  intro h
  have hn := h.2.2
  rw [neg_autonomy_withdraw_empty] at hn
  exact hn rfl

private theorem content_detached_pass :
    ContentSensitivity .positive .detached := by
  simp only [ContentSensitivity]
  refine ⟨by decide, by decide, by decide, by decide,
    .p1w0, .p1w1, ?_⟩
  decide

private theorem content_bridge_rep_pass :
    ContentSensitivity .bridgeRep .positive := by
  simp only [ContentSensitivity]
  refine ⟨by decide, by decide, by decide, by decide,
    .p1w0, .p1w1, ?_⟩
  decide

private theorem typed_link_corridor_failure (rv : ReceiverVariant)
    (cv : CorridorVariant) (routeV : RouteVariant)
    (h : ¬ CorridorPass cv) : ¬ TypedEndpointLink rv cv routeV :=
  fun link => h link.1

private theorem typed_link_bridge_failure (rv : ReceiverVariant)
    (cv : CorridorVariant) (routeV : RouteVariant)
    (h : ¬ BridgePass rv routeV) : ¬ TypedEndpointLink rv cv routeV :=
  fun link => h link.2.1

private theorem typed_link_content_failure (rv : ReceiverVariant)
    (cv : CorridorVariant) (routeV : RouteVariant)
    (h : ¬ ContentSensitivity rv cv) : ¬ TypedEndpointLink rv cv routeV :=
  fun link => h link.2.2.1

/-! Each theorem below gives the exact projection of the frozen
`audit/M3b_results.json` `lane_pass_changes` onto the L7 lanes: corridor,
bridge, route, content, autonomy, and typed endpoint link. `staged` and
`handoff` are later assembly checks, outside L7. Positive conjuncts make
the absence of a side effect explicit. -/

theorem neg_corridor_detached_lane_attribution :
    ¬ CorridorPass .detached ∧ BridgePass .positive .positive ∧
    RouteMemoryPass .positive ∧ ContentSensitivity .positive .detached ∧
    TargetAutonomy .funded c8WithdrawnReceiver ∧
    ¬ TypedEndpointLink .positive .detached .positive :=
  ⟨neg_corridor_detached_fails, bridge_positive, route_memory_positive,
    content_detached_pass, target_only_autonomy_positive,
    typed_link_corridor_failure _ _ _ neg_corridor_detached_fails⟩

theorem neg_corridor_gap_lane_attribution :
    ¬ CorridorPass .gap ∧ BridgePass .positive .positive ∧
    RouteMemoryPass .positive ∧ ¬ ContentSensitivity .positive .gap ∧
    TargetAutonomy .funded c8WithdrawnReceiver ∧
    ¬ TypedEndpointLink .positive .gap .positive :=
  ⟨neg_corridor_gap_fails, bridge_positive, route_memory_positive,
    receiver_missing_realized_mixed_event_fails,
    target_only_autonomy_positive,
    typed_link_corridor_failure _ _ _ neg_corridor_gap_fails⟩

theorem neg_bridge_rep_lane_attribution :
    CorridorPass .positive ∧ ¬ BridgePass .bridgeRep .positive ∧
    RouteMemoryPass .positive ∧ ContentSensitivity .bridgeRep .positive ∧
    TargetAutonomy .funded c8WithdrawnReceiver ∧
    ¬ TypedEndpointLink .bridgeRep .positive .positive :=
  ⟨corridor_positive, neg_bridge_rep_fails, route_memory_positive,
    content_bridge_rep_pass, target_only_autonomy_positive,
    typed_link_bridge_failure _ _ _ neg_bridge_rep_fails⟩

theorem neg_route_memory_lane_attribution :
    CorridorPass .positive ∧ ¬ BridgePass .positive .negMemory ∧
    ¬ RouteMemoryPass .negMemory ∧ ContentSensitivity .positive .positive ∧
    TargetAutonomy .funded c8WithdrawnReceiver ∧
    ¬ TypedEndpointLink .positive .positive .negMemory :=
  ⟨corridor_positive, bridge_route_memory_fails, neg_route_memory_fails,
    content_sensitive_positive, target_only_autonomy_positive,
    typed_link_bridge_failure _ _ _ bridge_route_memory_fails⟩

theorem neg_activation_source_absent_lane_attribution :
    CorridorPass .positive ∧ BridgePass .sourceAbsent .positive ∧
    RouteMemoryPass .positive ∧ ¬ ContentSensitivity .sourceAbsent .positive ∧
    TargetAutonomy .funded c8WithdrawnReceiver ∧
    ¬ TypedEndpointLink .sourceAbsent .positive .positive :=
  ⟨corridor_positive, bridge_source_absent_preserves_local_laws,
    route_memory_positive, source_absent_content_fails,
    target_only_autonomy_positive, typed_link_source_absent_fails⟩

theorem neg_autonomy_withdraw_lane_attribution :
    CorridorPass .positive ∧ ¬ BridgePass .sourceAbsent .underfund ∧
    ¬ RouteMemoryPass .underfund ∧
    ¬ ContentSensitivity .sourceAbsent .positive ∧
    ¬ TargetAutonomy .negUnderfund c8WithdrawnReceiver ∧
    ¬ TypedEndpointLink .sourceAbsent .positive .underfund :=
  ⟨corridor_positive, bridge_underfund_fails, route_underfund_fails,
    source_absent_content_fails, neg_autonomy_withdraw_fails,
    typed_link_bridge_failure _ _ _ bridge_underfund_fails⟩

theorem neg_preloaded_copy_lane_attribution :
    CorridorPass .positive ∧ ¬ BridgePass .preloadedCopy .positive ∧
    RouteMemoryPass .positive ∧
    ¬ ContentSensitivity .preloadedCopy .positive ∧
    TargetAutonomy .funded c8WithdrawnReceiver ∧
    ¬ TypedEndpointLink .preloadedCopy .positive .positive :=
  ⟨corridor_positive, bridge_preloaded_copy_fails, route_memory_positive,
    neg_preloaded_copy_content_fails, target_only_autonomy_positive,
    typed_link_bridge_failure _ _ _ bridge_preloaded_copy_fails⟩

end CSTTT.POS04
