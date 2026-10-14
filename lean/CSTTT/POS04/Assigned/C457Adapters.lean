import CSTTT.POS04.Assigned.C457Locality
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit

/-- A pure cell transformation preserves absence and cannot create a verdict. -/
def mapCell (a : Assignment) (k : Cell) (f : Value k → Value k) : Assignment :=
  put a k ((a k).map f)

theorem mapCell_complete {a : Assignment} (k : Cell) (f : Value k → Value k)
    {scope : List Cell} (h : Complete scope a) : Complete scope (mapCell a k f) := by
  intro j hj
  by_cases he : j = k
  · subst j
    simpa [mapCell] using h k hj
  · simpa [mapCell,put,he] using h j hj

def expose4 (a : Assignment) := mapCell a .channels (fun (cs : List CurrentChannel) => cs ++ [.canonicalM])
def external5 (a : Assignment) := mapCell a (.protocols .target) (fun p =>
  {p with edges := fun id => if id = .clockwise then forwardEdges .other else p.edges id
          owner := fun id => if id = .clockwise then .external else p.owner id})
def internalized5 (a : Assignment) := mapCell a (.protocols .target) (fun p =>
  {p with housing := fun id => if id = .scheduled then .target else p.housing id})
def aggregate7 (a : Assignment) :=
  mapCell (mapCell a (.joint .source) (fun j => {j with observables := []}))
    (.joint .target) (fun j => {j with observables := []})
def uncoupleAt7 (a : Assignment) (tag : Tag) := mapCell a (.joint tag) (fun j =>
  {j with coupling := fun id => if id = .crossed then coupling .diagonal else j.coupling id
          reassembly := fun id => if id = .crossed then .diagonal else j.reassembly id})
def transportBreak7 (a : Assignment) := uncoupleAt7 a .target
def uncoupled7 (a : Assignment) := uncoupleAt7 (uncoupleAt7 a .source) .target

def controls5 (v : C5Variant) : Assignment :=
  match v with
  | .positive => canonical
  | .negExternal => external5 canonical
  | .negInternalized => internalized5 canonical
  | .missingSelfEdge =>
    mapCell (mapCell canonical (.protocols .source) (fun p =>
      {p with edges := fun id => if id = .clockwise then (forwardEdges .self).drop 1 else p.edges id}))
      (.protocols .target) (fun p =>
        {p with edges := fun id => if id = .clockwise then (forwardEdges .self).drop 1 else p.edges id})
def controls7 (v : C7Variant) : Assignment :=
  match v with
  | .positive => canonical
  | .negAggregate => aggregate7 canonical
  | .negTransport => transportBreak7 canonical
  | .negUncoupled => uncoupled7 canonical
  | .missingMixedEvent => put canonical .realized (some [.sourceLive,.targetExit])
  | .sourceAbsent => mapCell canonical .receiverInput (fun r => {r with sourcePresent := false})

/-- Exact canonical record; unused fields of any clause's common decoder are
canonical totalization values. The gate prevents absent required fields. -/
def canonicalExtra (tag : Tag) : ExtraInputs :=
  ⟨legacyInputs .positive .positive .position tag,currentChannels,
   ⟨protocolEdges,protocolOwner tag,protocolHousing tag⟩,
   ⟨leftBranch,rightBranch,coupling,reassembly tag,jointObservables tag⟩,
   sourceHistory,events,realizedStages,receiver,routes,recordWriterAvailable⟩

theorem canonical_extra (tag : Tag) (c : Clause) :
    clauseExtra canonical tag c = canonicalExtra tag := by
  cases tag <;> cases c <;> rfl

theorem canonical_inputs (tag : Tag) (c : Clause) :
    clauseInputs canonical tag c = legacyInputs .positive .positive .position tag := by
  cases tag <;> cases c <;> rfl

theorem canonical_ready (tag : Tag) (c : Clause) : Ready canonical tag c := by
  refine ⟨canonical_complete _,?_⟩
  rw [canonical_inputs]
  exact legacy_rows_valid _ _ _ _

theorem canonical_gate4 (tag : Tag) : C4Gate canonical tag := by
  unfold C4Gate
  rw [canonical_extra]
  exact ⟨canonical_ready tag .c4,legacy_M_link _ _ _ _,
    by cases tag <;> rfl,by cases tag <;> rfl,by cases tag <;> decide⟩

theorem canonical_gate5 (tag : Tag) : C5Gate canonical tag := canonical_ready tag .c5

theorem canonical_gate7 (tag : Tag) : C7Gate canonical tag := by
  exact ⟨canonical_ready tag .c7,by rw [canonical_extra]; rfl,
    by rw [canonical_extra]; cases tag <;> decide⟩

/-- The raw support rule has no vacuous empty history. On the declared paths
it is equal to the legacy supportedHistory check. -/
theorem canonical_supported (tag : Tag) (id : HistoryId) :
    historySupported (canonicalExtra tag) id = supportedHistory tag id := by
  cases tag <;> cases id <;> decide

theorem canonical_credit_link (tag : Tag) (id : ProtocolId) :
    credit5 (canonicalExtra tag) id = c5Credit .positive tag id := rfl

theorem canonical_pairing_link (tag : Tag) (id : AssemblageId) (l r : HistoryId) :
    pairing7 (canonicalExtra tag) id l r = jointPairing .positive tag id l r := by
  unfold pairing7 jointPairing
  have hc : pairCount7 (canonicalExtra tag) id l r = c7PairCount .positive tag id l r := by
    cases tag <;> cases id <;> cases l <;> cases r <;> decide
  rw [hc]
  cases tag <;> cases id <;> rfl

theorem c4_canonical_equivalence (tag : Tag) :
    C4Accept canonical tag ↔ C4Surrogate .positive tag := by
  unfold C4Accept
  rw [and_iff_right (canonical_gate4 tag),canonical_extra]
  rfl

theorem c5_canonical_equivalence (tag : Tag) :
    C5Accept canonical tag ↔ C5Surrogate .positive tag := by
  unfold C5Accept
  rw [and_iff_right (canonical_gate5 tag),canonical_extra]
  simp only [C5Rule,C5Surrogate,Owner5,C5OwnerConsistent,Anchors5,C5AnchorsSupported,
    canonical_supported,canonical_credit_link]
  rfl

theorem c7_canonical_equivalence (tag : Tag) :
    C7Accept canonical tag ↔ C7Pass .positive tag := by
  unfold C7Accept
  rw [and_iff_right (canonical_gate7 tag),canonical_extra]
  have hn : C7Rule (canonicalExtra tag) := by
    cases tag <;> simp only [C7Rule,Local7,Histories7,Strict7,Operational7] <;> decide
  exact ⟨fun _ => c7_each_tag tag,fun _ => hn⟩

theorem canonical_c457 (tag : Tag) :
    C4Accept canonical tag ∧ C5Accept canonical tag ∧ C7Accept canonical tag :=
  ⟨(c4_canonical_equivalence tag).mpr (c4_surrogate_each_tag tag),
   (c5_canonical_equivalence tag).mpr (c5_surrogate_each_tag tag),
   (c7_canonical_equivalence tag).mpr (c7_each_tag tag)⟩

/-- The full HIDD non-exposure target remains false. This positive theorem
about exposure documents the negative result; C4 is only a surrogate. -/
theorem assigned_full_HIDD_nonexposure_fails (tag : Tag) :
    ¬ (¬ Exposed4 (clauseExtra canonical tag .c4)) := by
  intro h
  exact h (canonical_c457 tag).1.2.2.2

theorem controls5_complete (v : C5Variant) (scope : List Cell) :
    Complete scope (controls5 v) := by
  intro k hk
  clear hk
  cases v <;> cases k <;> try rfl
  all_goals rename_i tag; cases tag <;> rfl

theorem controls7_complete (v : C7Variant) (scope : List Cell) :
    Complete scope (controls7 v) := by
  intro k hk
  clear hk
  cases v <;> cases k <;> try rfl
  all_goals rename_i tag; cases tag <;> rfl

theorem controls5_inputs (v : C5Variant) (tag : Tag) :
    clauseInputs (controls5 v) tag .c5 = legacyInputs .positive .positive .position tag := by
  cases v <;> cases tag <;> rfl

theorem controls7_inputs (v : C7Variant) (tag : Tag) :
    clauseInputs (controls7 v) tag .c7 = legacyInputs .positive .positive .position tag := by
  cases v <;> cases tag <;> rfl

theorem controls5_gate (v : C5Variant) (tag : Tag) : C5Gate (controls5 v) tag := by
  refine ⟨controls5_complete _ _,?_⟩
  rw [controls5_inputs]
  exact legacy_rows_valid _ _ _ _

theorem controls7_gate (v : C7Variant) (tag : Tag) : C7Gate (controls7 v) tag := by
  refine ⟨⟨controls7_complete _ _,?_⟩,?_,?_⟩
  · rw [controls7_inputs]; exact legacy_rows_valid _ _ _ _
  · change (clauseInputs (controls7 v) tag .c7).publishedP = pNum
    rw [controls7_inputs]; rfl
  · cases v <;> cases tag <;> decide

theorem expose4_inputs (tag : Tag) :
    clauseInputs (expose4 canonical) tag .c4 = legacyInputs .positive .positive .position tag := by
  cases tag <;> rfl

theorem expose4_gate (tag : Tag) : C4Gate (expose4 canonical) tag := by
  refine ⟨⟨mapCell_complete _ _ (canonical_complete _),?_⟩,?_,?_,?_,?_⟩
  · rw [expose4_inputs]; exact legacy_rows_valid _ _ _ _
  · change MLinked (clauseInputs (expose4 canonical) tag .c4)
    rw [expose4_inputs]; exact legacy_M_link _ _ _ _
  · cases tag <;> rfl
  · cases tag <;> rfl
  · cases tag <;> decide

/-- Exact generator/credit bridge for every legacy protocol intervention. -/
theorem controls5_credit (v : C5Variant) (tag : Tag) (id : ProtocolId) :
    credit5 (clauseExtra (controls5 v) tag .c5) id = c5Credit v tag id := by
  cases v <;> cases tag <;> cases id <;> decide

theorem controls5_raw_tables (v : C5Variant) (tag : Tag) (id : ProtocolId) :
    (clauseExtra (controls5 v) tag .c5).protocols.edges id = c5Edges v tag id ∧
    (clauseExtra (controls5 v) tag .c5).protocols.owner id = c5Owner v tag id ∧
    (clauseExtra (controls5 v) tag .c5).protocols.housing id = c5Housing v tag id := by
  cases v <;> cases tag <;> cases id <;> decide

theorem controls5_histories (v : C5Variant) (tag : Tag) (id : HistoryId) :
    historySupported (clauseExtra (controls5 v) tag .c5) id = supportedHistory tag id := by
  cases v <;> cases tag <;> cases id <;> decide

theorem c5_controls_equivalence (v : C5Variant) (tag : Tag) :
    C5Accept (controls5 v) tag ↔ C5Surrogate v tag := by
  unfold C5Accept
  rw [and_iff_right (controls5_gate v tag)]
  simp only [C5Rule,C5Surrogate,Owner5,C5OwnerConsistent,Anchors5,C5AnchorsSupported,
    controls5_credit,controls5_histories,(controls5_raw_tables v tag _).2.1]

theorem c5_transport_equivalence (v : C5Variant) :
    C5Transport (controls5 v) ↔ C5RawTransport v := by
  unfold C5Transport
  rw [and_iff_right (controls5_gate v .source),and_iff_right (controls5_gate v .target)]
  simp only [C5RawTransport,(controls5_raw_tables v _ _).1,
    (controls5_raw_tables v _ _).2.1,(controls5_raw_tables v _ _).2.2]

theorem controls7_tables (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    (clauseExtra (controls7 v) tag .c7).joint.coupling id = c7Coupling v tag id ∧
    (clauseExtra (controls7 v) tag .c7).joint.reassembly id = c7Reassembly v tag id ∧
    (clauseExtra (controls7 v) tag .c7).joint.observables = c7Observables v tag := by
  cases v <;> cases tag <;> cases id <;> decide

theorem controls7_count (v : C7Variant) (tag : Tag) (id : AssemblageId) (l r : HistoryId) :
    pairCount7 (clauseExtra (controls7 v) tag .c7) id l r = c7PairCount v tag id l r := by
  cases v <;> cases tag <;> cases id <;> cases l <;> cases r <;> decide

theorem controls7_pairing (v : C7Variant) (tag : Tag) (id : AssemblageId) (l r : HistoryId) :
    pairing7 (clauseExtra (controls7 v) tag .c7) id l r = jointPairing v tag id l r := by
  simp only [pairing7,jointPairing,controls7_count,(controls7_tables v tag id).1]

theorem controls7_branchwise (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    branchwise7 (clauseExtra (controls7 v) tag .c7) id =
      ((c7Branchwise v tag id).1.map sourceHistory,(c7Branchwise v tag id).2.map sourceHistory) := by
  cases v <;> cases tag <;> rfl

theorem controls7_distribution (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    distribution7 (clauseExtra (controls7 v) tag .c7) id = c7JointDistribution v tag id := by
  simp only [distribution7,c7JointDistribution,controls7_count,(controls7_tables v tag id).1]

theorem controls7_display (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    display7 (clauseExtra (controls7 v) tag .c7) id = c7Display v tag id := by
  simp only [display7,c7Display,(controls7_tables v tag id).2.2,controls7_distribution]

theorem controls7_strict (v : C7Variant) (tag : Tag) :
    Strict7 (clauseExtra (controls7 v) tag .c7) ↔ C7Strict v tag := by
  cases v <;> cases tag <;> unfold Strict7 C7Strict <;> decide

theorem controls7_histories (v : C7Variant) (tag : Tag) (id : HistoryId) :
    historySupported (clauseExtra (controls7 v) tag .c7) id = supportedHistory tag id := by
  cases v <;> cases tag <;> cases id <;> decide

theorem controls7_mixed (v : C7Variant) (tag : Tag) :
    mixed7 (clauseExtra (controls7 v) tag .c7) = c7MixedRealized v := by
  cases v <;> cases tag <;> decide

theorem controls7_active (v : C7Variant) (tag : Tag) :
    active7 (clauseExtra (controls7 v) tag .c7) = c7ReceiverActive v := by
  cases v <;> cases tag <;> decide

theorem c7_controls_equivalence (v : C7Variant) (tag : Tag) :
    C7Accept (controls7 v) tag ↔ C7Pass v tag := by
  unfold C7Accept
  rw [and_iff_right (controls7_gate v tag)]
  have hb : (clauseExtra (controls7 v) tag .c7).base =
      legacyInputs .positive .positive .position tag := controls7_inputs v tag
  simp only [C7Rule,C7Pass,Local7,C7LocallyConsistent,Histories7,C7HistoriesAdmissible,
    controls7_strict,operational7_iff_raw,C7OperationalUse,controls7_histories,
    (controls7_tables v tag _).1,(controls7_tables v tag _).2.1,
    controls7_display,
    controls7_mixed,controls7_active,hb]
  rfl

theorem c7_transport_equivalence (v : C7Variant) :
    C7Transport (controls7 v) ↔ CSTTT.POS04.C7Transport v := by
  unfold C7Transport
  rw [and_iff_right (controls7_gate v .source),and_iff_right (controls7_gate v .target)]
  simp only [CSTTT.POS04.C7Transport,(controls7_tables v _ .diagonal).2.2,
    (controls7_tables v _ _).1,controls7_branchwise,controls7_distribution,c7Branchwise]

/-- The expanded public channel detects M and therefore destroys the narrow
collision; it does not repair full HIDD, whose non-exposure already fails. -/
theorem neg_c4_expose_outcome (tag : Tag) :
    ¬ C4Accept (expose4 canonical) tag := by
  intro h
  have hn : ¬ Collision4 (clauseExtra (expose4 canonical) tag .c4) := by
    cases tag <;> unfold Collision4 <;> decide
  exact hn h.2.1

theorem neg_c5_external_outcomes :
    C5Accept (external5 canonical) .source ∧ ¬ C5Accept (external5 canonical) .target ∧
    credit5 (clauseExtra (external5 canonical) .target .c5) .clockwise = .other := by
  refine ⟨(c5_controls_equivalence .negExternal .source).mpr (c5_surrogate_each_tag .source),?_,?_⟩
  · intro h; exact neg_c5_external_fails ((c5_controls_equivalence .negExternal .target).mp h)
  · exact (controls5_credit .negExternal .target .clockwise).trans neg_c5_external_credit_is_other

theorem neg_c5_internalized_outcomes :
    C5Accept (internalized5 canonical) .source ∧ C5Accept (internalized5 canonical) .target ∧
    ¬ C5Transport (internalized5 canonical) ∧
    credit5 (clauseExtra (internalized5 canonical) .target .c5) .scheduled = .other := by
  refine ⟨(c5_controls_equivalence .negInternalized .source).mpr (c5_surrogate_each_tag .source),
    (c5_controls_equivalence .negInternalized .target).mpr neg_c5_internalized_local_still_holds,?_,?_⟩
  · intro h
    exact neg_c5_internalized_breaks_raw_transport ((c5_transport_equivalence .negInternalized).mp h)
  · exact (controls5_credit .negInternalized .target .scheduled).trans neg_c5_internalized_credit_still_other

theorem neg_c7_aggregate_outcomes (tag : Tag) : ¬ C7Accept (aggregate7 canonical) tag := by
  intro h
  exact neg_c7_aggregate_loses_refinement tag
    ((c7_controls_equivalence .negAggregate tag).mp h).2.2.1

theorem neg_c7_uncoupled_outcomes (tag : Tag) :
    Local7 (clauseExtra (uncoupled7 canonical) tag .c7) ∧
    ¬ C7Accept (uncoupled7 canonical) tag := by
  refine ⟨?_,?_⟩
  · change Local7 (clauseExtra (controls7 .negUncoupled) tag .c7)
    simp only [Local7,(controls7_tables .negUncoupled tag _).1,
      (controls7_tables .negUncoupled tag _).2.1]
    exact neg_c7_uncoupled_consistent tag
  · intro h
    exact neg_c7_uncoupled_loses_refinement tag
      ((c7_controls_equivalence .negUncoupled tag).mp h).2.2.1

theorem neg_c7_transport_outcomes :
    C7Accept (transportBreak7 canonical) .source ∧
    Local7 (clauseExtra (transportBreak7 canonical) .target .c7) ∧
    ¬ C7Accept (transportBreak7 canonical) .target ∧ ¬ C7Transport (transportBreak7 canonical) := by
  refine ⟨(c7_controls_equivalence .negTransport .source).mpr (c7_each_tag .source),?_,?_,?_⟩
  · change Local7 (clauseExtra (controls7 .negTransport) .target .c7)
    simp only [Local7,(controls7_tables .negTransport .target _).1,
      (controls7_tables .negTransport .target _).2.1]
    exact neg_c7_transport_locally_consistent
  · intro h
    exact neg_c7_transport_loses_target_refinement
      ((c7_controls_equivalence .negTransport .target).mp h).2.2.1
  · intro h
    exact neg_c7_transport_breaks_staged_equation ((c7_transport_equivalence .negTransport).mp h)

theorem canonical_staged57 : C5Transport canonical ∧ C7Transport canonical :=
  ⟨(c5_transport_equivalence .positive).mpr c5_raw_staged_transport,
   (c7_transport_equivalence .positive).mpr c7_staged_transport⟩

theorem assigned_joint_distribution_probability (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    ((distribution7 (clauseExtra (controls7 v) tag .c7) id).map Prod.fst).sum = 2 ∧
    (∀ entry ∈ distribution7 (clauseExtra (controls7 v) tag .c7) id, entry.2 = 2) := by
  rw [controls7_distribution]
  exact c7_joint_distribution_probability v tag id

theorem assigned_exact_joint_probabilities (tag : Tag) :
    pairing7 (clauseExtra canonical tag .c7) .diagonal .repA .classB = 1/2 ∧
    pairing7 (clauseExtra canonical tag .c7) .crossed .repA .split = 1/2 := by
  rw [canonical_extra,canonical_pairing_link,canonical_pairing_link]
  exact c7_exact_distributions tag

theorem canonical_route_tuple (tag : Tag) (id : RouteId) :
    routeTuple (clauseExtra canonical tag .c6) id = some (routeRegister id) := by
  cases tag <;> cases id <;> rfl

theorem mapCell_other_cell (a : Assignment) (k j : Cell) (f : Value k → Value k)
    (h : j ≠ k) : mapCell a k f j = a j := put_other a k j _ h

theorem c4_expose_equivalence (tag : Tag) :
    C4Accept (expose4 canonical) tag ↔ C4Surrogate .negExpose tag := by
  constructor
  · intro h; exact False.elim (neg_c4_expose_outcome tag h)
  · intro h; exact False.elim (neg_c4_expose_loses_collision tag h.1)

theorem exposed_channel_raw_link (tag : Tag) (s : KState) :
    current (clauseExtra (expose4 canonical) tag .c4) s = c4Current .negExpose tag s := by
  cases tag <;> cases s <;> decide

theorem canonical_connector_link (tag : Tag) :
    connector (clauseExtra canonical tag .c4) = connectorHistory := by
  cases tag <;> rfl

end CSTTT.POS04.Assigned
