import CSTTT.POS04.Bridge
import CSTTT.Targets.TemporalFIACH

/-! FIACH-POS-04 assembly, `audit/M3_model_spec.md:16-24,30-32,46-48`.
This is a finite, model-relative witness that the declared TTH-06 obligations
are jointly satisfiable. C4-C7 remain declared surrogates: this is neither a
full P05 C-package, T17-I, nor a claim about a physical system. Recognition
is not addressed. All evidence below is tied to computed POS-04 predicates;
the free proposition fields of the older generic certificate are instantiated
only with those predicates. Each mutation theorem below proves non-existence
through one selected, real failure witness. The clause-specific variants do
not reproduce M3b's full per-mutation failure attribution.
-- FOLLOW-UP: use one shared raw `Model` record for every clause and lane;
-- express every declared mutation as a function `Model → Model`, then
-- recompute all clause and lane side effects from that single changed model. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

/-- Carrier identifiers are the indices in the declared ordered tag list. -/
def tagCarrierId (tag : Tag) : CarrierId := ⟨tags.idxOf tag⟩

theorem pos04_carriers_distinct :
    tagCarrierId .source ≠ tagCarrierId .target := by decide

/-- The only C1 table intervention changes target `p2w1/stay` from the
published T1 row to the declared half/half row (`NEG-C1-TABLE`). -/
inductive C1TableVariant where | positive | negTable
  deriving DecidableEq, Repr

def c1ActionRow (v : C1TableVariant) (profile : ProfileVariant) (tag : Tag)
    (s : KState) (a : Action) : List (Ambient × Nat) :=
  if v = .negTable && tag = .target && s = .p2w1 && a = .stay then
    [(.inK .p1w0,2),(.inK .p1w1,2)]
  else profileRow profile tag s a

/-- The variant M is derived from its own action supports and the frozen
hazard rule. In the positive case this is `rawMFor .positive`, not the
imported class number. -/
def c1RawM (v : C1TableVariant) (profile : ProfileVariant)
    (tag : Tag) (s : KState) : Nat × List (List Bool) :=
  (publicPosition s, actions.map fun a =>
    (c1ActionRow v profile tag s a).map fun entry => isLethalHazard entry.1)

theorem c1_rawM_is_rawMFor (profile : ProfileVariant) (tag : Tag)
    (s : KState) : c1RawM .positive profile tag s = rawMFor profile tag s := rfl

/-- These representatives are the first nonzero row of each frozen C column,
in its declared column order: p0w0, p1w1, p1w0, p2w1, p3w0, p4w0, p5w0.
The *class values* below are recomputed from variant raw M; imported
`taggedMClass` never decides C or U. -/
def c1ColumnRepresentatives : List KState :=
  [.p0w0,.p1w1,.p1w0,.p2w1,.p3w0,.p4w0,.p5w0]

/-- The fixed representative order is verified as the first nonzero row of
each separately imported C column. -/
def C1ColumnOrderMatches : Prop :=
  ((List.finRange 7).all fun k =>
    ((indices.filter fun i => cIndicator i k == 1).head?) ==
      some (index (c1ColumnRepresentatives.getD k.val .p0w0))) = true

theorem c1_column_order_matches : C1ColumnOrderMatches := by
  simp only [C1ColumnOrderMatches]
  decide

def c1RawClassOrder (v : C1TableVariant) (profile : ProfileVariant)
    (tag : Tag) : List (Nat × List (List Bool)) :=
  c1ColumnRepresentatives.map (c1RawM v profile tag)

def c1RawClassSize (v : C1TableVariant) (profile : ProfileVariant)
    (tag : Tag) (s : KState) : Nat :=
  (kernel.filter fun t => c1RawM v profile tag s == c1RawM v profile tag t).length

def c1RawC (v : C1TableVariant) (profile : ProfileVariant)
    (tag : Tag) (i : I) (k : J) : Nat :=
  if c1RawM v profile tag (stateAt i) =
      (c1RawClassOrder v profile tag).getD k.val (0,[]) then 1 else 0

def c1RawUNum (v : C1TableVariant) (profile : ProfileVariant)
    (tag : Tag) (k : J) (j : I) : Nat :=
  if c1RawM v profile tag (stateAt j) =
      (c1RawClassOrder v profile tag).getD k.val (0,[]) then
    2 / c1RawClassSize v profile tag (stateAt j) else 0

/-- P, C and U all read the variant raw rows. C-column order is fixed by
the declared prototype columns, while each ordered class is recomputed from
the variant raw M. The separate imported C and U tables are comparison
targets only; their product is checked against T1's `CU`. -/
def C1TablesReconstructed (v : C1TableVariant)
    (profile : ProfileVariant) (tag : Tag) : Prop :=
  indices = List.finRange 10 ∧ c1ColumnRepresentatives.length = 7 ∧
  C1ColumnOrderMatches ∧
  (c1RawClassOrder v profile tag).Nodup ∧
  (kernel.all fun s =>
    decide (c1RawM v profile tag s ∈ c1RawClassOrder v profile tag)) = true ∧
  (∀ s t : KState,
    rowWeight (c1ActionRow v profile tag s (canonicalAction s)) t =
      taggedPNum tag s t) ∧
  (indices.all fun i => (List.finRange 7).all fun k =>
    c1RawC v profile tag i k == cIndicator i k) = true ∧
  ((List.finRange 7).all fun k => indices.all fun j =>
    c1RawUNum v profile tag k j == uPrototypeNum k j) = true ∧
  (∀ i j : I,
    sum7 (fun k => c1RawC v profile tag i k *
      c1RawUNum v profile tag k j) = CU.num i j)

theorem c1_tables_reconstructed (tag : Tag) :
    C1TablesReconstructed .positive .positive tag := by
  refine ⟨by decide, by decide, c1_column_order_matches,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases tag <;> decide
  · cases tag <;> decide
  · intro s t
    exact canonical_action_row_agrees_with_tagged_P tag s t
  · cases tag <;> decide
  · cases tag <;> decide
  · cases tag <;> decide

/-- `NEG-C3-PROFILE` changes a canonical P row but leaves every raw M
readout unchanged. Its C1 failure is therefore a P-reconstruction failure,
not a C/U-fiber failure. -/
theorem neg_c3_profile_rawM_unchanged (s : KState) :
    c1RawM .positive .negC3Profile .target s =
      c1RawM .positive .positive .target s := by
  cases s <;> decide

theorem neg_c3_profile_class_order_unchanged :
    c1RawClassOrder .positive .negC3Profile .target =
      c1RawClassOrder .positive .positive .target := by decide

theorem neg_c3_profile_breaks_c1_P :
    ¬ C1TablesReconstructed .positive .negC3Profile .target := by
  intro h
  have hn :
      rowWeight (c1ActionRow .positive .negC3Profile .target .p1w0
        (canonicalAction .p1w0)) .p2w1 ≠
        taggedPNum .target .p1w0 .p2w1 := by decide
  exact hn (h.2.2.2.2.2.1 .p1w0 .p2w1)

theorem neg_c1_table_breaks_P :
    ¬ C1TablesReconstructed .negTable .positive .target := by
  intro h
  have hn :
      rowWeight (c1ActionRow .negTable .positive .target .p2w1
        (canonicalAction .p2w1)) .p1w0 ≠
        taggedPNum .target .p2w1 .p1w0 := by decide
  exact hn (h.2.2.2.2.2.1 .p2w1 .p1w0)

/-- The 160 imported assignments form exactly the tagged state/clause
product. Every typed primitive reference has a nonempty pointer to an
imported raw table; the read-only L5 transcription checker additionally
resolves those pointers against the frozen JSON. -/
def primitiveRefResolves (tag : Tag) : PrimitiveRef → Bool
  | .actionDistributions => kernel.length == 10 &&
      ambientStates.length == 12 && actions.length == 3
  | .publishedP => pRows.length == 10
  | .publishedC => declaredClassOrder.length == 7 && indices.length == 10
  | .publishedU => declaredClassOrder.length == 7 && indices.length == 10
  | .publicChannelRule => publicChannelRule tag == .position
  | .publishedMClasses => mClasses.length == 10
  | .currentChannels => currentChannels.length == 2
  | .protocols => protocolIds.length == 4
  | .tickIncrement => kernel.all (fun s =>
      actions.all (fun a => tickIncrement tag s a == 1))
  | .futureInterface => futureInterface.length == 8
  | .assemblages => assemblageIds.length == 2
  | .resources => decide (resourceOwner tag = tag)
  | .maintenance => decide (ledger.initialBudget ≥ ledger.actionCost) &&
      decide (ledger.rechargePerAction > 0)

def CoordinatesComplete : Prop :=
  coordinates.length = 160 ∧ coordinates.Nodup ∧
  (∀ tag : Tag, ∀ s : KState, ∀ c : Clause,
    ⟨tag,s,c⟩ ∈ coordinates) ∧
  (coordinates.all fun x =>
    !(primitiveRefs x.tag x.clause).isEmpty &&
    (primitiveRefs x.tag x.clause).all (fun ref =>
      primitivePath x.tag ref != "" &&
      primitiveRefResolves x.tag ref)) = true

theorem coordinates_complete : CoordinatesComplete := by
  refine ⟨coordinates_count, coordinates_distinct,
    clause_coordinates_complete, ?_⟩
  simp only [List.all_eq_true]
  intro x _
  cases x with
  | mk tag s c =>
      dsimp
      cases tag <;> cases c <;> decide

/-- T1's exact C1 audit transported to either tagged factor, including
uniqueness of the probability fixed point. -/
def C1FactorPass (tag : Tag) (v : C1TableVariant := .positive)
    (profile : ProfileVariant := .positive) : Prop :=
  C1TablesReconstructed v profile tag ∧
  TaggedProbability tag taggedPi ∧ TaggedFixed tag taggedPi ∧
  (∀ μ : TaggedIndex → Rat, TaggedProbability tag μ → TaggedFixed tag μ →
    ∀ i : I, μ (tag,i) = taggedPi (tag,i)) ∧
  (fun i : I => taggedPi (tag,i)) ≠ uniform ∧
  taggedCoreMass tag = 77/80 ∧ taggedCoreMass tag ≥ 3/4 ∧
  taggedTV tag = 3/80 ∧ taggedDefect tag = 78795/524288 ∧
  defect E2zero = 1/8

theorem c1_factor_pass (tag : Tag) : C1FactorPass tag :=
  ⟨c1_tables_reconstructed tag,
    c1_probability_each_tag tag, c1_fixed_each_tag tag,
    fun μ hp hf => c1_unique_each_tag tag μ hp hf,
    c1_nonuniform_each_tag tag, c1_core_mass_each_tag tag,
    c1_retention_each_tag tag, c1_tv_each_tag tag,
    c1_defect_each_tag tag, e2zero_defect⟩

/-- The package grade is explicit: C1-C3 and operational C8 are substantive
on the exact T1 factor; C4-C7 are their declared POS-04 surrogates. -/
structure ClauseVariants where
  c1 : C1TableVariant := .positive
  lower : LowerRule := .position
  profile : ProfileVariant := .positive
  c4 : C4Variant := .positive
  c5 : C5Variant := .positive
  c6 : C6Variant := .positive
  c7 : C7Variant := .positive

def PackagePass (v : C8Variant) (tag : Tag)
    (variants : ClauseVariants := {}) : Prop :=
  CoordinatesComplete ∧
  C1FactorPass tag variants.c1 variants.profile ∧
  C2Pass variants.lower tag ∧
  C3Pass variants.profile variants.lower tag ∧
  C4Surrogate variants.c4 tag ∧ C5Surrogate variants.c5 tag ∧
  C6Pass variants.c6 tag ∧ C7Pass variants.c7 tag ∧ C8Pass v tag

theorem package_funded_each_tag (tag : Tag) : PackagePass .funded tag :=
  ⟨coordinates_complete, c1_factor_pass tag, c2_split_each_tag tag, c3_each_tag tag,
    c4_surrogate_each_tag tag, c5_surrogate_each_tag tag,
    c6_each_tag tag, c7_each_tag tag, c8_funded_each_tag tag⟩

/-- The eight raw staged-map rows and their component equations. The equations
are on action rows, readouts, temporal ticks, protocol products and coupling;
the source/target package proofs are separate. -/
def StagedClausePass (funding : C8Variant := .funded)
    (variants : ClauseVariants := {}) : Prop :=
  stagedClauseMap = clauses.map (fun c => (c,.source,.target)) ∧
  (∀ s t : KState,
    rowWeight (c1ActionRow variants.c1 variants.profile .source s
      (canonicalAction s)) t =
      rowWeight (c1ActionRow variants.c1 variants.profile .target s
        (canonicalAction s)) t) ∧
  (∀ s : KState, taggedMClass .source s = taggedMClass .target s) ∧
  (∀ s : KState,
    lowerReadout (positiveLowerRule .source) s =
      lowerReadout (positiveLowerRule .target) s ∧
    rawM .source s = rawM .target s) ∧
  (∀ s : KState,
    profile2 variants.profile variants.lower .source s =
      profile2 variants.profile variants.lower .target s) ∧
  (∀ s : KState, ∀ a : Action,
    profileRow variants.profile .source s a =
      profileRow variants.profile .target s a) ∧
  (∀ s : KState, c4Current variants.c4 .source s =
    c4Current variants.c4 .target s) ∧
  C5RawTransport variants.c5 ∧
  C6Pass variants.c6 .source ∧ C6Pass variants.c6 .target ∧
  C7Transport variants.c7 ∧
  C8Pass .funded .source ∧ C8Pass .funded .target ∧
  C8Pass funding .target ∧
  c8Greatest .funded .source = c8Greatest funding .target ∧
  (∀ s : KState, ∀ a : Action,
    tickIncrement .source s a = tickIncrement .target s a ∧
    actionRow .source s a = actionRow .target s a) ∧
  resourceOwner .source = .source ∧ resourceOwner .target = .target

theorem staged_clause_pass : StagedClausePass := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, c5_raw_staged_transport,
    c6_each_tag .source, c6_each_tag .target, c7_staged_transport,
    c8_funded_each_tag .source, c8_funded_each_tag .target,
    c8_funded_each_tag .target, ?_, ?_, by decide, by decide⟩
  · intro s t; rfl
  · intro s; rfl
  · intro s; exact c2_tag_map_preserves_readouts s
  · intro s; cases s <;> decide
  · intro s a; cases s <;> cases a <;> decide
  · intro s; cases s <;> decide
  · rw [c8_funded_greatest_is_kernel, c8_funded_greatest_is_kernel]
  · intro s a; cases s <;> cases a <;> decide

/-- Comparison pairs come from the declared two-route domain, not a stored
status. No flatness certificate is supplied by POS-04. -/
def routeComparisonPairs : List (RouteId × RouteId) :=
  routeIds.flatMap fun first =>
    routeIds.filterMap fun second =>
      if first = second then none else some (first,second)

/-- The endpoint is recomputed for each route from its own raw history and
exit event. Equal target endpoints are required before comparing futures. -/
def routeTargetEndpoint (id : RouteId) : Option KState :=
  let route := routeOf id
  if route.eventPath.getLast? = some .exit &&
      (eventOf .exit).toStage = .targetExit then
    receiverFactor .positive route.sourceHistory
  else none

def routeStatusOf (v : RouteVariant) : RouteStatus :=
  if routeComparisonPairs.any (fun pair =>
      routeReferencesResolve pair.1 && routeReferencesResolve pair.2 &&
      routeEventsCompose pair.1 && routeEventsCompose pair.2 &&
      decide (routeRegister pair.1 ≠ routeRegister pair.2) &&
      (match routeTargetEndpoint pair.1, routeTargetEndpoint pair.2 with
       | some first, some second => decide (first = second)
       | _, _ => false) &&
      (match routeFutureOutput v pair.1, routeFutureOutput v pair.2 with
       | some a, some b => decide (a ≠ b)
       | _, _ => false))
  then .routeIndexed else .unresolved

theorem route_comparison_nonempty : routeComparisonPairs ≠ [] := by decide
theorem compared_routes_share_target_endpoint :
    routeTargetEndpoint .a = some .p1w0 ∧
    routeTargetEndpoint .b = some .p1w0 := by decide
theorem route_status_positive : routeStatusOf .positive = .routeIndexed := by decide
theorem recognition_not_addressed : recognitionStatus = .notAddressed := rfl

/-- Every field is a proof of a fixed computed predicate. Mutation variants
are data parameters, so the same type rejects a broken lane. -/
structure POS04FIACHCertificate (rv : ReceiverVariant)
    (cv : CorridorVariant) (routeV : RouteVariant) (funding : C8Variant)
    (variants : ClauseVariants := {}) where
  distinct : tagCarrierId .source ≠ tagCarrierId .target
  sourcePackage : PackagePass .funded .source variants
  staged : StagedClausePass funding variants
  targetPackage : PackagePass funding .target variants
  packageEndpoint : receiverOutput rv cv .repA = some .p1w0
  corridor : CorridorPass cv
  bridge : BridgePass rv routeV
  representatives : RepresentativeIndependence rv
  content : ContentSensitivity rv cv
  sourceAbsentFailure : receiverActive .sourceAbsent cv = false
  autonomy : TargetAutonomy funding c8WithdrawnReceiver
  typedEndpoint : TypedEndpointLink rv cv routeV
  routeMemory : RouteMemoryPass routeV
  routeStatus : routeStatusOf routeV = .routeIndexed
  recognition : recognitionStatus = .notAddressed

theorem pos04_fiach :
    Nonempty (POS04FIACHCertificate .positive .positive .positive .funded) := by
  refine ⟨{
    distinct := pos04_carriers_distinct
    sourcePackage := package_funded_each_tag .source
    staged := staged_clause_pass
    targetPackage := package_funded_each_tag .target
    packageEndpoint := by decide
    corridor := corridor_positive
    bridge := bridge_positive
    representatives := representative_independence_positive
    content := content_sensitive_positive
    sourceAbsentFailure := neg_activation_source_absent
    autonomy := target_only_autonomy_positive
    typedEndpoint := typed_endpoint_link_positive
    routeMemory := route_memory_positive
    routeStatus := route_status_positive
    recognition := recognition_not_addressed
  }⟩

/-- The three TTH-06 lanes remain separate predicates. -/
def IntegratedTargetRealization (rv : ReceiverVariant)
    (cv : CorridorVariant) (funding : C8Variant)
    (variants : ClauseVariants := {}) : Prop :=
  PackagePass .funded .source variants ∧
  StagedClausePass funding variants ∧
  PackagePass funding .target variants ∧
  receiverOutput rv cv .repA = some .p1w0

def StrictTemporalLineage (rv : ReceiverVariant)
    (cv : CorridorVariant) (routeV : RouteVariant) : Prop :=
  CorridorPass cv ∧ BridgePass rv routeV ∧
  RepresentativeIndependence rv ∧ ContentSensitivity rv cv ∧
  receiverActive .sourceAbsent cv = false ∧
  TypedEndpointLink rv cv routeV ∧ RouteMemoryPass routeV ∧
  routeStatusOf routeV = .routeIndexed

def PostWithdrawalAutonomy (funding : C8Variant) : Prop :=
  TargetAutonomy funding c8WithdrawnReceiver

theorem pos04_fiach_readout {rv cv routeV funding variants}
    (c : POS04FIACHCertificate rv cv routeV funding variants) :
    IntegratedTargetRealization rv cv funding variants ∧
    StrictTemporalLineage rv cv routeV ∧
    PostWithdrawalAutonomy funding := by
  exact ⟨⟨c.sourcePackage,c.staged,c.targetPackage,c.packageEndpoint⟩,
    ⟨c.corridor,c.bridge,c.representatives,c.content,
      c.sourceAbsentFailure,c.typedEndpoint,c.routeMemory,c.routeStatus⟩,
    c.autonomy⟩

/-! The old generic type is populated with raw POS-04 data and the same
computed predicates. Its unrestricted source/stage proposition slots receive
the fixed definitions above, rather than caller-supplied claims. -/
structure PackageDatum where
  tag : Tag
  endpoint : KState
  funding : C8Variant

structure CorridorDatum where
  source : Tag
  target : Tag
  receiver : ReceiverVariant
  corridor : CorridorVariant
  route : RouteVariant

structure AutonomyDatum where
  tag : Tag
  funding : C8Variant
  receiver : Receiver

def genericPackageValid (rv : ReceiverVariant) (cv : CorridorVariant)
    (d : PackageDatum) : Prop :=
  d.tag = .target ∧ PackagePass d.funding d.tag ∧
  receiverOutput rv cv .repA = some d.endpoint

def genericCorridorValid (d : CorridorDatum) : Prop :=
  d.source = .source ∧ d.target = .target ∧
  CorridorPass d.corridor ∧ BridgePass d.receiver d.route ∧
  ContentSensitivity d.receiver d.corridor ∧
  TypedEndpointLink d.receiver d.corridor d.route ∧
  RouteMemoryPass d.route

def genericAutonomyValid (d : AutonomyDatum) : Prop :=
  d.tag = .target ∧ TargetAutonomy d.funding d.receiver

def packageDatumTarget (d : PackageDatum) : CarrierId := tagCarrierId d.tag
def corridorDatumSource (d : CorridorDatum) : CarrierId := tagCarrierId d.source
def corridorDatumTarget (d : CorridorDatum) : CarrierId := tagCarrierId d.target
def autonomyDatumTarget (d : AutonomyDatum) : CarrierId := tagCarrierId d.tag

/-- Map the POS-04 raw recognition field into the older CSTTT vocabulary. -/
def genericRecognitionStatus : CSTTT.RecognitionStatus :=
  match recognitionStatus with
  | .notAddressed => .notAddressed

def GenericPOS04Certificate (rv : ReceiverVariant) (cv : CorridorVariant) :=
  TemporalFIACHCertificate PackageDatum CorridorDatum AutonomyDatum
    (genericPackageValid rv cv) genericCorridorValid genericAutonomyValid
    packageDatumTarget corridorDatumSource corridorDatumTarget
    autonomyDatumTarget

def toGeneric {rv cv routeV}
    (c : POS04FIACHCertificate rv cv routeV .funded) :
    GenericPOS04Certificate rv cv := {
  source := tagCarrierId .source
  target := tagCarrierId .target
  distinct := c.distinct
  sourcePackagePremise := PackagePass .funded .source
  sourcePackageEvidence := c.sourcePackage
  stagedClausePreservation := StagedClausePass
  stagedPreservationEvidence := c.staged
  packageCertificate := ⟨.target,.p1w0,.funded⟩
  packageEvidence := ⟨rfl,c.targetPackage,c.packageEndpoint⟩
  packageEndpoint := rfl
  corridorCertificate := ⟨.source,.target,rv,cv,routeV⟩
  corridorEvidence := ⟨rfl,rfl,c.corridor,c.bridge,c.content,
    c.typedEndpoint,c.routeMemory⟩
  corridorSourceEndpoint := rfl
  corridorTargetEndpoint := rfl
  autonomyCertificate := ⟨.target,.funded,c8WithdrawnReceiver⟩
  autonomyEvidence := ⟨rfl,c.autonomy⟩
  autonomyEndpoint := rfl
  routeStatus := routeStatusOf routeV
  recognitionStatus := genericRecognitionStatus
}

theorem pos04_existing_certificate_instance :
    Nonempty (GenericPOS04Certificate .positive .positive) := by
  obtain ⟨c⟩ := pos04_fiach
  exact ⟨toGeneric c⟩

theorem pos04_generic_statuses {rv cv routeV}
    (c : POS04FIACHCertificate rv cv routeV .funded) :
    (toGeneric c).routeStatus = .routeIndexed ∧
    (toGeneric c).recognitionStatus = .notAddressed :=
  ⟨c.routeStatus,rfl⟩

theorem no_fiach_detached :
    ¬ Nonempty (POS04FIACHCertificate .positive .detached .positive .funded) := by
  rintro ⟨c⟩
  exact neg_corridor_detached_fails c.corridor

theorem no_fiach_gap :
    ¬ Nonempty (POS04FIACHCertificate .positive .gap .positive .funded) := by
  rintro ⟨c⟩
  exact neg_corridor_gap_fails c.corridor

theorem no_fiach_source_absent :
    ¬ Nonempty (POS04FIACHCertificate .sourceAbsent .positive .positive .funded) := by
  rintro ⟨c⟩
  exact source_absent_content_fails c.content

theorem no_fiach_preloaded_copy :
    ¬ Nonempty (POS04FIACHCertificate .preloadedCopy .positive .positive .funded) := by
  rintro ⟨c⟩
  exact neg_preloaded_copy_content_fails c.content

theorem no_fiach_underfunded_withdrawal :
    ¬ Nonempty (POS04FIACHCertificate .sourceAbsent .positive .underfund .negUnderfund) := by
  rintro ⟨c⟩
  exact neg_autonomy_withdraw_fails c.autonomy

theorem no_fiach_bridge_rep :
    ¬ Nonempty (POS04FIACHCertificate .bridgeRep .positive .positive .funded) := by
  rintro ⟨c⟩
  exact neg_bridge_rep_fails c.bridge

theorem no_fiach_route_memory :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .negMemory .funded) := by
  rintro ⟨c⟩
  exact neg_route_memory_fails c.routeMemory

/-! These nineteen `no_fiach_*` theorems establish non-existence through one
selected, real failing obligation for each declared intervention. They do not
claim complete M3b side-effect attribution: the clause-specific variants do
not propagate one mutation through every predicate. `NEG-C3-PROFILE` retains
local C3 and raw M, but its changed canonical P row fails C1 reconstruction.
Its staged raw-row equality also fails independently. -/

theorem no_fiach_c1_table :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { c1 := .negTable }) := by
  rintro ⟨c⟩
  exact neg_c1_table_breaks_P c.targetPackage.2.1.1

theorem no_fiach_c2_split :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { lower := .stateLabel }) := by
  rintro ⟨c⟩
  rcases c.targetPackage with ⟨_,_,hc2,_⟩
  exact neg_c2_split_no_defect .target ⟨.p1w0,.p1w1,hc2⟩

theorem neg_c3_profile_breaks_staged_rows :
    ¬ StagedClausePass .funded { profile := .negC3Profile } := by
  intro h
  rcases h with ⟨_,_,_,_,_,hrow,_⟩
  have hn :
      profileRow .negC3Profile .source .p1w0 .cw ≠
      profileRow .negC3Profile .target .p1w0 .cw := by decide
  exact hn (hrow .p1w0 .cw)

theorem no_fiach_c3_profile :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { profile := .negC3Profile }) := by
  rintro ⟨c⟩
  exact neg_c3_profile_breaks_c1_P c.targetPackage.2.1.1

theorem no_fiach_c4_expose :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { c4 := .negExpose }) := by
  rintro ⟨c⟩
  rcases c.targetPackage with ⟨_,_,_,_,hc4,_⟩
  exact neg_c4_expose_loses_collision .target hc4.1

theorem no_fiach_c5_external :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { c5 := .negExternal }) := by
  rintro ⟨c⟩
  rcases c.targetPackage with ⟨_,_,_,_,_,hc5,_⟩
  exact neg_c5_external_fails hc5

theorem no_fiach_c5_internalized :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { c5 := .negInternalized }) := by
  rintro ⟨c⟩
  rcases c.staged with ⟨_,_,_,_,_,_,_,hc5,_⟩
  exact neg_c5_internalized_breaks_raw_transport hc5

theorem no_fiach_c6_future :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { c6 := .negFuture }) := by
  rintro ⟨c⟩
  rcases c.targetPackage with ⟨_,_,_,_,_,_,hc6,_⟩
  exact neg_c6_future_trace_fails hc6.1

theorem no_fiach_c6_record :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { c6 := .negRecord }) := by
  rintro ⟨c⟩
  rcases c.targetPackage with ⟨_,_,_,_,_,_,hc6,_⟩
  exact neg_c6_record_clause_fails hc6

theorem no_fiach_c7_aggregate :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { c7 := .negAggregate }) := by
  rintro ⟨c⟩
  rcases c.targetPackage with ⟨_,_,_,_,_,_,_,hc7,_⟩
  exact neg_c7_aggregate_loses_refinement .target hc7.2.2.1

theorem no_fiach_c7_transport :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { c7 := .negTransport }) := by
  rintro ⟨c⟩
  rcases c.staged with ⟨_,_,_,_,_,_,_,_,_,_,hc7,_⟩
  exact neg_c7_transport_breaks_staged_equation hc7

theorem no_fiach_c7_uncoupled :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .positive
      .funded { c7 := .negUncoupled }) := by
  rintro ⟨c⟩
  rcases c.targetPackage with ⟨_,_,_,_,_,_,_,hc7,_⟩
  exact neg_c7_uncoupled_loses_refinement .target hc7.2.2.1

theorem no_fiach_c8_underfund :
    ¬ Nonempty (POS04FIACHCertificate .positive .positive .underfund
      .negUnderfund) := by
  rintro ⟨c⟩
  exact neg_autonomy_withdraw_fails c.autonomy

end CSTTT.POS04
