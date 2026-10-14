# G2b-1 — assignment-indexed C4, C5, C7

## Scope, grades, and statement changes

Authority: frozen `audit/M3_model_spec.md:20–23,30–35` and the existing L6b
predicates in `C4C5.lean` and `C7.lean`. All three clauses retain their declared
**surrogate** ceilings. This is not an HIDD/T5/joint-history upgrade, full P05
package, or T17-I instance. TTH-02 stays **conditional**. No registry, inventory,
frozen model, or existing L6b predicate is modified.

All changes are **(b) mathematical** for TTH-02:

- `Assigned/Substrate.lean`: extend the typed cell/value domain and canonical
  raw assignment; expand C4/C5/C6/C7 dependency scopes. C8 already has its raw
  rows, policy, resources and ledger dependencies; it does not read corridor,
  history or receiver activation data. C1–C3 scopes and semantics are unchanged.
- Four new C457 modules: assignment-indexed raw rules, activation-gated receiver
  operation, locality, canonical/control equivalence, actual mutation adapters,
  and field guards. The root module imports the new guards module.
- Input well-formedness is explicit: C4's connector has pinned endpoints and
  at least two states; C7's raw history table is injective on the four declared
  references. These guards strengthen acceptance of arbitrary assignments,
  without changing any canonical or declared-control outcome. They prevent
  empty connectors and duplicate-name pseudo-witnesses.

C6 and C8 evaluators remain for G2b-2. A reference-readiness gate for the new
route/writer cells is supplied here, explicitly **not** C6 acceptance or an
all-word proof.

## Namespace and derived views

The same immutable `Assignment` now contains six additional typed cell families:

| Cell | Raw value | Sharing |
|---|---|---|
| `histories` | `HistoryId → List KState` | C4 connector, C5 anchors, C7 branch records, C6 future routes |
| `eventTable` | `List Event` | C7 operation and C6 trace |
| `realized` | `List Stage` | C7 operation and C6 trace |
| `receiverInput` | `Receiver` | C7 activation and C6 run/route inputs |
| `routeTable` | `List Route` | C6 route references |
| `writers` | `Tag → RouteId → Bool` | C6 writer availability |

Canonical values resolve directly to the already transcribed Data tables.
The old 160 logical coordinates remain views. `resolveRef` still maps every
old primitive pointer to the one namespace, and `view_references_resolve`/
`views_160` still prove resolution, completeness and distinctness.

C4's connector is **defined** as the `.split` history in the shared cell;
`canonical_connector_link` proves equality with the frozen connector table.
The pinned collision pair and C5's vertex-to-history anchor identities are
fixed protocol indices, not independent supplied witnesses. Their raw paths
are decoded from `histories`. All history support checks use assigned rows
and assigned policy, require a nonempty path, and compute consecutive-edge
weights. They do not read stored support verdicts.

`routeTuple` is **defined** from the assigned route and history tables.
`canonical_route_tuple` links it to Data's `routeRegister`. There is no separate
candidate register cell. The single-enumerand route-readout rule is a fixed
protocol definition, not a independently supplied function. Funding/counter
updates and the future readout itself are reserved for G2b-2.

## Raw evaluators and canonical bridges

### C4

`currentChannel` computes the public position, action availability, or raw M
reader from assigned base fields. `current` evaluates the assigned complete
channel family. `Collision4`, `Connector4`, and `Exposed4` implement the L6b
narrow collision/connector and full exposure tests.

`C4Gate` checks missing inputs, positive/normalized support rows, the imported
M link, connector endpoints, and length. `C4Accept` evaluates all three rules
on **defined** decoded inputs. `c4_canonical_equivalence` identifies it with
`C4Surrogate .positive` on each tag. `exposed_channel_raw_link` checks the
expanded-channel adapter's current readouts; `c4_expose_equivalence` identifies
its failure with the old expanded-channel surrogate failure.

`assigned_full_HIDD_nonexposure_fails` proves the full HIDD non-exposure target
still fails: the nonconstant public position channel factors through the
computed predictive M. It is not recast as a positive full-HIDD result.

### C5

`count5`, `forward5`, `reverse5`, and `credit5` compute generator products
and self/other/none/ambiguous credit from assigned protocol edges.
`Owner5` checks credit/provenance consistency. `Anchors5` runs support checks
on the actual assigned histories. `C5Gate` rejects missing/malformed raw rows;
`C5Rule` contains the declared four protocol credits, ownership, and anchors.
Housing is **not** a credit input.

`C5Transport` compares assigned source/target edges, translated provenance,
and translated housing, with both decoder gates. `controls5_raw_tables` and
`controls5_credit` give exact field/product bridges. `c5_canonical_equivalence`,
`c5_controls_equivalence`, and `c5_transport_equivalence` preserve the L6b
results without projecting a free accepted predicate.

### C7

`branchwise7` keeps **actual complete ordered history paths**, not just their
names. `pairCount7` counts coupling entries whose decoded paths equal the
requested pair. `pairing7` divides that count by the actual coupling length
using exact `Rat`. `distribution7` retains exact numerator/denominator pairs.
Raw history injectivity in the gate ensures the four reference labels form
an exact, nonduplicated observation domain.

`recombination7` combines the branchwise record with the computed joint
observable. `Strict7` checks the pinned two-assemblage strict refinement.
`Local7` checks each indexed reassembly against the fixed diagonal/crossed
construction rule and its actual two-edge, nonduplicate coupling.
`Histories7` checks support of every history using assigned policy/rows.

`mixed7` checks the **assigned** events for atomic mixed support and both
realized endpoint stages. `active7` computes the declared receiver activation.
`receiverDisplay7` is a defined operation: it returns the computed joint display
only with realized mix and activation, otherwise no display. `Operational7`
gates on both conditions, actual display distinction, and assigned policy-row
agreement with the assigned pinned P. `operational7_iff_raw` shows its exact
relationship to the equivalent L6b gated raw-display condition.

`C7Transport` compares source/target observable families, branch records,
couplings, and computed distributions, with both gates. The canonical and
control equivalences hold on both tags. `controls7_branchwise` is a **decoding**
bridge from the old history-name lists to actual paths; `controls7_count`,
`controls7_pairing`, and `controls7_distribution` check the old/new exact
probabilities. `assigned_joint_distribution_probability` proves total numerator
mass two and denominator two for every adapter. `assigned_exact_joint_probabilities`
recovers the declared one-half entries.

The operational readout is designed to use the joint relation; this remains
a synthetic surrogate behavior, not independent causal corroboration.

## Locality

`extra_locality` is derived from the G2a generic `decoder_locality`.
There are separate `c4/c5/c7_gate_locality` and `c4/c5/c7_acceptance_locality`
theorems. `c5_transport_locality` and `c7_transport_locality` use the union of
the two defined clause scopes. No independently supplied verdict, decoded
record, credit, quotient, distribution or locality proposition is an acceptance
argument. The future reference gate also has `future_references_locality`.

## Declared mutation outcomes

Every adapter is a pure raw edit using `put`/`mapCell`. Missing cells remain
missing. `mapCell_other_cell` proves its footprint. The algorithms do not
receive variant names; `controls5/7` only construct compatibility assignments.

| Mutation | Local outcome | Staged outcome / qualification | Theorem |
|---|---|---|---|
| `NEG-C4-EXPOSE` | C4 fails on both tags | Full HIDD non-exposure already fails on the baseline | `neg_c4_expose_outcome` |
| `NEG-C5-EXTERNAL` | Source C5 passes; target C5 fails, clockwise credit other | Raw generator/provenance edits, not a credit label flip | `neg_c5_external_outcomes` |
| `NEG-C5-INTERNALIZED` | C5 passes on both tags; scheduled credit remains other | C5 raw transport fails | `neg_c5_internalized_outcomes` |
| `NEG-C7-AGGREGATE` | C7 fails on both tags | Observable family removed; branch data unchanged | `neg_c7_aggregate_outcomes` |
| `NEG-C7-TRANSPORT` | Source passes; target fails | Target local reassembly remains consistent; transport fails | `neg_c7_transport_outcomes` |
| `NEG-C7-UNCOUPLED` | C7 fails on both tags | Both local reassemblies remain consistent | `neg_c7_uncoupled_outcomes` |

`canonical_c457` proves the positive instance on each tag.
`canonical_staged57` proves the two positive staged equations. This table
claims the requested C4/C5/C7 outcomes, not full 19-mutation lane attribution.

## Argument classification

| Argument/object | Classification | Treatment |
|---|---|---|
| `a,b : Assignment` | Raw data | Immutable optional typed primitive values; no proof fields. |
| `tag`, clause/history/assemblage/protocol IDs | Raw indices | Fixed finite domains and pinned protocol views. |
| Raw cell key/value or `f` in `mapCell` | Raw edit data | Pure transformation, used only to construct mutations/probes. |
| `d : ExtraInputs` in raw rule lemmas | Raw representation | Acceptance **defines** d by scoped decoding; no candidate-record parameter. |
| `Agrees` premise, scope membership, edit-key inequality | Evidence on raw data | Pointwise equality or checked index relations. |
| Compatibility variant enum | Raw intervention choice | Used only by adapters; absent from acceptance signatures. |
| `transportScope` and clause scopes | Defined objects | Fixed dependency closures/union; not supplied acceptance parameters. |
| M/current view, history support, connector, credit | Defined objects | Computed from assigned raw values. |
| Branchwise/recombination state, pairing/distribution | Defined objects | Computed from actual paths and raw couplings. |
| Mixed-event evidence, activation and receiver display | Defined objects | Computed from assigned events/realization/receiver inputs. |
| Route register tuple | Defined object | Computed from raw route plus history references. |
| Lineage/autonomy premises | Absent | No such evidence parameter is used by these clause checks. |

## Field coverage and guards

All names are in `CSTTT.POS04.Assigned`. Guards are method-level sensitivity
probes, not new scientific model declarations or exhaustive isolation claims.
They alter one cell or one subfield of a cell. Housing's guard is staged,
not a fabricated local credit failure.

| Cell/field family | Check/law | Guard |
|---|---|---|
| Presence of any required C4/C5/C7 cell | `Complete` via `Ready` | `c4_missing_rejected`, `c5_missing_rejected`, `c7_missing_rejected` (all assignments/cells) |
| Scoped decoding | Defined filtering, `extra_locality` | G2a `scope_deletion_rejected` still covers expanded scopes |
| Shared histories | Nonempty supported paths; C4 endpoint/length; C7 actual-path injectivity | `c4_histories_guard`, `c5_histories_guard`, `c7_histories_guard`, `c7_duplicate_history_guard` |
| Channel family | Computed collision and exposure | `c4_channels_guard`, expanded-channel declared control |
| Protocol generator edges | Forward/reverse cycle products | `c5_edges_guard` |
| Protocol provenance | Computed-credit owner consistency | `c5_owner_guard` |
| Protocol housing | Translated raw staged equation; deliberately absent from credit rule | `c5_housing_guard`, internalized declared control |
| Joint left/right branch records | Actual path-pair counts and proper refinement | `c7_left_guard`, `c7_right_guard` |
| Joint coupling | Pair counts, indexed local consistency, strict refinement | `c7_coupling_guard`, uncoupled declared control |
| Indexed reassembly | Equality with the named diagonal/crossed construction | `c7_reassembly_guard` |
| Joint observable family | Computed display/recombination | `c7_observable_guard`, aggregate declared control |
| Event table (new) | Atomic mixed support, non-exit event, realized endpoints | `c7_events_guard` |
| Realized stages (new) | Both endpoints of a mixed event realized | `c7_realization_guard` |
| Receiver source presence (new cell) | Activation conjunction | `c7_source_presence_guard` |
| Receiver funding | Activation conjunction | `c7_receiver_funding_guard` |
| Target receiver funding | Activation conjunction | `c7_target_funding_guard` |
| Routes (new; C6 preparation) | Nonempty path and source-history reference, coverage of both route IDs | `future_route_table_guard` |
| Writers (new; C6 preparation) | Required writer available on each referenced route | `future_writer_guard` |
| Any required future-reference cell | Completeness before reference check | `future_reference_missing_rejected` |

Rows, public positions, hazards, policy and published P/M use the same existing
cells. Their checks here are `RowsValid`, raw M/current readouts and M linkage,
supported edges, and C7's P anchor/reconstruction. G2a's field guards remain;
the declared generator/assemblage controls and new history/activation probes
exercise the new consumers. No second copy of those inputs is introduced.

Other members of the raw receiver/event records (latent factor, initial budget,
content/register-rule enumerands, event strictness) are not claimed to gate
C4/C5/C7 when those clauses do not read them. They remain raw data for C6 and
handoff consumers. Fixed connector/anchor indices and pairing templates are
protocol definitions, not supplied derived objects. The route tuple is derived;
there is no independently mutable register readout to cap or substitute.

## Self-review and remaining work

Trace: assignment → defined scope/decode → actual raw rule → predicate →
canonical/control bridge. The support rule explicitly rejects empty paths;
C7 does not certify an inactive display, un-realized mix, or duplicate raw
histories merely because their names differ. Provenance and credit are separate
raw/data-derived notions; housing alone does not change credit. Full HIDD
non-exposure is honestly documented as failing.

C6's closure-wide future observation/update laws and all-word sufficiency,
and C8's viability fixed-point proof, remain G2b-2. The preparatory reference
checks do not assert them. Generic staged/glued assembly remains G2c.

Verification receipts follow below.
## Verification receipts

- `cd lean && lake build`: exit 0, 308 jobs. Rebuilt C457 (2.1 s),
  C457Locality (1.7 s), C457Adapters (9.7 s), and C457Guards (2.7 s).
  No new warnings; existing replayed warnings remain.
- `scripts/validate_lean.sh`: exit 0, overall PASS. All 39 rows and 174
  registered declarations pass resolution and axiom checks. Source scan:
  0 placeholders, 0 high-confidence vacuity findings, 22 non-gating
  ignored-input leads. These include deliberate constant-data guard variants;
  they are not clause predicates stored as verdicts.
- Read-only `/tmp/g2b1_axioms.lean` probes: all 91 theorem declarations in the
  four new modules resolve; the union of dependencies is exactly within
  `propext`, `Quot.sound`, and `Classical.choice`. No untrusted axiom.
- Forbidden-construct scan of the new Lean modules: no matches.
- `git diff --check`: clean. The registry and inventory are unchanged.
