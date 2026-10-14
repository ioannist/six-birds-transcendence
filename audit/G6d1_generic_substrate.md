# G6d-1 / G6d-1b — generic assignment substrate and finite viable sets

## Boundary and scope

This packet extracts polymorphic cells, scoped decoding, heterogeneous typed
stages and constructive dependent gluing. It also completes the G6d-1b finite
viable-set engine before its first use. TTH-06 remains **conditional**. No
registry, inventory, frozen model, evaluator, or existing theorem statement changes.
New definitions/theorems are **(b) mathematical additions**, supporting TTH-06
and the extraction of TTH-02. There are no (a) renames.

The public modules use arbitrary cell/index/value types; source and target may
have different namespaces and value families. No Tag, KState, Clause, canonical
assignment, fixed stage, star cover, disturbance alphabet or unit ledger occurs
in the generic modules. The cover's finite index list and finite scopes give an
actual enumeration of all covered cells (`covered_cells_enumerate`). The theorem
needs no globally enumerated value space: cell values can themselves be tables.

## Modules and construction

- `Targets/GenericHandoff/Substrate.lean`: dependent immutable assignments,
  decoder locality/missing guards, shared views, typed instruction language,
  defined mapped locals, totality/reference/value/source-coverage checks,
  arbitrary adjacency/scoped connectivity, constructive gluing, and guards.
- `Targets/GenericHandoff/POS04Substrate.lean`: exact legacy specialization.
- `Targets/GenericHandoff/ViableSet.lean`: monotone pruning, finite viable-union
  construction, fixed-point and greatest-containment theorems.
- `Targets/GenericHandoff/POS04ViableSet.lean`: exact C8/F algorithm equations.
- `CSTTT.lean`: imports the two adapters and their generic dependencies.

`mappedLocal` reads the source cell specified by the typed instruction. Missing
arrows, missing source cells and failed instructions stay `none`; no decoder
fallback is present. `StageTotal` checks presence and instruction totality;
`ReferenceCheck` compares raw source references, independently of equal-looking
values; `ValuePreserving` compares the actual translated assigned values to the
raw reference stage. `SourceCoverage` checks all declared source-scope cells,
without requiring bijectivity or an involution.

`firstCover` scans the raw index list for a scope containing the cell. It does
**not** scan for a present value: a missing local cannot be replaced by a
convenient different local. `glued` is defined from that selector and the locals.
`glued_restricts` applies TTH-01's scoped-path compatibility lemma to Sigma-valued
assignments, then extracts the dependent value equality. `glued_unique` proves
uniqueness among assignments satisfying the same restrictions. No choice-based
global assignment or supplied global appears. `restrictions_imply_compatible`
also proves that an actual incompatible overlap forbids a restricting global,
not merely that a sufficient gate fails.

The cover permits cyclic adjacency when each cell's carriers are connected. It
imposes neither a star nor a rooted tree. Cover validity is a raw structural
predicate; scoped paths are evidence of connectivity, not stored acceptance.
`DependenciesCovered` is an explicit scope-inclusion check. Later clause schemas
must **define** their required dependencies; it is not a caller-supplied verdict.

## Exact POS-04 specialization

The adapter's instruction is the legacy typed raw primitive-value operation.
Its interpreter applies that operation; it is never a clause-acceptance callback.
The generic modules do not restrict instructions to POS-04's swap recipe.

The following equations hold for arbitrary assignments, including partial ones:

| Generic object | Exact legacy link |
|---|---|
| immutable replacement | `put_eq` |
| scoped decoding | `decode_eq` |
| readiness and scoped equality | `complete_iff`, `agrees_iff` |
| mapped local assignment | `mapped_eq` |
| total map with reference source check | `typed_total_legacy_iff` |
| reference-stage value preservation | `values_legacy_iff` |
| source coverage | `source_coverage_of_legacy` |
| cover connectivity/coverage | `cover_checked` from any checked legacy cover |
| clause dependency inclusion | `dependencies_checked` |
| overlap compatibility | `compatibility_iff` |
| constructed global | `generic_global_eq_legacy` under checked compatibility |
| 160 logical views / shared references | `views_and_references` |

`total_legacy_iff` separately exposes the legacy swap-source restriction. It is
not imposed on generic stages. The stronger exact `typed_total_legacy_iff`
identifies it with the raw reference check in this specialization.

`canonical_stage_total`, `canonical_cover_checked`, `canonical_compatible` and
`canonical_global` provide concrete positive instances on **both tags**. Legacy
clause acceptance has not been replaced or generalized by this substrate packet;
C1–C8 generic rule extraction remains G6d-2. Thus these are substrate/stage/cover
results, not a generic TTH-06 certificate.

## Argument classification

| Argument | Classification | Role |
|---|---|---|
| Cell, Value, source/target cell families, Index | structural types | Dependent typing; no fixed finite carrier or value vocabulary |
| DecidableEq Cell/target/X | structural evidence | Scope membership, immutable replacement, finite subset computations |
| assignment | raw data | Partial immutable primitive values; absent inputs remain absent |
| translation instruction types and interpreter | raw translation semantics | Maps primitive values; contains no clause/handoff acceptance parameter |
| stage, reference stage, declared source scopes | raw data | Defined mapped values; totality, raw-reference and coverage equations |
| cover indices/scopes/adjacency | raw data | Finite selection and independently checked topology |
| scope required dependencies | schema-derived data in future clause adapters | Inclusion check, not an acceptance proposition |
| StageTotal, ReferenceCheck, ValuePreserving, SourceCoverage | evidence on raw data | Computed equations; no supplied mapped local |
| CoverCheck, EdgeCompatible | evidence on raw data | Coverage and scoped connectivity/overlap; no supplied global |
| local assignments in gluing lemma | gluing input data | In staging application they are **defined** mapped locals |
| mappedLocal, firstCover, glued | defined objects | All derived from the above raw data |
| finite carrier list and completeness proof | structural data/evidence | Enumerates comparison sets for the viability engine |
| retention function | component rule at the engine seam | Later operators defined from raw component data; not a lane verdict |
| retention monotonicity | evidence on the component rule | Explicit inclusion law, instantiated by proved POS-04 retention laws |
| comparison subset / its viability | comparison data and evidence | Containment theorem uses viability; never a supplied greatest set |
| powersets, prune, greatest | defined objects | Enumeration/filter computations |

`CellView` and `TypedReindex` are raw view/reindex utilities; their reads and
pullbacks are defined and propagate absence. `sequenceLanguage` defines typed
instruction composition, with `sequence_execution` proving the bind equation.
No TTH-07 handoff composition or preservation theorem is claimed here.

## Field coverage and guards

| Field | Constraint / law | Guard theorem(s) |
|---|---|---|
| cell/value type and arrow instruction type | dependent typing; outputs have target primitive type | Ill-typed replacement/arrow is not expressible; absence is expressible and checked below |
| assignment primitive | scope completeness and absent reads | `missing_rejected`, `decoder_missing`, `missing_any_cell_guard` for **every** POS-04 cell |
| shared coordinate/view reference | one cell identity; read only that cell | `view_locality`, `view_missing`, `views_and_references` |
| decoder scope | reads inside scope only | `decoder_outside`, `decoder_locality`; dependency omission guard below |
| stage arrow presence | StageTotal | `missing_arrow_rejected`, `dropped_map_guard` |
| stage source reference | ReferenceCheck plus SourceCoverage | `coordinate_change_rejected`, `coordinate_guard`, `source_coverage_rejected` |
| referenced source value | StageTotal presence | `missing_source_rejected` |
| primitive translation instruction | total execution and actual value equation | `broken_instruction_rejected`, `value_change_rejected`, `changed_value_guard` |
| raw cover enumeration | every cell has an enumerated carrier | `uncovered_cell_rejected`, `enumeration_guard` |
| cover scopes | coverage, scoped connectivity, dependency inclusion | `missing_dependency_scope_rejected`, `dependency_scope_guard` |
| adjacency | cellwise connectivity over declared edges | `disconnected_cover_rejected`, `adjacency_guard` |
| overlap values | EdgeCompatible | `incompatible_overlap_rejected`, `overlap_guard`, `restrictions_imply_compatible` |
| viable operator | monotone retention | `prune_mono`; monotonicity must be proved for each instantiated operator |
| viable candidates and invariant | full subset enumeration and viable containment | `filter_mem_subsets`, `greatest_contains_viable`, `greatest_viable`, `greatest_fixed` |
| unavailable response | retention false at every candidate/state | `no_viable_member_empty` |

The changed-value guard also breaks compatibility; it is a group sensitivity
control, not an isolated gluing ablation. A constant primitive that is well typed
is not generically invalid at the substrate layer; clause-content guards belong
to its raw schema in G6d-2. No arbitrary callback for acceptance has been added
to manufacture rejection or acceptance here.

## Viable-set engine proof and ordering

For arbitrary X with complete finite enumeration and arbitrary **monotone**
retention rule, `greatest` filters the enumeration by membership in an enumerated
viable subset. Any viable set can be normalized by filtering the complete
carrier list; that normalized set is among `subsets`. Monotonicity transfers
viability to this normalization, giving containment in `greatest`. A member's
witness viable subset is then contained in `greatest`; monotonicity yields
viability of `greatest` itself. Filtering this viable set is the identity,
proving the pruning fixed point. This works with duplicate enumeration entries;
claims concern membership/inclusion, not cardinality or probability sums.

`c8_engine_eq` and `full_engine_eq` prove exact equality to the existing C8/F
computations. `c8_retain_monotone` and `full_retain_monotone` instantiate the
engine's real hypothesis. `c8_generic_greatest` derives the existing model's
containment result from the new generic engine. Later G6d-2c and G6d-5a reuse
this engine rather than introducing it after its first use.

## Finite-factor lift: explicit outstanding gate

This packet does **not** lift a run to a controlled finite factor. The engine is
only a finite-set theorem. Before any later generic autonomy application,
prove that the projection covers **every response- or resource-relevant run
context**, and that projected rows, resource availability and update laws agree
throughout the computed closure. A record naming a projection is insufficient.
If that proof needs any new finite-context premise beyond G0/G6, **stop and
report it before proceeding** for the owner's decision. No such premise is
introduced by this packet, and no general run-level autonomy claim is made.

## Completion checks

Check receipts are recorded below after the final build, validator and axiom
probes. Frozen CST-TT-08 and the G6 declarations/results are unchanged.

- `cd lean && lake build`: **exit 0**, 354 jobs; final changed adapter build
  2.5 seconds, CSTTT aggregate 2.3 seconds. Only existing replayed warnings.
- `scripts/validate_lean.sh`: **exit 0**; all 39 rows / 210 row declarations
  resolve and have clean axioms. Placeholders 0, high-confidence vacuity 0;
  28 non-gating ignored-input heuristic leads are reported honestly. Final log:
  `lean/.validate-logs/run-20261001T101319-234195Z/report.json`.
- A generated `/tmp/g6d1-axioms.lean` imports CSTTT and probes **all 71 new
  theorems** with `#print axioms` through `lake env lean`. All 71 resolve;
  axiom union is exactly a subset of `propext`, `Quot.sound`, `Classical.choice`.
- Forbidden-construct scan over the four new modules: no matches.
- `git diff --check`: clean. Only the two audit notes, the four new modules and
  the two import lines changed. No model verdict was newly computed.

The next boundary is G6d-2's generic clause-rule extraction. The generic
RawHandoff assembly, acquisition/bridge, run-to-factor lift and autonomy
specializations remain later packets; no completed generic TTH-06 is claimed.
