# G2c — assignment-sensitive staged package assembly (TTH-02)

## Claim and statement changes

The unchanged CST-TT-09 exact statement is:

> Separately typed, total, value-preserving source-to-target clause maps plus an independently valid target gluing certificate assemble one integrated target package without using lineage or autonomy premises.

**(b), TTH-02:** add a generic construction over the G2 typed primitive-cell substrate, with real assigned C1–C8 acceptance rules. The old `CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly` is retained unchanged as a schema-level theorem. It does not carry the promotion. C4–C7 retain their declared surrogate grades; this is neither a full P05 C-package nor T17-I. The 09 ceiling becomes **“C4–C7 surrogate clause content”**. No exact-statement change is applied.

Here “generic” quantifies over arbitrary immutable source assignments, raw typed stage operations, and checked target covers in this primitive namespace. The authoritative eight algorithms and the typed carrier-translation recipe are definitions, not freely supplied clause rules. This does not quantify over arbitrary alternative interpretations of C1–C8. Each tagged primitive has its own dependent `Value` type; shared cells remain single cells, and all 160 logical slots retain their existing views.

## Exact theorem and construction

Source: `lean/CSTTT/POS04/Assigned/PackageAssembly.lean:184`:

```lean
theorem stagedHeterogeneousPackageAssembly_generic
    (source : Assignment) (stage : RawStageMap) (cover : RawPackageCover)
    (targetTag : Tag) (hc : CoverCheck cover targetTag)
    (_hsource : AssignedPackagePass source (swapTag targetTag))
    (hmap : MapTotal source stage cover) (hvalues : ValuePreserving source stage cover)
    (htarget : TargetLocalChecks source stage cover targetTag)
    (hcompat : EdgeCompatible source stage cover) :
    AssembledPackage source stage cover targetTag hc
```

`AssembledPackage` (`PackageAssembly.lean:171`) asserts, for the **defined** global assignment:

- restriction equality on every cover scope;
- every primitive cell has a value;
- every assigned clause accepts that same global assignment;
- every hard gate holds on that same assignment;
- checked scoped value preservation and totality.

`assembled_global_package` (`:201`) exposes the existential assignment and its restrictions, acceptance, and gates. Acceptance dispatches to the actual `C1Accept` through `C8Accept` (`:12`); these decode supplied primitives and reject missing dependencies. C1 retains T1's uniqueness argument and C6 retains its all-word result. No acceptance predicate or target package witness is a theorem argument.

The raw arrows contain a typed source cell and an `Option`-valued operation (`:65`). `MapTotal` (`:107`) checks existence of the arrow, its expected source coordinate, a present source value, and operation totality on **all** primitive values. `stage_source_coverage` (`:113`) proves total coverage of the derived source scopes. The fixed `swapCell` translation is an involution; `translatedValue` (`:87`) preserves factor primitives while translating resource ownership, protocol provenance, and writer indexing. `ValuePreserving` compares actual operation outputs to this raw typed recipe at every scoped cell (`:122`). It is not a clause verdict.

`mappedLocal` (`:101`) binds the source cell to its raw operation and restricts to the cover scope; all other cells are missing. `TargetLocalChecks` (`:125`) evaluates the eight real rules on these **defined** local assignments. This is necessary evidence on the raw assignments, not a free `accepted : Clause → Prop` field. Source acceptance is independently checked; it is logically unused in the gluing proof once these computed target-local checks are available. The conclusion therefore holds in that stronger-in-part situation as well; the row's source-package premise is retained.

`CoverCheck` (`:47`) checks root, parents, ranks, cell coverage, running intersection, and inclusion of every clause's decoder scope. Adjacency is **defined** from parents. `EdgeCompatible` (`:128`) separately checks actual overlapping local values on those edges; it is not inferred from an acceptance label. On a globally value-preserving map it is redundant, but remains a separately evaluated check. No compatibility conclusion is a raw field.

`assembledAssignment` (`:134`) chooses a covering clause **from raw coverage**, not from a supplied global candidate. It uses standard `Classical.choice`; this is an exact definition, not an executable package-export algorithm. `assembled_restricts` (`:138`) applies TTH-01's `gluedAssignmentAgrees` to Sigma-valued locals, and extracts equality of the dependent primitive values. `assembled_complete` (`:163`) follows from map totality and restrictions. Finally, `clause_accept_locality` (`:22`) uses the eight previously proved locality theorems to transfer each local acceptance to the defined global. Acceptance implies its own hard gate (`:34`). This closes the former projection gap: global acceptance is **derived**, not stored.

### No lineage or autonomy premise

The exact signature above has no corridor, strict-lineage, receiver-content, bridge, withdrawal, or post-withdrawal autonomy argument. The construction exists without any such lane record. Operational C8 viability and the raw resources/receiver dependencies needed by individual clause rules are package content, not an additional autonomy-lane premise. This is the signature-level independence the packet requests; no proof of a corridor is used by the construction.

## POS-04 instance and nonemptiness

Source: `PackageInstance.lean:19–119`.

The positive cover is a **decoder-dependency closure of the star presentation**: C1's root view retains all primitive cells, and each other clause view is precisely its dependency scope. This padding is required by shared history/event/receiver dependencies added in G2b. It changes the cover presentation, not any frozen model values, acceptance rule, or the 160 logical views. C1 continues to read only its own clause scope. A root containing all shared cells proves running intersection without incorrectly treating the old logical slots as independent assignments.

| Evidence | Theorem |
|---|---|
| Every typed primitive is covered; star is valid | `primitive_cells_complete`, `arrival_cover_check` |
| Source arrival package, both tags | `canonical_assigned_package` |
| Typed value recipe matches the canonical model | `translated_canonical_value` |
| Stage totality and raw value preservation | `canonical_stage_total`, `canonical_stage_values` |
| Defined mapped locals equal canonical on their scope | `canonical_mapped_agrees` |
| Every computed target local accepts | `canonical_target_locals` |
| Independently checked edge compatibility | `canonical_edge_compatibility` |
| Generic conclusion instantiated | `pos04_staged_package` |
| The constructed global is exactly the canonical assignment | `pos04_assembled_assignment_canonical` |
| Canonical acceptance linked to L8 on both tags | `canonical_package_equivalence` |
| Actual assembled target acceptance and L8 `PackagePass` | `pos04_arrival_package_L8` |

The last equality makes the L8 comparison a comparison of the actual constructed assignment, not merely existence of a separate package. Canonical equivalences reuse all eight G2 clause bridges. The inhabited source assignment, map, cover and target local checks show the generic hypotheses are jointly satisfiable.

## Controls and their exact meaning

Source: `PackageGuards.lean:6–157`, `PackageControls.lean:7–50`.

| Raw intervention | Checked failure / theorem |
|---|---|
| Drop C2's target-row arrow | `dropped_map_not_total` |
| Point C2's row arrow at the wrong tag | `wrong_coordinate_rejected` |
| Make C2's hazard operation constant false | `changed_map_total` still holds; `changed_map_not_preserving` |
| Same operation disagrees with root on the overlap | `incompatible_overlap_rejected` |
| Change root only | `wrong_root_rejected` |
| Change parent only to a self-parent cycle | `cyclic_parent_rejected` |
| Change rank only to constant zero | `flat_rank_rejected` |
| Delete a required row from C2 scope only | `missing_scope_rejected` |
| Empty the assigned source action rows | `source_assignment_guard`, `package_hard_gate_guard` |

The incompatible-overlap probe **also fails value preservation**. It demonstrates actual gluing-check sensitivity; it is not an isolated gluing-only ablation. No isolated gluing failure with an everywhere value-preserving common source image is possible under these definitions.

`packageControl` applies existing raw primitive adapters, and `m3b_package_controls_reject` proves rejection through one selected real clause failure per intervention. It does **not** claim full shared-model failure attribution.

| M3b intervention | Selected failed clause |
|---|---|
| NEG-C1-TABLE | C1 |
| NEG-C2-SPLIT | C2 |
| NEG-C3-PROFILE | C1; C3 itself still passes, as recorded |
| NEG-C4-EXPOSE | C4 |
| NEG-C5-EXTERNAL | C5 |
| NEG-C6-FUTURE | C6 |
| NEG-C6-RECORD | C6 |
| NEG-C7-AGGREGATE | C7 |
| NEG-C7-TRANSPORT | target C7 |
| NEG-C7-UNCOUPLED | C7 |
| NEG-C8-UNDERFUND | target C8 |
| NEG-AUTONOMY-WITHDRAW | target C8 |
| NEG-ACTIVATION-SOURCE-ABSENT | C7 activation check |
| NEG-CORRIDOR-GAP | C6 realization check |

The exact model labels and transformations remain those of the prior adapters; no new frozen-data mutation is declared. `exchangeAssignment` is a derived namespace relabeling, proved involutive. `mapped_exchange_agrees` proves that applying the **same** positive stage to the exchanged mutated source gives exactly the mutated target primitives on scope. Thus `m3b_mapped_package_controls_reject` rejects the mapped local checks themselves, and `m3b_no_assembled_control` excludes a certified global equal to any of those rejected primitive assignments.

NEG-C5-INTERNALIZED is honestly different: `m3b_internalized_package_still_passes` proves local package acceptance on both tags, while `m3b_internalized_transport_still_fails` records the separate staged C5 transport failure. The row does not infer that local package acceptance automatically preserves every additional protocol-origin equation. Detached/copy/route controls affecting only handoff lanes are not asserted to break this package theorem.

## Argument classification

| Argument/object | Classification | Treatment |
|---|---|---|
| `source : Assignment` | Raw data | Immutable typed primitive values, decoded by clause rules |
| `stage : RawStageMap` | Raw data | Scoped source references and typed operations; no verdicts |
| `cover : RawPackageCover` | Raw data | Root, parent, rank, scope lists |
| `targetTag : Tag` | Raw data | Declared destination carrier; source is its typed counterpart |
| `hc : CoverCheck ...` | Evidence on raw data | Tree laws, coverage, running intersection, decoder dependencies |
| `_hsource` | Evidence on raw data | Source assigned rules; no separate witness supplied |
| `hmap` | Evidence on raw data | Raw reference/operation totality and source-value presence |
| `hvalues` | Evidence on raw data | Pointwise raw transport equation |
| `htarget` | Evidence on raw data | Assigned rules evaluated on defined mapped locals |
| `hcompat` | Evidence on raw data | Actual overlapping values on derived adjacency |
| Clause rules/gates, source scopes, mapped locals, checked tree/adjacency, global assignment and package result | Defined objects | Definitions/theorems, never candidate arguments |
| Corridor/lineage/post-withdrawal autonomy evidence | Absent | No parameter of the theorem |

## Field coverage

| Raw field family | Law/check | Per-field guard |
|---|---|---|
| Source assigned primitive values | Assigned source rules, required-input completeness, `MapTotal` | `source_assignment_guard` |
| Arrow availability | Existence in `MapTotal` on every target scope; inverse source coverage | `dropped_map_not_total` |
| Arrow source coordinate | Typed inverse equation `arrow.source = swapCell k` | `wrong_coordinate_rejected` |
| Arrow value operation | All-values totality plus actual `ValuePreserving` equation | `changed_map_not_preserving` (totality survives) |
| Cover root | No parent at root | `wrong_root_rejected` |
| Cover parent | Total nonroot parents, decreasing ranks; adjacency derived | `cyclic_parent_rejected` |
| Cover rank | Strict decrease along parent edges | `flat_rank_rejected` |
| Cover scopes | Full cell coverage, running intersection, all decoder dependencies included | `missing_scope_rejected` |
| Shared overlap values | Independently checked `EdgeCompatible` | `incompatible_overlap_rejected` |
| Clause primitive rule inputs | Eight fixed assigned algorithms and locality, not a supplied rule function | `m3b_package_controls_reject` (C1–C8 selected input controls) |
| Hard gates | Computed on the same assigned primitives; global acceptance implies gates | `package_hard_gate_guard` |
| Ownership/provenance/writer translation | Defined typed recipe, involutions, canonical raw equations | The primitive resource/protocol/writer controls above; no independently replaceable translation field |
| Target verdicts and glued assignment | Defined; restriction/locality proof | `m3b_mapped_package_controls_reject`, `m3b_no_assembled_control` |

No unused raw evaluator, free global, free gate table, or hidden lane evidence occurs. Coverage guards are concrete discriminating probes, not assertions that every possible constant field is invalid. All guards preserve immutable assignment semantics.

## Status and checks

TTH-02 is promoted from `conditional` to `proved` at the declared surrogate ceiling. The 09 row names the generic theorem, its global readout, POS-04 construction/equality/L8 bridge, and mapped-control theorem. The 08 row and all frozen model/spec/prediction files remain unchanged. Expected counts: **5 proved, 14 checked finite countermodels, 12 conditional, 8 open**.

Reproduction:

```bash
cd lean && lake build
cd ..
python3 -B scripts/validate_lean.py --write-inventory
scripts/validate_lean.sh
```

Build, validator and direct new-theorem axiom receipts are recorded below after the final run.

Final receipts:

- `cd lean && lake build`: exit 0, 323 jobs. New module compile times observed: assembly 2.9 s, instance 2.7 s, guards 3.8 s, controls 3.4 s; the final cached whole-build run took 0.29 s. No warnings originate in these four modules; existing vendor/legacy linter warnings are replayed.
- `scripts/validate_lean.sh`: exit 0, overall `pass`; 39 rows, 179 declaration entries (178 unique), all resolution and axiom checks pass. Scans: zero placeholders, zero high-confidence vacuity findings, 25 non-gating heuristic leads (including the deliberately broken constant parent/rank guards).
- `/tmp/g2c-axioms.lean` read-only `lake env lean` probes: all 44 new theorem names resolve; transitive axiom union is exactly `propext`, `Quot.sound`, `Classical.choice`. No `sorryAx` or `hiddenness_pending` dependency.
- `git diff --check`: clean. Row-by-row comparison against HEAD shows **only TTH-02** changed in the 09 CSV. The CST-TT-08 records and frozen POS-04 declaration artifacts have no diff.

Self-review: this is a conditional construction from raw equations and computed local checks, with a concrete joint instance, rather than an unconditional claim that arbitrary source packages survive arbitrary maps. A classical covering selector is used only to define the global assignment; locality/TTH-01 make the resulting restrictions independent of that selection. The extra source-validity premise and redundant independent compatibility check are disclosed above. Surrogate upgrades and full shared-model mutation attribution remain separate work; neither is claimed by this promotion.
