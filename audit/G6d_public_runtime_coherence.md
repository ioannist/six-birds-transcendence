# G6d: public constructed target and target-execution coherence

## Proved boundary and remaining gate

TTH-06 stays **conditional**. This seam binds the package, historical F/O
interpreter and complete lineage to one constructed target, one dependent cell
alphabet, one resource instruction family and one target register-frame span.
It does **not** complete every public coordinate-presentation equation or the
final `RawHandoff` assembly. No new exact equivalence failed.

`PublicRuntime.Raw` is polymorphic in the source/target cell families, all
register families, carriers/factors, actions, outcomes, disturbances, events,
stages, histories and routes. It contains raw programs and table decoders, not
supplied targets, verdicts, entries, observation functions or coherence flags.
The closed dispatcher/stage/cover constructs `target` once. The historical
resource schema, acquisition schema and resource instructions are **derived**
from the actual lineage runtime. There is no independently selectable copy.

The historical executor and actual dual-mode executor cannot be equated on
all source contexts: autonomy uses recorded source support, receiver reset and
funded target execution; lineage requires actual funded source execution.
Instead `historicalLink` and `RuntimeLineage.targetLink` share the actual
receiver program and the **same typed target embedding**. Their independently
checked `ExecutionLink.Laws` yield exact row and successor equality on that
frame, then equality on every supported word. Positive-support coverage is
required on both arms. This is neither root-only agreement nor representative
selection. No source funding/ticks are added to the autonomy lane.

## Main results

All names below are under `CSTTT.TargetTheory.GenericHandoff`.

| Theorem | Meaning |
|---|---|
| `PublicRuntime.package_target`, `lineage_target`, `endpoint_target` | All consumers read the same constructed global assignment |
| `resource_instructions`, `resource_schema`, `acquisition_schema` | Resource instructions and schemas are shared by construction |
| `resource_closed_iff`, `factor_inside_iff`, `withdrawal_iff`, `legal_iff` | Equal resource ownership/solvency and factor membership on every run, independently of whether a game exists |
| `frame_eq` | Historical and actual target execution use exactly the same frame embedding |
| `rows_eq`, `positive_successor_eq` | Exact list probabilities and complete updates agree on every target run / actual positive branch |
| `every_supported_word_eq` | Target execution agrees for all finite supported words, using the existing inductive execution-link theorem |
| `strict_sparse_iff` | Identical selected-response representation; no order or duplicate restriction added |
| `POS04PublicRuntime.autonomy_eq`, `target_eq` | Exact historical-runtime model and staged image, for every partial assignment |
| `package_iff`, `package_named_iff` | Exact package gate/readout adapters; the converse derives cell completeness from totality of the stage map |
| `full_iff_af`, `operational_iff_ao`, `lineage_named_iff` | Arbitrary-partial AF/AO and complete-lineage equivalences |
| `coherent_of_lineage`, `canonical_coherent`, `positive_readouts` | The checked target span follows from complete POS-04 lineage; the positive instance is nonvacuous |
| `full_implies_package` | AF implies P at a genuine entry; package soundness retains its own subcheck |
| `O_control_vectors`, `F_control_vectors`, `operational_named_separation` | Direct named readout outcomes, not gate-failure inferences |
| `relabel_vector`, `source_recharge_vector` | Complete lineage rejects both diagnostics while the appropriate historical games pass |

The O vectors remain `(F,T,T)`, `(T,F,T)`, `(T,T,F)`; F remains
`(F,T,F)`, `(T,F,T)`, `(T,T,F)`. These are transferred through proved
biconditionals, not recomputed by unrelated positive adapters.

## Argument classification

| Argument/field | Classification | Constraint |
|---|---|---|
| All type families and equality instances | Raw interface | No fixed POS-04 cardinality or alphabet in `PublicRuntime` |
| `package` language, stage, reference stage, scopes, cover, closed rules | Raw data | Existing `DispatchedPackage.Valid` and locality/gluing theorems |
| `lineage` source/receiver instructions, runtime, factor/record/endpoint tables, route recipes | Raw data | Existing computed lineage checks; presentation coherence remains explicitly outstanding below |
| `historicalExecution` row and program | Raw instruction data | Target span checks actual probabilities, domain/support coverage and successors against the receiver execution |
| `historical` support tables, activation, reset and response instructions | Raw instruction data | Historical acquisition readiness and entry interpretation; missing consumed cells reject |
| `runCells` | Raw per-cell instruction | Run assignment is evaluated on the actual run and the constructed target; game package safety must be proved |
| `a` | Raw immutable source assignment | Exactly one global target is constructed from it |
| `hl`, `hh` | Evidence on raw dependency completeness | No decoder default may establish readiness |
| `ll`, `lh` | Evidence on defined raw execution equations | Not Boolean law flags; every row/program/support equation is proved |
| Target assignment, schemas/resources, link objects, interpreted frame, rows, successors, entries, game/readout predicates | Defined objects | No supplied candidate argument |
| Auxiliary strategies/invariants | Proof-bearing evidence | Hybrid architecture: actual semantics must establish safety; no supplied autonomy proof |

## Coverage and guards

| Field family | Equation/check | Guard / receipt |
|---|---|---|
| Stage and cover | Defined dispatcher global; exact target passed to every consumer | Existing stage/cover guards; `target_eq` holds even for partial assignments |
| Resource schema/instructions | Derived from lineage runtime, no duplicate parameter | `resource_schema`, `resource_instructions`, `resource_closed_iff` |
| Shared run/coordinate alphabet | Same dependent register type, source/receiver embedding instruction on both target-span arms | `frame_eq`; `missing_target_frame_rejected` |
| Historical row | Exact list equality to receiver row at every frame | `mismatched_historical_rows_rejected`; `empty_rows_ready` plus `empty_rows_rejected` (only that row changed) |
| Historical updater | Complete successor equation on every actual positive branch and all supported words | `mismatched_historical_successor_rejected`; `identity_ready`, `identity_successor_rejected` (only the historical program changes); inherited coverage guards |
| Domain and support | Every positive outcome in declared domain on both arms | Existing omission regression and `ExecutionLink.Laws.supportCoverage` |
| Missing consumed row | Eager completeness before evaluation | `missing_historical_row_rejected` |
| Readout evolution | Existing receiver/source closure laws, actual runtime and game step laws | No new candidate readout; whole-run updates transported by `positive_successor_eq` |
| Named P/L/F/O outcomes | Exact semantic adapters, including protocol failures | `package_named_iff`, `lineage_named_iff`, AF/AO biconditionals and direct control vectors |

The empty-row and identity-successor guards are nonvacuous: the broken interpreter is ready, and the
canonical target receiver has a real positive row. The generic mismatch guards
state genuine rejection; they do not combine readiness and missing-cell
premises in a way that makes their antecedents contradictory.

## Precise remaining work

1. Publicly link the endpoint and factor coordinate presentations and record
   event/writer/clock presentation to the typed source/receiver execution
   frames and the closed dispatcher primitives. They already read the same
   global assignment; that alone is not an interpretation-coherence theorem.
   In particular the raw endpoint's common factor alphabet still needs its
   explicit projection to the separately typed runtime frames.
2. Finish `RawHandoff` with all these public raw bindings and computed F/O
   checks, the generic three-readout soundness theorem and genuine instance.
   Transfer the named O separation and all controls through that interface.
3. Extend transcription to that final interface and evaluate the registry
   faithfulness gate. No promotion is applied before those obligations.

Historical acquisition, StrictSparse representation sensitivity, explicit
positive-support coverage and the sound-but-incomplete finite constructor
remain disclosed. C4–C7 remain surrogates; nominal disturbance words provide
all-support robustness, not resource-shock robustness. The exact TTH-06 row
is unchanged. This seam is **(b)**, TTH-06: new raw public binding, checked
execution span, exact adapters and guards. No (a) changes, old declarations
unchanged. Frozen CST-TT-08 and model declarations remain untouched.

## Checks

- `cd lean && lake build`: exit 0, 518 default jobs; final incremental run
  6.80 s. `PublicRuntime` built in 5.7 s and `POS04PublicRuntime` in 4.2 s.
  No new module warnings; inherited replayed lint warnings remain.
- Inventory regenerated with `python3 -B scripts/validate_lean.py --write-inventory`.
  `scripts/validate_lean.sh`: exit 0, 39 rows, 254 evidence entries / 253 unique,
  245 theorem-kind, 8 statement-only, 1 other. No placeholders, untrusted
  axioms or high-confidence vacuity findings; 46 nongating heuristic leads.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0, 32 planted drifts
  caught (two new); repeated output is byte-identical by `cmp`. The universal
  adapters and both row/program negatives are also kernel-checked in the probe.
- All 47 new theorem declarations were probed with `#check` and `#print axioms`:
  standard three or fewer; three use no axioms.
- Forbidden-construct scan on the new modules: no matches. `git diff --check`:
  clean. Five frozen CST-TT-08 surfaces compared byte-for-byte with HEAD. Only
  TTH-06's 09 evidence/ceiling/rationale changed; status and exact text unchanged.

Self-review: the target/resource/frame span is substantive and inhabited; the
new raw-row and updater guards are separately ready. This does not establish
that arbitrary independently decoded endpoint/factor/record presentations
agree with those frames. That unproved hinge is kept in the registry gap list;
no final `RawHandoff` theorem or promotion is claimed. The lane adapters retain
all partial assignments and historical dependency diagnostics, not only the
canonical assignment. All additions are (b); no frozen statement is narrowed.

Ignored receipts: `lean/.validate-logs/g6d-public-*`. Final validator report:
`lean/.validate-logs/run-20261009T111019-370084Z/report.json`.
Work is uncommitted.
