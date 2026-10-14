# G6d: generic acquisition endpoint extraction

## Proved boundary

TTH-06 remains **conditional**. This seam completes the raw-table endpoint
extraction and its exact POS-04 adapter. It does not complete public
cross-component coherence or the final `RawHandoff` assembly.

`AcquisitionEndpoint` is polymorphic in cells and their dependent values,
factor coordinates, actions, outcomes, histories, routes, stages, event IDs
and owners. Its two carrier presentations have separate raw tables and owners
and a common coordinate alphabet. Separately typed runtime registers remain
in `RuntimeLineage`. The public binding still must check the coordinate
presentation against those runtime frames; this seam does not silently assume
that relationship.

The primitive decoders produce raw temporal tables, supported event records
and a receiver protocol. The following are defined by the rule, not supplied:

- predictive profiles from positions, hazards and action rows;
- route tuples from the priority raw-route lookup and history table;
- strict event checks and path continuity;
- activation by scanning **all** raw event records;
- target funding and normalized, strictly positive phase-2 responses;
- the received raw terminal coordinate and mapped target history;
- the typed terminal-event, profile and ownership equations.

The rule reproduces `G6_lane_spec.md:125–139`, the acquisition dependencies
at 104–145, and phase-2 support at 213–285. The original POS-04 endpoint
algorithm's three atomic-leg equations follow from the leg constructor itself
(`constructed_atomic_endpoint`), for arbitrary assignments and routes. They
are not independent supplied positive adapters. The coordinate-copy receiver
remains deliberately near-automatic; no independent causal corroboration is
claimed.

The decoder is eager: every declared input must be present. There is no
fallback in this decoder. The explicit raw coordinate fallback only totalizes
`getLastD` inside a subsequently checked nonempty path, matching the frozen
phase-2 algorithm. An empty path never passes. The comparison domain must be
nonempty.

## Main theorems

Names below are under `CSTTT.TargetTheory.GenericHandoff`.

| Theorem | Statement / role |
|---|---|
| `AcquisitionEndpoint.decoder_locality`, `locality` | Agreement on the computed dependency scope preserves decoding and acceptance |
| `AcquisitionEndpoint.missing_input`, `missing_rejected`, `missing_no_readout` | Any missing consumed primitive rejects before decoding |
| `AcquisitionEndpoint.receiver_state` | A passing comparison has a decoded route, a received terminal, the same terminal in the constructed target history, and a checked phase-2 execution |
| `POS04AcquisitionEndpoint.pass_iff`, `readout_iff` | Exact endpoint equivalence for **every partial** POS-04 assignment |
| `RuntimeLineage.complete_soundness` | `CompletePass raw a → StrictTemporalLineage raw a` |
| `POS04RuntimeLineage.generic_complete_iff` | `RuntimeLineage.StrictTemporalLineage (raw (protocol m)) (image m.assignment) ↔ POS04CompleteLineage.StrictTemporalLineage m`, for every partial assignment |
| `POS04RuntimeLineage.positive_complete_pass` | The positive runtime aggregate, including the extracted endpoint, is inhabited |
| `POS04RuntimeLineage.generic_O_control_vectors`, `generic_F_control_vectors` | Exact registered named-readout vectors transfer through the biconditional |
| `POS04RuntimeLineage.relabel_no_lineage` | Direct complete-execution relabeling rejection remains valid |

The old `CoreReadout`, `soundness`, `whole_iff`, `complete_iff`, and family
controls are retained. The old core theorem explicitly omits the endpoint;
the new generic complete adapter needs **no external POS-04 endpoint premise**.

O vectors are `(F,T,T)`, `(T,F,T)`, `(T,T,F)`. F vectors are `(F,T,F)`,
`(T,F,T)`, `(T,T,F)`. These are semantic readout vectors, not conclusions
inferred from failure of a sufficient check. Autonomy still uses the committed
historical-support game readouts, with selected-response StrictSparse.

## Argument classification

Every argument of `complete_soundness` is listed below; the expanded endpoint
arguments are included because they become part of `raw`.

| Argument / field | Classification | Constraint |
|---|---|---|
| Generic type families and equality instances | Raw interface data | No POS-04 cardinality, enum, owner or state type fixed |
| `raw` and existing source/target/runtime/factor/record/route instructions | Raw data | Existing independently checked execution, snapshot, closure-law, factor, arrow and Indexed/Retained rules |
| `raw.endpoint` coordinate types, schemas, finite lists, entry/exit identifiers, row scale, fallback and transfer instruction | Raw data | Interpreted by the endpoint rule; nonempty domain, actual support, profile, terminal, owner and receiver equations checked |
| Endpoint primitive bindings | Raw cell references and projections | Eager Option interpretation; computed scopes, locality and missing-input rejection |
| `a` | Raw immutable assignment | The same assignment is passed to all lineage components |
| `h : CompletePass raw a` | Evidence on computed checks | No supplied endpoint, class, future, dynamics, closure or autonomy readout |
| Decoded tables, profiles, tuples, activation, phase-2 check, receiver state, target history, endpoint outcome, bridge/corridor/future objects | Defined objects | Not additional theorem parameters |

This is **not** a table certifying absent public coherence equations. One
assignment can be read by different instructions; it does not alone prove that
their coordinate/owner interpretations agree.

## Endpoint field coverage and guards

| Raw field family | Law/check | Guard or adapter |
|---|---|---|
| Both temporal input scopes | Eager decode of both scopes; exact union equals frozen `acquisitionDependencies` | `scope_iff`; `missing_endpoint_rejected` covers every cell in either scope |
| Source rows and policy | Every recorded source edge has positive computed weight | `supported_eq`, `phase2_eq`; missing source-row/policy cases of `missing_endpoint_rejected` |
| Target rows, policy and outcome domain | Supported mapped path; nonempty phase-2 row, declared normalization and every listed entry strictly positive and in domain | `path_eq`, `phase2_eq`; missing target-row/policy cases of the same guard |
| Positions, hazards and action alphabet | Predictive profile computed from raw data on both sides | `at_route_eq`; missing position/hazard cases |
| Route and history tables | Priority tuple resolution; nonempty paths; equality of compared tuples; actual receiver terminal | `tuple_eq`, `received_eq`, `target_history_eq`; missing route/history cases |
| Event records and realization | Strict adjacent event steps, continuity, entry/exit stages, target-only terminal support | `event_eq`, `strict_eq`, `path_eq`; `exit_deleted_no_endpoint`, `exit_deleted_no_lineage` |
| Receiver presence/funding/mixed requirement | All-record activation; raw coordinate operation then terminal equality | `active_eq`, `received_eq`; `constant_receiver_rejected`, missing receiver case |
| Resource owner and ledger | Target recharge availability, solvency and positive next budget; both owner equations | `available_eq`, `at_route_eq`; missing resource/ledger cases |
| Writers and ticks/interface/reference inputs retained by frozen dependency contract | Required input presence, target phase-2 writer; full temporal laws remain independently checked in runtime core | `decoded_complete_iff`, missing writer/tick/interface/reference cases; inherited runtime closure-law guards |
| Comparison domain | Nonempty source route list; every route checked | Nonempty conjunct in `Pass`; concrete finite domain adapter in `pass_iff` |
| Atomic carrier and terminal predictive projections | Derived from the leg constructor, not stored | `constructed_atomic_endpoint` |

`deleteExit` deletes **only** the referenced exit event, while all dependency
cells remain present (`exit_deleted_complete`). The endpoint rule and the
complete semantic lineage reject it directly. The separate missing-cell guard
also rejects whole event-table deletion for every partial assignment. A raw
constant receiver operation is rejected without changing the other inputs.
These guards do not combine readiness with a contradictory missing-cell premise.

## Remaining public coherence and assembly gates

1. Bind the closed dispatcher stage/cover and historical F/O runtime so that
   the target assignment is constructed once and read by package, games and
   lineage. Prove their public target equations.
2. Check endpoint/factor/record coordinate and owner projections against the
   shared acquisition execution, event tables and full readouts. The endpoint
   interface is now a raw component, but its common factor alphabet and decoder
   references must be linked to the runtime's separately typed frames; merely
   collecting them in a record is insufficient.
3. Relate historical autonomy's target-only execution and receiver reset to
   lineage's funded actual execution on the relevant target contexts. Historical
   source support must not be strengthened to funded source execution. The
   source-recharge and missing-source-tick diagnostics remain required.
4. Assemble final polymorphic `RawHandoff`, F/O soundness, generic AF⇒P, the exact
   instance and named O separation over that interface. Preserve StrictSparse,
   positive-support coverage, and the sound-but-incomplete finite constructor.

No exact claim failed in this seam. No narrowing or status promotion is applied.
The generic endpoint component is not presented as a completed public coherence
proof or a completed G0 `RawHandoff`.

## Statement changes and verification

All additions and the new `RuntimeLineage.Raw.endpoint` field are **(b),
TTH-06**: raw endpoint extraction, a strengthened aggregate and exact adapters.
No (a) porting changes. Old declaration statements are retained; adding the raw
field changes the raw interface type, not any frozen registry statement.
CST-TT-08, frozen declarations/results, and `paper/` remain untouched.

The transcription checker exports actual decoded receiver coordinates, paths,
histories, endpoint checks and protocol parameters. It compares all four G6b
endpoint outcomes and raw coordinates against the frozen JSON, adds four drift
checks, and kernel-checks the arbitrary-partial complete adapter. The legacy
G6b lineage Boolean remains explicitly weaker than complete semantic lineage.

### Fresh receipts and self-review

- `cd lean && lake build`: exit 0, 516 default jobs, 5.07 s incremental;
  the final endpoint and runtime adapter builds took 3.0 s and 1.8 s.
  No new module warnings; inherited replayed lint warnings remain.
- `scripts/validate_lean.sh`: exit 0. Inventory matches; 39 rows,
  238 evidence entries / 237 unique, 229 theorem-kind, 8 statement-only,
  1 other definition. No untrusted axioms, placeholders, or high-confidence
  vacuity. There are 46 nongating heuristic leads: 45 existing ones plus
  `POS04AcquisitionEndpoint.lean:251` (`constantReceiver`), an intentionally
  rejected sensitivity control, not positive evidence.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0; 30 planted
  drifts caught (four new). A completed second run is byte-identical by `cmp`.
- A read-only `/tmp` `#check`/`#print axioms` probe covered all 74 theorems
  across the four affected modules, including the 35 retained core/adapter
  theorems. All resolve and use only the standard three axioms or fewer.
- Forbidden-token `rg` scan: no matches. `git diff --check`: clean. Five frozen
  CST-TT-08 status files were explicitly compared byte-for-byte with HEAD;
  other 09 rows are unchanged, and TTH-06's exact statement/status are unchanged.

A transient shared-filesystem ENOSPC prevented one attempted scratch rerun;
commands recovered, the audit note was checked intact, and the rerun above
completed. No global cleanup or unrelated-file change was made.

Self-review: this is a real raw-table endpoint interpreter and an exact
arbitrary-partial adapter, not a final G0 handoff proof. Its common coordinate
alphabet is explicit; coherence with separately typed runtime frames remains
required at the public boundary. The independently decoded factor, record,
endpoint and runtime components are not made coherent merely by passing one
assignment. Consequently TTH-06 stays conditional and the exact gap list above
is retained. No new counterexample to an exact adapter was found.

Ignored receipts: `lean/.validate-logs/g6d-endpoint-*`; validator JSON:
`lean/.validate-logs/run-20261009T103151-905662Z/report.json`.
Work remains uncommitted.
