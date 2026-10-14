# G6d — owning raw-interface assembly boundary

**TTH-06 remains conditional.** This is a proved component boundary, not a
claim that all of the G0 contract or its promotion gate is finished. No frozen
statement, declaration, model, prediction or result is changed.

## Frozen target and result

The CST-TT-08 `exact_statement`, carried unchanged by the 09 row, is:

> A valid Temporal-FIACH certificate entails, as separate fields, integrated target realization, strict temporal lineage, and post-withdrawal autonomy; none of the three is inferred from either of the others.

`OwningHandoff.RawHandoff` (`Targets/GenericHandoff/RawHandoff.lean`) owns
raw package rules, stage/cover, source package rules, acquisition frames,
primitive views, typed maps, runtime instructions, historical acquisition,
resource instructions, routes and run-cell instructions. The factor,
endpoint, temporal presentations, public runtime, target assignment and game
semantics are **defined**. In particular callers cannot replace an endpoint
or factor presentation independently of those primitive views. Raw finite
endpoint coordinates use the committed common-coordinate interface; source
and receiver register frames remain separately typed. This does not assert
that arbitrary source/target alphabets have already been embedded in that
interface.

`Coherence` checks owner injectivity and distinct carriers, frame/schema
identities, equality of the closed dispatcher C6 rule with the frame-owned
primitive rule, all-context temporal simulation and record equations, and the
actual/historical target-execution span. These are equations on raw data,
not flags. `HandoffPass_F/O` additionally check the source package, the typed
staged/glued target package, complete runtime lineage, and a proof-bearing
StrictSparse game invariant. No free lane predicate is a structure field.

The generic theorems have the following exact shape (types and equality
instances are implicit):

```lean
temporalFIACHCertificateSoundness_generic_F
  (m : RawHandoff ...) (a : Assignment SC SourceValue)
  (h : HandoffPass_F m a) :
  IntegratedTargetRealization m a ∧ StrictTemporalLineage m a ∧
    PostWithdrawalFullAutonomy m a

temporalFIACHCertificateSoundness_generic_O
  (m : RawHandoff ...) (a : Assignment SC SourceValue)
  (h : HandoffPass_O m a) :
  IntegratedTargetRealization m a ∧ StrictTemporalLineage m a ∧
    PostWithdrawalOperationalAutonomy m a
```

The package proof consumes only `DispatchedPackage.Valid`; lineage only
`RuntimeLineage.CompletePass`; autonomy only its computed acquisition/resource
readiness and invariant. The invariant's soundness is proved by induction on
strategy-generated plays. Its fields are obligations against actual updater,
resources, package and all positive successors, not a stored autonomy proof.

`full_autonomy_implies_package` derives F's logical dependence at a genuine
entry. It is **not** used by the package soundness derivation. Version O has
three existential witnesses on the **generic named readouts** in
`POS04RawHandoff.temporalFIACH_three_lane_separation`.

`full_each_entry_exact` transports TTH-05 for every historical entry, using
`HistoricalFiniteAutonomy.Checked` and `Lift` as proved per-instance evidence.
It does not silently assume omitted context irrelevant. The finite constructor
remains sound and potentially incomplete; this is not a decision-completeness
claim for unrestricted run recipes.

## POS-04 receipts and exact scope

`POS04RawHandoff.raw` constructs the new raw value from the committed data.
`factor_decoder` compares the *constructed* seven-cell factor views on every
partial assignment, rather than asserting canonical equality alone.
`factor_iff`, `lineage_readout_iff`, `lineage_pass_iff`, and `lineage_iff`
compose this with the already-proved whole semantic adapter. Thus

```lean
OwningHandoff.StrictTemporalLineage (raw (protocol m)) m.assignment ↔
  POS04CompleteLineage.StrictTemporalLineage m
```

is hypothesis-free for arbitrary partial assignments. `package_iff` likewise
matches the complete named package readout. `coherence_of_lineage` discharges
the new public interpretation equations on every such assignment with actual
complete lineage; it is not a conjoined fixed-positive adapter.

`full_iff_af` and `operational_iff_ao` are also arbitrary-partial biconditionals,
but their left sides **explicitly contain the frozen, independently computed
nominal protocol**. They are not claimed to equate bare unrestricted games
with AF/AO. `protocol_failure_cases` retains the matching failure cases.

`positive_F/O` prove the owning component gate is nonvacuously inhabited.
The generic semantic controls are:

| Control | F: P,L,A | O: P,L,A | Receipt |
|---|---|---|---|
| Package deletion | F,T,F | F,T,T | `F_control_vectors`, `O_control_vectors` |
| Lineage deletion | T,F,T | T,F,T | same |
| Post-exit retention deletion | T,T,F | T,T,F | same; `withdrawal_no_games` directly rejects resource safety at every run |
| Exit relabeling | T,F,T | T,F,T | `relabel_vector`, `relabel_no_lineage` |
| Source recharge unavailable | T,F,T | T,F,T | `source_recharge_vector` |
| Source past ticks missing | F rejects; O passes | O passes | `missing_past_ticks_full_rejected`, `missing_past_ticks_operational` |
| Duplicate event-ID activation record | — | A passes | `duplicate_event_operational` |

Here the three main vectors and relabel/recharge outcomes are on **bare generic
game readouts**, not merely protocol-qualified predicates. In particular the
withdrawal negative uses the direct resource-closure impossibility theorem,
then the format-qualified-to-support-only implication. It is not a failed
nominal check used to infer semantic failure. `endpoint_deletion_no_lineage`
is a direct semantic negative. `wrong_owner_rejected` changes only the raw
schema's target carrier and rejects the enclosing coherence gate.

## Argument classification

| Argument / raw field | Class | What binds it |
|---|---|---|
| Cell/value families; source/target register families; coordinate/action/outcome/history/route/event/resource types | Raw interface | No POS-04 alphabet/cardinality in generic definitions; equality instances are interface data |
| `sourceClauses`, `package` (language, source scopes, stage, reference stage, cover, closed rules) | Raw tables/rules | Source rule acceptance; target totality, value preservation, source coverage, rule locality and checked gluing |
| `frames` source/target schemas, primitive cell views, raw frame rows/programs/readout recipes, audit paths | Raw tables/instructions | Defined presentations; `SchemaCheck`, temporal simulation and complete semantic execution checks |
| `schema`, `runtime` resource/acquisition/row/program/readout instructions | Raw tables/instructions | Shared execution, resource/game legality, actual ownership, withdrawal and supported-step laws |
| Embeddings, translation, snapshot maps, clock, owner, finite predictive images/projections | Raw typed instructions/maps | Checked all-context execution and presentation equations; owner injection/distinctness |
| Names/seeds, predictive/history/route coordinates, route instructions | Raw maps/tables | Seed coherence, full bridge laws, Indexed + Retained comparison, every-branch runtime links |
| Historical support/reset/response instructions and historical execution | Raw instructions | Eager dependency completeness, recorded support, activation/realization, target-execution span |
| `runCells` | Raw instruction program | PackageAt is evaluated at the actual run; game invariant proves same-package safety |
| Source assignment `a` | Raw input | Never modified or replaced by a supplied target assignment |
| Readiness, raw equations, invariant certificates, Checked/Lift | Evidence on raw data | Auxiliary invariant/lift obligations are proved against defined semantics |
| Target, factor, endpoint, public runtime, presentations, entries, closure, observers, games, verdicts | Defined objects | No argument supplies any of them |

## Field/readout coverage and guards

All names below are in `Targets/GenericHandoff`; reused guards remain unchanged.
This table distinguishes a semantic rejection from rejection of a sufficient
certificate. No unready/missing-input premise is paired with contradictory
readiness evidence.

| Field family | Check / law | Guard |
|---|---|---|
| Source clause primitives | Closed dispatcher acceptance on source assignment | `OwningHandoff.missing_source_primitive_no_pass` for every required cell |
| Stage, coordinate/value maps, reference map, scopes, cover/adjacency | `DispatchedPackage.Valid` / TTH-02 constructive gluing | Committed PackageEngine / POS04PackageEngine dropped-cell, value-change, incompatible-overlap controls |
| Dispatcher C6 primitive view/schema | Literal equality to derived target temporal rule | `mismatched_clause_primitives_no_pass` |
| Source/target factor rows, positions, hazards, policy, ticks, resources, ledger | Defined `factorView`; FactorTransport equations | Imported missing-factor and parameterized factor-field guards; exact `factor_decoder` |
| Raw carrier IDs and owner map | OwnershipCheck and game ResourceClosed | `wrong_target_owner_no_pass`; concrete `wrong_owner_rejected` |
| Frame stage/event/route/boundary/clock/owner interfaces | SchemaCheck and SharedExecution | FramePresentation interface selector guards; clock/owner guards |
| Row domains and weights | ExecutionLink exact rows + positive-support coverage | Missing-row, row-mismatch, outcome-omission regressions |
| Actual updater, counters, tick, progress, writer, record, residue, maintenance, owner, predictive readout | Frame-owned presentations, all-context simulation, closure-wide readout laws | PresentationCoherence row/update/readout guards; ExecutionFrontier semantic field guard; committed constant/capped controls |
| Snapshot roots/execution/maps | Actual source/target execution + complete bridge SemanticReadout | Committed source/relabeling and snapshot failures; no legacy-lineage implication used |
| Endpoint events/receiver/primitive inputs | Defined endpoint decoder and atRoute checks | `missing_endpoint_no_lineage`, `endpoint_deletion_no_lineage` |
| Atomic witnesses | Actual frame event availability | `missing_atomic_no_lineage` |
| Record events, realization, writers, clock | RecordLaws and computed arrow transport | Committed event/writer/clock/realization guards |
| Route comparisons and retained register | Indexed + Retained, shared endpoint, actual every-branch execution | RuntimeLineage empty-domain/constant-residue guards; route deletion control |
| Historical support, receiver reset, target entries | HistoricalAcquisition completeness and raw execution | Missing consumed inputs, duplicate-event and historical source-context diagnostics |
| Withdrawal, resources, response legality/normalization and advancement | StrictSparse invariant over actual plays, full positive support | Direct `withdrawal_no_games`; committed zero/empty/null-row and permutation/duplicate regressions |
| Run package cells | Closed dispatcher evaluated on runAssignment | Generic full-autonomy-implies-package; direct package deletion control |

## Remaining promotion obligations — no narrowing applied

1. Bind the **nominal protocol generically** from the shared raw fields, with
   the precise consumed dependency projection, and prove the exact final F/O
   gate adapters. The current bare generic games have correct soundness, but
   the exact AF/AO family wrappers retain a POS-04-specific computed protocol.
   Do not replace it with a free Boolean instruction or assume it follows from
   a game. Do not strengthen legacy AF/AO to hide the difference.
2. Complete the G0 **receiver-content/activation coherence**, including the
   all-coordinate relationship between the factor map, endpoint transfer,
   historical reset and actual receiver frame. Existing snapshot and actual
   transition laws are preserved; no unproved all-input content-sensitivity
   consequence is asserted here. Complete source-package/stage preservation,
   route-status and recognition **final-gate correspondence** with the frozen
   family surface (source acceptance and stage checks already exist in the
   new component gate, but the whole correspondence is not yet proved).
3. Finish the final RawHandoff contract's typed-interface scope and exact
   whole-gate adapter, retaining the ownership/public-presentation equations.
   The common coordinate presentation is the committed endpoint interface,
   not a silently advertised proof of arbitrary separately typed finite
   coordinate embeddings.

Consequently the generic theorem names above are **component soundness**;
this note does not call them a completed proof of the frozen TTH-06 contract.
The 09 row remains conditional. The final theorem/instance promotion gate is
not bypassed just because its three readout eliminations compile.

## Classification and verification

All new definitions/theorems and the ownership/component certificate
construction are **(b)** mathematical additions for TTH-06. There are no
renames, statement weakenings, or changes to existing Lean declarations.
The 09 evidence/ceiling/rationale and generated inventory record this partial
boundary; the exact row text and status are unchanged.

The extended transcription checker evaluates the **constructed owning factor
and record instructions**, compares their exact tables with frozen JSON, and
kernel-checks the universal adapters, positive certificates, semantic controls
and diagnostics. It does not present stored Lean Booleans as readout proofs.
The checks and current axiom receipt are recorded in `.validate-logs/owning-*`.

### Fresh checks

- `cd lean && lake build`: exit 0, 523 jobs, final cached build 1.37 s.
  Newly compiled owning module 6.3 s; POS-04 adapter 3.5 s. No new warnings.
- `scripts/validate_lean.sh`: exit 0, 39 rows, 325 evidence entries / 324
  unique names; 316 theorem-kind, 8 statement-only and 1 other definition.
  Zero placeholders, untrusted axioms or high-confidence vacuity findings;
  46 non-gating heuristic leads.
- All 51 new theorems individually `#check`/`#print axioms` probed: 48 use
  only standard axioms, 3 are axiom-free.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0, 38 planted drift
  checks caught; second run output byte-identical by `cmp`.
- `git diff --check`: clean. All 1,445 tracked CST-TT files/symlinks outside
  the authorized 09 registry are byte-identical to HEAD; only TTH-06 changes
  in that registry, with unchanged exact text and conditional status.

Self-review traced the owning gate to each component soundness theorem and
checked direct semantic negatives independently of gate rejection. The review
identified the explicit nominal-protocol and complete G0 receiver-interface
completion gates above; these are left open rather than advertised as proved.
This was self-review, not an independent Eddy review.

## Independent review and takeover verification (2026-10-09)

A fresh read-only Codex sub-agent (`gpt-6.1-sol`, high reasoning effort),
`/root/raw_handoff_review`, returned **ACCEPT — as component progress, without
TTH-06 promotion**. It inspected the raw definitions, all-partial adapters,
actual semantic negatives, source/missing-input guards, registered evidence,
and statement classification. Independent Lean import/axiom probes passed for
F/O soundness, lineage/qualified AF adapters, O separation, positive F, and
withdrawal rejection using only the three standard axioms. It found no blocking
mathematical or implementation defect. The three remaining promotion obligations
above are retained unchanged.

The reviewer identified stale historical ownership/assembly wording in the
current 09 ceiling. It now states the owning **component** assembly is proved
while complete contract and whole-gate correspondence remain open. The generated
inventory was refreshed. Its optional checker hardening was implemented:
each owning-probe extraction replacement must match exactly once, rejecting
missing/duplicate markers before any Lean probe can run.

Fresh takeover checks: `lake build` passed (523 jobs), `validate_lean.sh`
passed (39 rows, 325 entries, 316 theorem-kind, 8 statement-only, 1 definition;
no placeholders/high-confidence findings/untrusted axioms), and the transcription
checker passed with all 38 planted drifts caught. Validator receipt:
`lean/.validate-logs/run-20261009T124151-775676Z/report.json`.
Final post-review checks are recorded in `lean/.validate-logs/owning-takeover-*`.
