# G6d: shared runtime routes and execution representations

## Proved boundary and promotion decision

This seam binds the route and actual-program components to the shared runtime,
and rebuilds the **complete POS-04-family** named lineage readout with that route
binding. It does **not** finish the polymorphic complete-lineage aggregate or
`RawHandoff`. TTH-06 stays **conditional**, with its exact statement unchanged.
The new evidence is explicitly family evidence in the 09 surface.

There is no new failed exact claim or adjudication. The existing relabeling
counterexample remains a direct negative of the complete semantic readout.
`paper/`, CST-TT-08, declarations, and frozen evaluation results are untouched.

## What is proved

- `RuntimeComponents.route` defines acquisition, register and owner from one
  `RuntimeComponents.Raw`. Only the raw provenance, probe and endpoint
  instructions are additional inputs. The owner comes from the required raw
  resource account, not a supplied carrier label.
- `RetainedRouteReadout` retains the entire `Indexed`/`Retained` comparison:
  distinct raw paths, distinct provenance and defined probes, a shared computed
  arrival endpoint, nonempty response support and retention on **every** branch.
  `retained_route_status_iff` binds status to this full readout; no comparison is
  declared flat. `retained_result_shared` links every result to the actual
  resource rows and updater.
- `POS04RuntimeRoute.semantic_iff` is a biconditional for **every partial
  assignment and withdrawal protocol**:

  ```lean
  RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions a ↔
    Complete POS04RouteExecution.dependencies a ∧
      POS04RouteReadout.RouteReadout a
  ```

  The account-based owner reads the ledger as well as the target resource.
  Acquisition already consumes both, so this does not strengthen the old
  arbitrary-partial route gate. `ready_iff` proves the exact dependency domain.
  Reversing the raw source histories passes, with probes `[1,0]`.
- `ExecutionLink` interprets a raw typed register embedding and checks raw
  domain, list-level row and successor equations on **all run contexts**.
  `supported_word_iff` and `supported_fold` prove support preservation and
  execution transport by induction on every finite supported word.
  `normalized_iff` and `strict_sparse_iff` preserve response normalization and
  the selected-row format. No branch is replaced with a predictive representative.
- `POS04RuntimeExecutionLink.checked` instantiates these equations for either
  tag, from the five-register G1c execution to the carrier/run acquisition
  frame. The source and receiver execution objects are identified by
  `g1c_source_execution` and `g1c_receiver_execution`. All contexts and ambient
  branches, including the distinct exits, are covered.
- `historical_laws` links the historical target updater to that same actual
  target program, independently of source execution. `historical_pass_iff`
  proves its exact four-cell dependency domain:
  `rows.target`, `ticks.target`, `maintenance`, `resources.target`.
  This is an updater link, not the entire acquisition protocol gate. Historical
  entries still check all of their separately declared consumed inputs.
- `POS04SharedRuntimeLineage.whole_iff` is the exact whole **family semantic
  readout** adapter for arbitrary partial assignments:

  ```lean
  StrictTemporalLineage m ↔ POS04CompleteLineage.StrictTemporalLineage m
  ```

  It preserves corridor, executed seeds, factor and record laws, typed endpoint,
  full route comparison and whole-closure actual execution transport. The
  last obligation is independently mandatory; it is not inferred from the
  legacy acceptance predicate or from equal M classes. The new representation
  links are derived by `actual_runtime_links` and `historical_runtime_link`,
  rather than inserted as bookkeeping conjuncts in the semantic readout.

### Named readout controls

`POS04SharedRuntimeLineage.F_control_vectors`, `O_control_vectors`, and
`operational_named_separation` transfer the direct semantic outcomes by the
biconditional above, never by contraposing a sufficient gate.

| Raw control | P | complete L | F | O |
|---|---:|---:|---:|---:|
| Positive | T | T | T | T |
| Package deletion | F | T | F | T |
| Lineage deletion | T | F | T | T |
| Withdrawal deletion | T | T | F | F |
| Relabeling (`relabel_vector`) | T | F | T | T |
| Source recharge unavailable | T | F | T | T |
| Missing past ticks | not asserted here | F | existing F rejection | T |

`missing_atomic_no_lineage` and `relabel_no_lineage` reject the complete named
readout directly. `legacy_not_sufficient` preserves the counterexample to the
old weaker readout implying the complete one. Missing past ticks still pass the
historical target execution link but fail actual source execution in lineage.
Full autonomy additionally consumes package primitives; its existing rejection
of missing past ticks comes from that package scope, not funded source history.

## Argument classification

| Argument or object | Classification | Constraint / derivation |
|---|---|---|
| Generic finite interface lists, carrier ids, clock | Raw schema data | Existing domain and corridor checks; execution link checks matching declared domains |
| Shared `RuntimeComponents.Raw` | Raw instructions and typed views | One execution object owns acquisition and resources; route register and owner are projections |
| Immutable partial assignment | Raw data | Eager Option reads; no defaults enter a readiness witness |
| `RouteInstructions` provenance, probe, endpoint | Raw typed instructions | Interpreted on raw histories/paths and actual runs; full comparison, definedness and branch retention |
| `ExecutionLink.Raw.source/target` | Raw execution programs | Required list/domain equations and all-run successor equations; enclosing POS-04 instance selects its actual programs |
| `ExecutionLink.Raw.embedding` | Raw typed coordinate instructions | Complete dependency check, interpreted by `embed`; all-run row/update equations |
| `Ready`, `Laws`, `Complete`, response/resource proofs | Evidence on raw data | Every obligation is against the defined interpreter |
| POS-04 withdrawal protocol | Raw withdrawal metadata | Route equivalence holds for every protocol; it does not certify withdrawal viability |
| POS-04 run frame / register encoding | Defined representation | Raw coordinate packing plus proved all-run/all-word execution links |
| Rows, embedding, successors, folds, results, status | Defined objects | No independent candidate argument |
| `POS04SharedRuntimeLineage` | Defined semantic family readout | Same staged assignment throughout; independent complete execution readout required |
| Auxiliary autonomy invariants/lifts | Proof evidence, unchanged hybrid contract | Obligations remain against actual raw semantics; no finite-context irrelevance assumption |

`ExecutionLink` is an interpretation-level proof engine, not the public
`RawHandoff` boundary. Its raw programs must be bound by the enclosing component
interface, as explicitly done for the POS-04 specialization. Its existence does
not make disconnected arbitrary programs a handoff.

## Field and readout coverage

| Field / obligation | Law or check | Guard / regression |
|---|---|---|
| Disturbance/action/outcome domains | `ExecutionLink.Laws.disturbances/actions/outcomes` plus **row-derived source and target SupportCoverage** | `domain_mismatch_rejected`; `omitted_source_support_rejected` / `omitted_target_support_rejected`; `ExecutionLinkOmission.omission_rejected` |
| Raw rows, all contexts | `ExecutionLink.Laws.rows` | `rows_mismatch_rejected`; `uniform_rejected` has a separate `uniform_ready` witness |
| Actual updater, all contexts/branches | `ExecutionLink.Laws.successor` | `successor_mismatch_rejected`; `identity_rejected` has a separate `identity_ready` witness |
| Source/target program inputs | `ProgramReady` for both actual updaters | `missing_source_program_rejected` / `missing_target_program_rejected` |
| Embedding coordinate inputs | `Ready` and `embed_equation` | `missing_embedding_rejected` |
| Source-row inputs | `ExecutionReady` | `missing_source_row_rejected`, `POS04RuntimeRoute.missing_source_rows` |
| Acquisition events/realization/histories/receiver | Acquisition readiness and actual `Arrival` | `missing_route_input_rejected`, `missing_atomic`, and inherited `RouteComponent.source_absent_rejected` |
| Target response support | Normalization, positive support, actual shared updater | `missing_target_rows`; existing `RouteComponent.no_result_rejected` |
| Account owner | Defined required-account read; `route_owner_from_resources` | `wrong_account_owner`; generic `RouteComponent.owner_mismatch_rejected` |
| Ledger consumed by owner and execution | Exact `ready_iff` / `historical_pass_iff` | `missing_ledger`; no source-tick/funding dependency added to historical updater |
| Raw route identity / comparison domain | Full `Indexed` | `empty_domain_no_retained_routes`, inherited `constant_paths_rejected` |
| Retained register / residue | Runtime resource residue instruction, every resulting branch | `constant_register_no_retained_routes`; inherited constant-register guard |
| Defined distinct future probe | Raw probe instruction interpreted after actual step | Inherited `undefined_probe_rejected` / `constant_probe_rejected`; `reversed` passes without baseline 0/1 gate |
| Shared endpoint | Full `Retained`, every activated arrival of the comparison | Inherited `endpoint_mismatch_rejected` |
| Computed status | `retained_route_status_iff`, full `Indexed`/`Retained` | `retained_route_never_flat` |
| Predictive, order, tick, progress, writer, record, residue, maintenance, owner | Existing complete `ExecutionBridge.SemanticReadout` and whole-closure `ReadoutLawGate` retained unchanged | Existing G1c/RegisterFuture per-field guards; actual bridge relabeling negative retained |
| Funded actual source vs historical autonomy | Separate actual and historical interpreters, same assignment | `source_recharge_diagnostic`, `missing_source_ticks_no_lineage`, `missing_source_ticks_historical_link` |

The final row above the acquisition distinction is **not** a claim that a new
polymorphic runtime/bridge readout adapter is finished. The existing family
bridge has those laws. Generalizing its complete readout binding remains a
promotion gate. This seam's execution link covers programs, not a substitute
full observation interface.

## Statement changes

- **(a): none.** No existing theorem was renamed or changed.
- **(b), TTH-06:** additive raw shared-route binding, all-run register execution
  links and their inductive consequences; exact new family semantic adapter and
  direct controls. Existing support-only, format-qualified and legacy/family
  readouts remain unchanged. No narrowing of the frozen row.
- The 09 row receives related family evidence and an explicit gap update only;
  its status stays `conditional`. Inventory regeneration follows it.

## Remaining promotion gates

1. The complete **polymorphic** lineage interface must extract factor, record
   and typed-endpoint laws alongside source/receiver frontiers and shared route
   instructions from the public raw runtime. Keep the complete observation
   links; the present all-run program link alone does not establish those.
2. Bind those components with the generic stage/cover/closed dispatcher and
   historical F/O games into `RawHandoff`, with no independent derived object or
   interpretation parameter left at the public theorem boundary.
3. Prove final generic F/O soundness, generic AF ⇒ P, and transfer the instance
   and O named separation to that **polymorphic** interface, including the
   diagnostics and relabeling control.
4. Extend transcription to the final aggregate, then apply the FAITHFUL
   registry gate. The current transcription still checks the committed G6 data
   and legacy controls; the new family readout/route/execution links are linked
   by kernel theorems, not exported stored Bool verdicts.

Ceiling to retain throughout: finite typed raw interfaces; declared nominal
words with all-support robustness, no resource-shock robustness; POS-04 C4–C7
surrogates; autonomy acquisition is **historical support** and lineage
acquisition **funded actual source execution**; StrictSparse is selected-response
and representation-sensitive (zeros rejected, no order/duplicate rule); the
finite invariant constructor is sound and potentially incomplete. Its lifting
laws are proved per instance, never assumed generically.

## Checks (before the support-coverage correction)

- `cd lean && lake build`: exit 0, 512 jobs; final incremental build 13.31 s.
  Replayed older linter warnings remain; no new module warnings.
- `python3 -B scripts/validate_lean.py --write-inventory`: regenerated only
  TTH-06 metadata/evidence. `scripts/validate_lean.sh`: exit 0; 39 rows,
  217 declaration entries (216 unique), inventory match, no untrusted axioms.
  Scan: 0 placeholders, 0 high-confidence vacuity findings, 40 existing
  nongating heuristic leads.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0, including its
  planted-drift checks. Its documented legacy/family scope stays unchanged;
  no final polymorphic aggregate has been claimed or added to that export.
- `/tmp/g6d_shared_runtime_axioms.lean`, through `lake env lean`: all 81
  new theorem names resolve; their axiom union is exactly the standard three.
- Forbidden-token source scan: no matches. `git diff --check`: clean.
  Among tracked `cst-tt/` files only the 09 CSV differs; CST-TT-08 stays
  byte-identical. No edits to `paper/`. Work is uncommitted.

Logs are under the ignored `lean/.validate-logs/` directory with prefix
`g6d-shared-runtime-`. The proof note and six new modules form this reviewable
boundary; the remaining generic interface work above is not reported as done.

## Eddy fix: omitted positive support

The old matching-domain check was insufficient: equal outcome lists could both
omit a real positive branch. `ExecutionLink.SupportCoverage` is now computed
from the interpreted raw rows on **all** run contexts, and `Laws` requires it
for source and target. No Boolean flag or independent support table is supplied.
`positive_successor` and `supported_positive_step` derive the outcome-domain
condition from actual positive support. POS-04's `ambient_coverage` proves the
obligation using the exhaustive ambient enumeration, including both exits;
all arbitrary-partial adapters are preserved.

`ExecutionLinkOmission` reproduces Eddy's fair row `[(false,1/2),(true,1/2)]`
with domain `[false]`. `previous_checks_hold` proves all former domain/row/
listed-successor checks, while `actual_updates_differ` gives source 0 and target
1 on the positive true branch. `omission_rejected` directly proves no `Pass`.
Both readiness and positive support are separately proved, so the guard has no
unsatisfiable premises. No duplicate or ordering condition was added.

### Related-module sweep

| Component | Positive-support coverage mechanism | Disposition |
|---|---|---|
| `RuntimeRoute` / `RouteComponent.Result`, `Retained` | Results quantify over **every** raw-row positive outcome, without requiring membership in `execution.outcomes`; retention is over all those results | No analogous gap; unchanged |
| `AcquisitionExecution.HistoryExecution`, historical entries | Raw positive support; outcomes are not filtered by the advertised list | Unchanged |
| `StrategyGame`, finite game projection/constructor and autonomy lifts | Every positive-support outcome is quantified directly; step projection/full-support safety has no outcome-list filter | Unchanged |
| `ResourceRuntime.DomainCheck` | Exhaustive domain `(∀ o, o ∈ execution.outcomes)` | Already protected; unchanged |
| `ExecutionFrontier.ExecutionDomain` / `ExecutionBridge` | Exhaustive outcome domain required by both complete frontier gates | Already protected; unchanged |
| `ProfileRules.DomainCheck`, temporal factor acceptance | Exhaustive outcomes, plus raw row validation | Already protected; unchanged |
| Standalone `RegisterFuture.ReadoutLawGate` | Previously only checked advertised outcomes | **Fixed:** row-derived `ReadoutSupportCoverage` on the whole computed closure |
| `RegisterFuture.future` / `FutureLumping` | Interpreter/proof engine for its declared finite outcome sum, not an independent certificate about raw-row coverage | Coverage is enforced by the enclosing gates above; no new model/future argument |

The standalone readout gate now rejects omissions even without borrowing the
frontier's exhaustive-domain premise. `positive_branch_in_closure` derives
closure inclusion for every actual positive branch. `readout_omission_rejected`
tests that gate independently. Its advertised false branch passes all field
and positive-advancement checks (`readout_previous_steps`), while the omitted
true branch is nonadvancing. Closure restriction/locality and the POS-04
readout proofs transport the new check from the same raw rows.

**Classification:** (b), TTH-06, strengthens `ExecutionLink.Laws`/`Pass` with
the missing support-domain obligation. (b), TTH-03/TTH-06, strengthens the
shared `ReadoutLawGate` with the same raw-support requirement; dependent
semantic readouts inherit it. Proof repairs in `ReadoutFrontierRestriction`,
`ExecutionLocality`, `SemanticExecutionBridge`, `POS04RegisterReadoutLaws` and
`POS04ExecutionFrontier` preserve their existing signatures apart from that
shared definition strengthening. No status or frozen statement change.

### Correction checks

- `cd lean && lake build`: exit 0, 512 jobs, 317.77 s with the dependent
  readout/lineage modules rebuilt. No new warnings; older replayed warnings remain.
- `scripts/validate_lean.sh`: exit 0; 39 rows, 217 entries / 216 unique,
  inventory match, no untrusted axioms, no placeholders or high-confidence
  vacuity findings. Heuristic leads are 45: the five additions are deliberate
  singleton-register/initialization/branch-update constructions in the omission
  probes, not statement predicates. The scanner is unchanged.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0, planted drifts caught.
- `/tmp/g6d_support_coverage_axioms.lean` through `lake env lean`: 174 new and
  affected theorem probes resolve; standard axioms only.
- `git diff --check` and forbidden-construct scan: clean. No changes in this
  correction to registry/status/inventory, frozen data, or `paper/`; uncommitted.

Correction logs: ignored `lean/.validate-logs/g6d-support-coverage-*`.
