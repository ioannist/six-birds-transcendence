# G7 — actual staged assignments and executed raw namespace transport

TTH-07 remains **conditional**. This packet closes the raw assignment exposure
gap from the immutable-assignment bridge component. It constructs a common
typed primitive namespace from the two actual stage globals. Each raw program
reads its corresponding branch, and the complete executed frame and bridge
gates and semantic readouts are preserved in both directions for every partial
assignment. Physical middle agreement and the supported next acquisition
remain separate full-composition obligations.

## Argument table

| Argument/object | Classification | Constraint |
|---|---|---|
| Cell selector and typed value instruction | Raw syntax | Total value operation; Option mapping retains every missing primitive |
| Supplied primitive assignment | Raw interpreter input | Arbitrary partial assignment |
| Cell pullback | Defined interpretation object | Selected actual primitive, mapped by raw typed value operation; no cached value |
| Translated expression/program/initializer/views | Defined raw syntax | All cell reads translated recursively; register and environment coordinates preserved |
| Raw acquisition, future and executed frame | Defined raw constructors | Every instruction translated; schema, clocks, audit, event/environment domains retained |
| Raw bridge | Defined raw constructor | Both frames and actual register translation translated; all eight snapshot maps retained |
| Intermediate and final assignments | Defined stage outputs | Two actual PackageEngine.global calls with the original raw stages and covers |
| Common namespace assignment | Defined stage output | Disjoint Sum branches containing those computed outputs |
| Readiness and law witnesses | Evidence | Actual decoded/interpreted instructions; proof choices bound by evaluation equations |
| Numeric stages | Raw data | Existing add/multiply stages, existing cover and parameters |
| Partial-instruction control | Raw data | Reject above limit 3; complete source value 4 produces no output |
| Context-reuse control | Raw instruction mutation | Only final read redirects to middle branch; actual output differs |
| Native application | Existing raw package and execution model | Two POS04 package stages, actual original execution bridge in final branch |

The generic cell selector need not be injective. Its semantics is explicitly
the selected pullback, so the theorem does not infer independently selectable
source primitives from colliding target references. The public staged span
uses disjoint Sum injections and identity value operations, preserving the
independently computed middle/final contexts.

## Coverage table

| Obligation | Receipt | Scope |
|---|---|---|
| Expression evaluation/dependencies | CellReindex `evaluation/dependencies` | Every partial assignment; mapped raw dependency list, including repeats |
| Exact expression/program/initializer readiness | `complete_iff/ready_iff/program_ready_iff/initializer_ready_iff` | Every partial assignment, no success hypothesis |
| Actual program and initialized runs | `execute_equation/checked_execute_equation/initialize_equation` | Defined evaluation, no supplied derived run |
| Primitive/static decoders | `view_equation/cell_view_equation/view_dependencies` | Actual selected Option read and total typed raw operation |
| Direct missing primitive rejection | `missing_evaluation` | Actual translated expression evaluates to none |
| Actual future row/updater/readouts | FutureCellReindex `read_equation/observation_equation/row_equation/next_equation/weight_equation` | All runs and environment arguments |
| Whole interpreted future/dynamics | `future_equation/dynamics_equation` | Equality of all-state/all-word raw models, not finite observation equivalence |
| Complete readout-law gate | `field_expression/field_law_iff/positive_recipes_iff/readout_gate_iff` | All nine field instructions, advancement recipes, entire raw closure and support coverage |
| Actual acquisition | AcquisitionCellReindex `initial_equation/update_equation/receive_equation/rows_equation/fold_equation` | Entire interpreted raw instruction interface |
| Supported words and arrival | `history_check_iff/history_execution_iff/arrival_iff` | Same actual supported terminal and receiver, all declared paths/activation retained |
| Frame roots/audits/snapshots | FrontierCellReindex `roots_equation/history_prefix_equation/snapshot_equation/observation_equation` | Actual initializers and assigned word prefixes |
| Whole closure and supported audit execution | `closure_iff/prefix_check_iff/audit_check_iff` | Actual raw dynamics, including zero-weight successors |
| Every frame gate/readout conjunct | `execution_domain_iff/row_gate_iff/paths_available_iff/readout_gate_iff/checks_iff/valid_iff/semantic_checks_iff/semantic_iff` | Two-way exact complete frame validity and separately defined semantic readout |
| Every bridge law | BridgeCellReindex `laws_iff/law_family_iff` | Audit, outcomes, assigned words, initializers, weights, successor and eight-field observation |
| Complete bridge gate and semantic readout | `valid_iff/semantic_iff` | Every partial assignment; both parent frames and actual translated runs retained |
| Actual staged assignments | StagedAssignmentSpan `middle_equation/final_equation/composed_target` | Computed globals; final branch equals constructed composed package stage output |
| Raw stage program reads | `middle_expression/final_expression` | Every partial original assignment |
| Staged bridge binding | `middle_bridge_valid_iff/final_bridge_valid_iff/middle_bridge_semantic_iff/final_bridge_semantic_iff` | Complete bridge interpretations on their corresponding computed global |
| Numeric partial assignment/readout formulas | model `middle_cell/final_cell/output_equation/shortcut_equation` | Exact on every partial assignment |
| Actual context-reuse counterexample | `positive_readout/same_context_readout/same_context_not_equivalent` | Actual 4+8 = 12 versus 4+4 = 8; universal shortcut equivalence directly refuted |
| Consumed absence and partial instruction failure | `source_missing/right_cut/partial_first_rejects/rejected_source_present/partial_positive` | Actual output none; complete source does not imply success of partial stage instruction |
| Native arbitrary-partial adapter | `native_final_pullback/native_middle_pullback/native_valid_iff/native_semantic_iff` | Existing exchange involution; actual final bridge interprets original partial primitives |
| Inhabited actual native bridge | `native_positive/native_semantic_positive` | Original supported POS04 execution, all-word/readout/route gates retained |
| Direct native atomic deletion | `native_deleted_atomic_no_readout` | Actual bridge semantic readout false after deleting the original atomic table |

The reindexing constructors translate every raw instruction, not just the
positive snapshots. Evaluation equations identify selected values; proof
irrelevance only reconciles readiness proofs of identical propositions.
The interpreted future/dynamics are equal as whole functions, and the executed
root lists are equal. Thus support, full closure, actual history execution,
row laws, paths, all readout fields and future propositions transport exactly.
Bridge equations are checked against those actual frame interpretations.

The two-stage span does not replace a partial raw instruction with a total
one. Its first PackageEngine.global may return none even when its source cell
is present; that absence enters the common namespace and every consuming raw
expression rejects. The declared reject-above-limit control tests exactly this.

## Counterexample adjudication and classification

An unconditional reuse of the middle assignment as the final assignment is
false. The raw numerical stages produce middle 4 and final 8. The actual
two-context expression yields 12; redirecting its final cell to the middle
branch yields 8. `same_context_not_equivalent` directly refutes universal
equivalence of these actual readouts. The stronger repair preserves both
computed contexts in disjoint typed branches and translates the whole raw
program interface. No frozen statement is narrowed.

All **97 new theorems** (13 cell, 13 future, 11 acquisition, 24 frontier,
six bridge, 11 span and 19 fixture) and definitions are **(b)** additions.
No earlier statement, exact row text or status changes. No new axioms,
expression constructors, global toolchain changes or automatic finite lifts.

## Remaining full composition scope

The raw stage assignment binding and exact cell-namespace transport are now
proved. This does not show that the first target's physical carrier/clock,
delivered history/path and actual returned run agree with the next source
acquisition interface. The reindexed middle frames live in distinct primitive
branches; their semantic agreement is a remaining independently checked seam.
The earlier bridge composer requires an identical middle raw frame and cannot
silently equate these branches. Supported intervening acquisition, concatenated
corridor/funded route, final withdrawal/autonomy, original source-package
retention and a genuine full two-hop Temporal-FIACH positive remain.

The native specialization uses the existing package exchange twice and the
existing POS04 execution bridge. Its exact adapter verifies changed primitive
contexts and actual dynamic laws; it is not a new physical carrier hop.
Existing C4–C7 surrogate grades and all TTH-06 qualifications remain.

The raw model/control inputs were declared before evaluation in
`audit/proposed_models/TTH07-STAGED-ASSIGNMENT-SPAN.model.json`. The dedicated
checker compares raw parameters, cover, namespace dependency reads and actual
stage globals/results, compiles all-partial and native actual semantic probes,
and plants four instruction/namespace/threshold drifts. Finite probes do not
replace any unbounded kernel theorem.

Fresh read-only reviewer `/root/staged_assignment_span_review`
(`gpt-6.1-sol`, high effort) returned **ACCEPT**, with no substantive or
blocking findings and no required repairs. It independently built all seven
modules and directly elaborated each source, inspected all 97 transitive
axiom reports, checked precise 13/13/11/24/6/11/19 export coverage in inventory
and CSV, confirmed frozen statements/statuses and other rows unchanged, and
ran the dedicated checker with all four planted drifts.

It traced the typed pullback/dependencies without an injectivity assumption,
actual evaluation identification of checked runs, full acquisition/future/root/
closure/snapshot/readout-law transport, complete frame and bridge gates and
semantic readouts in both directions, the computed stage branches, direct
12-versus-8 counterexample and partial-instruction controls, and native exact
adapters/atomic-deletion semantic rejection. Only propext, Classical.choice and
Quot.sound occur. The reviewer accepted exactly the raw staged-assignment/
namespace component grade and retained all physical/full-composition gaps.
Independent logs/probe are `staged-span-independent-*` in the ignored
`lean/.validate-logs/` directory.

Manager self-review separately traced every translated raw constructor field,
the total value-operation versus partial stage-instruction distinction,
evaluated-choice equations, actual roots/closure support, complete gate and
semantic adapters and direct controls. Fresh final checks:

- `(cd lean && lake build)` passed, 555 jobs;
  `lean/.validate-logs/staged-span-final-build.log`.
- `scripts/validate_lean.sh` passed: 39 rows, 754 entries, 753 unique exports,
  745 theorems, eight statement-only declarations and one definition. Zero
  placeholders, high-confidence findings, untrusted axioms or issues; exact
  inventory match. Receipt:
  `lean/.validate-logs/run-20261009T190451-882569Z/report.json`.
- `python3 -B scripts/check_tth06_transcription.py` passed and caught all
  38 planted drifts; `lean/.validate-logs/staged-span-tth06-transcription.log`.
- Stage, global-package, receiver, register/bridge and staged-span checkers
  each passed and caught four planted drifts; logs
  `staged-span-{stage,global,receiver,register}-transcription.log` and
  `staged-span-transcription.log` in the same ignored directory.
- `git diff --check` passed. Comparison with HEAD confirmed all frozen row
  statements/statuses unchanged and only TTH-07 metadata changed, with
  precisely 97 new theorem exports.
