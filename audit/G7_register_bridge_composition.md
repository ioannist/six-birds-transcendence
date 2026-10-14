# G7 — typed register substitution and actual bridge composition

TTH-07 remains **conditional**. This packet constructs composed typed register
instructions and derives an execution bridge from checked parent bridges over
one immutable assignment and an identical middle raw frame. It does not claim
the full handoff composition or a physical new hop.

## Argument table

| Argument/object | Classification | Constraint |
|---|---|---|
| Source/middle/target register families | Raw typed interfaces | Independent register sorts and dependent value families |
| First/second instruction families | Raw instructions | Existing eager Expr syntax; no supplied translated run |
| Immutable partial static assignment and environment | Raw interpreter inputs | Same input for both programs; arbitrary absence |
| Partial intermediate registers | Defined interpretation object | Actual first instruction evaluation at each register |
| Total intermediate/target registers | Defined checked object | Actual evaluation, chosen only after readiness |
| Shared middle raw frame | Raw interface equation | Entire first target equals second source; checked seam, no composite success premise |
| Parent bridge validity | Evidence | Actual source/target frame laws, raw translation equations, all-closure readout/row/updater laws |
| Domain coverage | Evidence inside parent frame gate | Every disturbance/action; closure includes zero-weight outcomes |
| Composed snapshot maps | Defined raw operations | All eight component functions compose in order |
| Composed bridge | Defined object | First source, second target, substituted instructions and composed maps |
| Numerical register fixture | Raw instructions | Bool middle register has distinct Nat/Bool value types |
| POS04 bridge fixture | Existing checked raw frames | Actual original bridge followed by identity continuation |

## Coverage table

| Obligation | Receipt | Scope |
|---|---|---|
| Every-partial substitution interpretation | `evaluation`, `program_evaluation`, bridge `partial_translation` | No readiness, supplied intermediate run or middle equality |
| Exact static dependency footprint | `dependencies`, `complete_iff`, `program_ready_iff` | Original second dependencies plus first fields actually read by second; eager branches retained |
| Actual checked translation sequence | `checked_evaluation`, `translate_compose`, bridge `translation_equation` | Independently evaluated programs; proof choices eliminated by evaluation equations |
| Consumed missing inputs | `missing_static`, `missing_consumed_register` | Actual composed evaluation is none |
| Association | `associative`, `program_associative` | Syntactic equality, hence all absence cases |
| Whole closure applicability | `closure_transport` | Actual initializer/audit/updater/outcome equations; all disturbance/action arguments and zero-weight successors |
| Composed bridge validity | `valid` | Every original bridge conjunct derives from checked parents over the actual translated closure |
| Eight-field observation maps | `maps_equation`, composed observation proof | Predictive, order, tick, progress, record, residue, maintenance and owner |
| Numerical all-partial output/readiness | model `output_equation`, `ready_iff` | Actual typed instructions on every partial assignment |
| Missing consumed/unused/eager controls | `consumed_missing`, `unused_missing`, `unused_prefix_not_ready`, `unused_composite_ready`, `eager_missing` | Direct actual outputs; unused first field can fail while composed output succeeds; eager unselected field still rejects |
| Actual numeric input effect | `positive_readout`, `changed_readout`, `instruction_effect` | Source 5, assigned input 3/4, multiplier 2 yield 16/18 |
| Inhabited executed bridge component | `bridge_positive`, `bridge_initial_translation`, `middle_closure` | Existing POS04 bridge plus identity continuation, genuine original temporal closure |

The closure theorem is the substantive applicability step. FutureClosure
includes every outcome successor, even with zero weight, and every D × A
argument. AcquisitionExecution.DomainCheck and ExecutionDomain in the existing
parent Valid gate cover all disturbances and actions. Induction transports
audit roots by the actual initializer equation and all successors by the actual
updater equation. Consequently the second parent's closure-wide laws apply to
the first translated state; no desired membership predicate is assumed.

The composite validity proof retains the first source and second target gates.
Audit, outcome and assigned-word equations compose. Initializers compose using
the evaluated register sequence. Row weights compose through the actual middle
closure, as do successor and all eight observation equations. No desired
composite bridge conclusion is supplied as raw data or check premise.

## Classification and limitations

All **33 new theorems** (14 substitution, six bridge and 13 fixture) and
definitions are **(b)** additions. No earlier statement, exact row text or
status changes. No new axioms or expression constructors.

The full package pipeline changes primitive assignments between stages;
these bridge laws use one immutable assignment. Register substitution leaves
static cell references and environment unchanged. It does not establish a
typed raw pullback of those changed cells. The identical middle-frame premise
also does not certify physical carrier/clock adjacency, delivered histories'
next supported acquisition, concatenated corridor or funded final route.
Final withdrawal/autonomy and a genuine two-hop Temporal-FIACH positive remain.

The numerical fixture tests heterogeneous register substitution and consumed
dependencies. The POS04 identity continuation is an inhabited application of
the bridge composer, with its actual closure and eight maps; it is explicitly
not a second carrier transfer.

The raw model was declared before fixture evaluation in
`audit/proposed_models/TTH07-REGISTER-BRIDGE-COMPOSITION.model.json`.
`scripts/check_register_bridge_composition_transcription.py` checks actual raw
syntax shapes, decoded assignments, dependency/read footprints and interpreted
outputs, compiles the all-partial/readiness/inhabited bridge probes, and plants
four independent drifts. Finite probes do not replace the kernel proofs.

Fresh read-only reviewer `/root/register_bridge_composition_review`
(`gpt-6.1-sol`, high effort) returned **ACCEPT**, with no blocking findings or
required repairs. It independently compiled the target and directly elaborated
each of the three modules, inspected axioms of all 33 exports, ran the dedicated
checker with four planted drifts, and checked precise inventory/CSV coverage.
It confirmed every-partial semantics, consumed dependency equivalences,
derived whole-closure applicability, all seven composed bridge laws and proof
choice elimination. Only propext, Classical.choice and Quot.sound occur.
It accepted the immutable-assignment/exact-middle-frame component grade and
explicitly retained the physical/staged-cell/full-handoff gaps. Logs:
`lean/.validate-logs/register_bridge_independent_*`.

Manager self-review independently traced the eager interpreter, actual partial
prefix, universal disturbance/action coverage, audit-root and successor
induction, all eight map compositions and the direct semantic controls.
Fresh final checks on the reviewed sources:

- `(cd lean && lake build)` passed, 548 jobs;
  `lean/.validate-logs/register-bridge-final-build.log`.
- `scripts/validate_lean.sh` passed: 39 rows, 657 entries, 656 unique exports,
  648 theorems, eight statement-only declarations and one definition. Zero
  placeholders, high-confidence findings, untrusted axioms or issues; exact
  inventory match. Receipt:
  `lean/.validate-logs/run-20261009T183253-247073Z/report.json`.
- `python3 -B scripts/check_tth06_transcription.py` passed all 38 planted
  drifts; `lean/.validate-logs/register-bridge-tth06-transcription.log`.
- Stage, global-package, receiver and register/bridge transcription checkers
  each passed and caught all four planted drifts; logs
  `register-bridge-{stage,global,receiver}-transcription.log` and
  `register-bridge-transcription.log` in the same ignored directory.
- `git diff --check` passed. Comparison with HEAD confirmed unchanged frozen
  statements/statuses for all rows; only TTH-07 evidence/ceiling/rationale
  changed, with precisely 33 new exports.
