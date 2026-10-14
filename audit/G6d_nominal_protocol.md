# G6d — owning nominal protocol

TTH-06 remains conditional. This packet completes the generic raw nominal
protocol and its owning POS04 binding. Receiver-law integration and exact
correspondence of the final gate with the frozen row remain open. The exact
frozen statement, statuses and existing bare-game definitions are unchanged.

## Construction and argument table

`NominalProtocol` defines the nominal protocol on arbitrary typed finite
alphabets and numerical parameters. Its raw reader consumes source/target
rows and policies, target ticks/resources/ledger, histories, supported events,
realized stages, receiver, route table and writers. It performs a closed eager
instruction evaluation, without accepting a supplied protocol verdict. Every
missing consumed primitive rejects. The specification supplies raw reference
ledger/operator and domain declarations, not a derived future or safe set.

Route checks use priority lookup, actual nonempty history/path endpoints,
activation, strict consecutive realized stages, raw source and target support,
target-only final event, pre-withdrawal target funding, writer, terminal row
normalization and positive declared outcomes. All raw supported branches
remain visible. Withdrawal requires exactly the six role kinds (duplicates
allowed), source absence and required retained support. Advancement and the
reference ledger and P checks use the same raw target data after withdrawal.

`NominalHandoff` constructs this specification and its primitive views from
`OwningHandoff.RawHandoff.frames`. Only reference ledger/operator, required
resource names and a static source-presence instruction are additional raw
recipe data. Withdrawal metadata is obtained from the SAME owning runtime's
withdrawal instruction, paired with that static instruction. `Laws` checks
all-run equality of source presence and required-support recipes and literal
closed C8 dispatcher equality using the constructed specification/views.
The POS04 laws hold for every protocol and partial target assignment.

| Argument/object | Classification | Binding |
|---|---|---|
| Domain, route/stage/event and ownership declarations | Raw schema | Constructed from owning source/target frames |
| Reference ledger/P and required support | Raw recognition/reference data | Closed C8 schema and all-run resource recipe equations checked by `Laws` |
| Primitive probability rows, pasts, events, ticks and resources | Raw cells | Reader views are projections of owning frame primitive bindings |
| Withdrawal roles/retained list/source presence | Raw physical metadata | Decoded from owning withdrawal and static presence recipes; all-run presence law |
| Protocol result | Defined proposition | No supplied Boolean verdict; all checks operate on decoded raw data |
| Nominal full/operational autonomy | Defined semantic readouts | Protocol conjoined explicitly with existing independent bare games |
| Subchecks/certificates and laws | Evidence | Exact invariant/subcheck equivalence; positive certificates imply respective readouts |

Standalone `NominalProtocol.Pass` is a parameterized raw audit. It does not
assert schema validity or positive domain/scale declarations; the enclosing
package and frame coherence gates provide those obligations. Likewise, the
nominal-qualified semantic readouts are defined independently of `Laws`; the
enclosing handoff certificate separately checks those binding equations.

The explicit protocol qualification is necessary: the frozen nominal unit
ledger is stronger than resource solvency of an arbitrary bare game. Earlier
kernel counterexamples and bare-game semantics are retained. A failed protocol
check does not imply failure of the bare game. Negatives below refute the actual
defined protocol or nominal-qualified semantic readout only.

## Coverage table

| Obligation | Receipt | Coverage |
|---|---|---|
| Raw protocol dependency scope | `POS04NominalProtocol.dependency_iff` | Exactly the frozen twelve cells; shared policy projects twice |
| Missing input rejection | Generic `missing_no_pass`; owning `missing_primitive_no_pass`, `missing_metadata_no_pass` | Every partial assignment; no decoder default acceptance |
| Exact raw protocol specialization | `reader_computed`, `withdrawal_iff`, `withdrawn_eq`, `advancement_iff`, `unchanged_iff`, `phase2_eq`, `check_iff`, `pass_iff` | Empty/malformed histories/paths, missing cells, arbitrary raw tables/metadata |
| Same owning primitive views/specification | `shared_primitives`, POS04 `specification_eq`, `views_eq` | Literal constructed equality; no additional raw probability table |
| Actual resource recipe coherence | POS04 `laws`, `metadata_computed`, `protocol_iff` | Every protocol and partial assignment; no game/positive fixture premise |
| Exact AF/AO adapters | POS04 `full_iff_af`, `operational_iff_ao` | All partial assignments for newly defined nominal-qualified readouts |
| Generic assembly | `full_subcheck_iff`, `operational_subcheck_iff`, `soundness_F`, `soundness_O` | Polymorphic nominal-qualified games; package/lineage use their own subchecks |
| Nonvacuous positive | POS04 `baseline_pass`, `baseline_readouts` | Both nominal autonomy lanes inhabited |
| Historical-support diagnostics | `duplicate_event_pass`, `missing_past_ticks_pass`, `source_recharge_pass` | Preserve existing nominal outcomes; no added source-funded execution requirement |
| Unconsumed raw cells | `unused_primitive_locality` | Any unconsumed target-image cell replacement/deletion, all partial assignments |
| Direct controls | `source_present_no_pass`, `source_present_no_readouts`, `zero_ledger_rejected` | Actual defined protocol/qualified readouts, never inferred bare-game failure |

The source-absent nominal flag is post-withdrawal metadata, distinct from the
receiver's pre-withdrawal activation field. The raw metadata reader requires
its actual primitive withdrawal input; it does not default when absent.
`legacyData` appears only as a comparison witness under explicit completeness
in the POS04 equivalence proof. Public readers have no fallback data.

## Statement classification and remaining obligations

All 49 new theorems and the additional definitions are **(b)** additions. There are no **(a)**
statement edits, new axioms, silent narrowing or status promotion. The old
POS04 computed protocol and bare-game names remain as comparison evidence.
The exact new owning protocol adapter removes the dependency on a supplied
POS04 protocol verdict in the new generic readout definitions.

The remaining final gate must own the receiver recipe/laws, counterfactual
coherence, source/staged/route/recognition fields and compare its full gate
against the frozen contract on every partial assignment. This packet does not
claim those obligations. Common-coordinate scope, historical-support
acquisition versus funded lineage, representation-sensitive selected-response
StrictSparse, complete positive-support coverage and sound-but-incomplete
finite invariant certification remain unchanged and disclosed.

Registry evidence lists every new theorem exactly once; the checker adds typed
kernel probes of the arbitrary-partial protocol/AF/AO adapters, all-run laws,
missing-input rejection and diagnostic controls while retaining frozen raw
factor/record comparisons and planted drift checks.

## Review and verification

Fresh read-only reviewer `/root/nominal_protocol_review` (`gpt-6.1-sol`, high
reasoning effort) returned **ACCEPT**, with no blockers or remaining required
fixes. It independently compiled all four modules, checked all 49 theorem
exports and axioms, verified exact inventory coverage and unchanged frozen
statements/statuses, and confirmed the component/final-target boundaries.
The standalone schema-validity limit and independent `Laws` gate are explicit.

Fresh `lake build` passed, 531 jobs: `lean/.validate-logs/nominal-build.log`.
All 49 individual axiom probes passed, with only standard axioms;
`shared_primitives` is axiom-free: `lean/.validate-logs/nominal-axioms.log`.
Fresh `python3 -B scripts/check_tth06_transcription.py` passed, including the
new typed probes and all 38 planted drift checks:
`lean/.validate-logs/nominal-transcription.log`. `git diff --check` passed.
CSV comparison confirms only TTH-06 evidence, ceiling and rationale changed.
No paper files were read or changed.

Fresh `scripts/validate_lean.sh` passed: 39 rows, 436 evidence entries / 435
unique names, 427 theorem-kind, 8 statement-only and 1 other definition;
no placeholders, high-confidence vacuity findings or untrusted axioms.
Receipt: `lean/.validate-logs/run-20261009T142659-511247Z/report.json` and
`lean/.validate-logs/nominal-validator.log`.
