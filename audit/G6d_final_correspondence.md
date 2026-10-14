# G6d — final whole-gate correspondence and reversed-history certificate

This packet completes the every-partial POS04 final-gate comparison. The owning
generic certificate derives the three named readouts and the actual receiver
intervention readout from primitive instructions and checked component laws.
TTH-06 is promoted to **proved** after independent **ACCEPT / FAITHFUL** assessment.
The frozen row text and all earlier Lean statements are unchanged.

## Exact gate and adjudication

`POS04FinalCorrespondence.Common` retains the frozen source-package check,
staged preservation, target package lane, and complete actual lineage. For
**every partial original assignment**, the final F/O gates are equivalent to
`Common ∧ AF/AO`, and hence to `POS04CompleteFIACH.HandoffPassF/O`. No positive
fixture, additional readiness assumption, or externally supplied lineage
verdict enters these adapters. Missing consumed inputs reject through their
existing decoders. The source/staging fields are present explicitly: staging
is derived from the source-package and target-package premises, not deleted.

The legacy `validF/O` checks are weaker. The same raw relabeling proposal passes
their source/staging checks and whole gates, while its actual source branch
has weight 1 and the target branch weight 0. Complete actual lineage and the
final F/O gates reject it. `legacy_full_gate_not_equivalent` and
`legacy_operational_gate_not_equivalent` are kernel counterexamples to the
universal legacy gate identification. The stronger complete certificate is
used openly; there is no assertion that the old checks establish its readout.
This repairs a certificate's insufficient check without narrowing the row's
soundness conclusion or claiming a complete decision procedure.

## Argument classification

| Argument/object | Classification | Constraint |
|---|---|---|
| Original partial assignment and raw model | Raw data | Same primitive namespace and original stage/cover/withdrawal recipes |
| Source, staged and target checks | Computed checks | Frozen source/staging definitions and closed clause dispatcher |
| Complete lineage | Constructed certificate | Actual source and receiver execution, seeds, factors, records, endpoint and all retained branches |
| F/O nominal games and receiver operation | Defined objects | Shared owning primitive views; raw initializer and source-absence operation |
| `Common`, final and complete family gates | Defined predicates | Conjunctions of the above interpreted checks; no supplied Boolean verdict |
| Adapter hypotheses | Evidence | Only the defined left/right gate; no external completeness or baseline premise |
| Reversed-history proposal | Raw mutation | Exchange `repA`/`repB` past histories; preserve all other primitives |
| Relabeling control | Existing raw mutation | Same actual proposal as the earlier direct branch-weight obstruction |

## Coverage and non-vacuity

| Obligation | Receipt | Scope |
|---|---|---|
| Complete runtime check correspondence | `complete_pass_iff_valid` | Every partial original assignment; every component including shared execution |
| Frozen source and staging fields | `source_gate`, `staging_gate` | Exact source check under target-package readiness; staged check is derived |
| Complete nominal whole gate | `nominal_full_iff`, `nominal_operational_iff` | Every partial assignment, `Common ∧ AF/AO` |
| Final whole gate | `final_full_iff`, `final_operational_iff`, `final_*_iff_complete` | Every partial assignment; receiver and route/recognition scope already included |
| False legacy identification | `relabel_source_check`, `relabel_stage_check`, `relabel_legacy_F/O`, `relabel_no_final_F/O`, `legacy_*_gate_not_equivalent` | Same inhabited raw counterexample; direct complete-lineage negative |
| Reversed source and receiver frontiers | `POS04FinalReversal.Source/Target.rev_positive` | All four actual snapshots, actual support, unbounded future/readout laws and normalized rows |
| Reversed execution transport | `Bridge.bridge_laws`, `Bridge.valid` | Actual weights, updates and full observations on the entire source closure |
| Reversed seeds and corridor | `seed_equations`, `corridor_check`, `lineage_valid` | Executed endpoints, predictive coordinates, past/event residue, complete lineage |
| Reversed full certificate | `full`, `operational`, `outputs_and_certificates` | Both final gates hold with the recomputed route outputs **1/0** |
| Reversed semantic conclusions | `readouts`, `operational_readouts`, `receiver_readout` | Generic F/O and actual before/after receiver soundness |
| Existing canonical and semantic controls | `POS04FinalHandoff.positive_F/O`, `positive_receiver`, `O_control_vectors`, `F_control_vectors`, `constant_no_receiver_readout` | Previously reviewed same-family positives and direct readout negatives |

The reversed proof checks C6's finite bisimulation and invariant premises on
the exchanged histories, embeds the actual initialized roots into that
invariant, and applies the established unbounded readout laws. Source and
target execute their own decoded programs. Complete bridge laws are proved
on every register state, which includes the computed closure. The four audit
snapshots are only the declared snapshot domain, not a bound on future words.
The coordinate seed square is checked on the actual executed source endpoints.
Both route outputs are computed from the mutated histories; the proof never
substitutes canonical route labels.

## Statement classification and final faithfulness request

All **45 new theorems** are **(b)** additions. No previous theorem is edited,
no new axiom is introduced, and no frozen text is narrowed. The substantive
generic F/O and receiver soundness declarations are in `FinalHandoff`; the
new modules close their POS04 whole-gate/non-vacuity obligations. The original
schema declaration remains historical evidence.

The independent assessment must distinguish kernel correctness from target
coverage and decide whether these additions plus the reviewed owning,
nominal-protocol, receiver and complete-lineage packets are **FAITHFUL** to
TTH-06 at the declared structural grades. The accepted interpretation of
“none ... inferred” is proof-structural in F, with `AF ⇒ P` disclosed, and
logical three-lane separation in the supplementary O lane. Both soundness
proofs consume their own lane checks. The O named-readout separation has all
three same-family direct negative controls; F cannot have a package-only
logical counterexample because its same-package realization entails P.

Keep these limits visible in any promotion: C4–C7 are declared surrogates;
autonomy uses historical source support while complete lineage uses funded
actual source execution; disturbances are nominal with all positive-support
branch robustness, not resource-shock robustness; selected-response
`StrictSparse` is representation-sensitive; finite invariant certificates
are sound but potentially incomplete; receiver transport uses the declared
common coordinate interface; recognition remains `.notAddressed`.

## Review and verification

Fresh read-only reviewer `/root/final_correspondence_review` (`gpt-6.1-sol`,
high effort) returned **ACCEPT**, with a separate original-target **FAITHFUL**
verdict and no blockers or required fixes. It independently compiled both
new source files, checked all 45 standard-only axiom exports and exact
CSV/inventory coverage, compiled the full 207-line owning probe, ran the
transcription checker (all 38 planted drifts caught), and traced the actual
component derivations against the accepted G0/G6d contract. Its logs are in
`lean/.validate-logs/independent_final_correspondence_review/`.

The final review accepts the complete certificate replacement of the
insufficient legacy gates, every-partial correspondence, reversed 1/0
certificate and accepted F/O independence interpretation. It finds no
remaining TTH-06 target blocker at the disclosed grades. `status_09` is
therefore `proved` and `l3_verdict` is `FAITHFUL`; historical original registry
provenance and frozen exact text remain unchanged. The same reviewer confirmed
the final promotion metadata without corrections; the compiled owning probe
was byte-identical. Manager self-review confirmed the two-sided adapters,
direct semantic legacy obstruction and unbounded reversed execution laws.

Fresh final checks, after promotion metadata and checker wording:

- `(cd lean && lake build)` passed, 537 jobs;
  `lean/.validate-logs/final-correspondence-build.log`.
- `scripts/validate_lean.sh` passed, 39 rows, 510 declaration entries, 509
  unique declarations, 501 theorems, eight statement-only declarations and one
  definition; zero placeholders, high-confidence findings, untrusted axioms
  or issues. Receipt:
  `lean/.validate-logs/run-20261009T151157-728607Z/report.json`.
- `python3 -B scripts/check_tth06_transcription.py` passed, including the new
  complete-gate/legacy/reversal probes and all 38 planted drifts;
  `lean/.validate-logs/final-correspondence-transcription.log`.
- `git diff --check` passed. Only TTH-06's current evidence/promotion metadata
  changed; all 39 frozen exact statements remain unchanged.

The current registry has eight proved, fourteen checked finite countermodel,
nine conditional and eight open rows. The larger Lean/code campaign remains
active; this packet settles TTH-06, not the remaining backlog.
