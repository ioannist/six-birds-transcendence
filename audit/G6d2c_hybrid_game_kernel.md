# G6d-2c hybrid: strategy/play kernel seam

## Proved

`StrategyGame` is an interpretation-parametric semantic engine. Runs, actions,
disturbances and outcomes are arbitrary types; runs need not be finite.
A strategy reads the past run history and current disturbance, not future input.
`Play` executes its chosen action through the actual updater for each positive
row-support outcome. `GameReadout` requires withdrawal, nonempty entries,
package/resource safety and legal normalized responses with step laws on those
plays. It does **not** require safety of unselected actions.

`InvariantCertificate` contains an auxiliary invariant and proofs of entry
coverage, package/resource closure, and total legal responses with full-support
invariant preservation and transition laws. There is no autonomy-readout field.
`invariant_game_soundness` chooses responses and inducts on `Play`.
`game_answers_every_word` proves total response execution for every finite
word by induction, not bounded enumeration. `play_selected_congruence` proves
that changing only unselected action interpretations cannot change plays.

`game_same_package_implies_arrival` derives the same-package consequence at a
genuine entry: with the F interpretation `arrival ∧ packageContext r`, game
autonomy implies arrival. This is an engine lemma, **not yet the RawHandoff AF→P
adapter**. It uses the nonempty entry and initial play, not an implication field.

`GameFiniteConstructor.certificate` constructs the run invariant as the pullback
of `ViableSet.greatest` intersected with a run-context invariant. The proof uses
`ViableSet.greatest_viable`. `finite_lift_game_soundness` applies game induction;
`finite_lift_play_context` proves context/projection coverage throughout the
strategy's generated plays. Its `LiftWitness` obligations quantify over every
relevant context and every positive-support successor of the selected response.
This is sound **given proved lift obligations**. It neither proves that every
raw recipe has a finite lift nor asserts decision completeness.

## Argument classification / boundary

| Argument | Classification and eventual binding |
|---|---|
| Run/disturbance/action/outcome types | Semantic domains; no finite-run assumption |
| Rows and updater | Interpreted component interfaces in this engine; must be defined from shared raw cells at the RawHandoff boundary |
| Entries and withdrawal | Interpreted acquisition/withdrawal interfaces; activation, realization and completeness still need the raw adapter |
| Package/resource predicates | Interpreted component interfaces; must be computed by assigned clauses/resources, never free verdicts at the raw boundary |
| Legal-response / transition-law predicates | Interpreted ownership/resource/solvency/advancement interfaces; must refer to the defined actual updater |
| Invariant and response evidence | Approved auxiliary witnesses; each obligation proved against those interpretations |
| Finite carrier / retention / monotonicity | Existing ViableSet interface; specialized retention must be computed from raw rules |
| Projection, context and lift proofs | Auxiliary finite-lift engine witness; actual specialization must construct the projection and prove its context laws, not assume omission harmless |
| Causal strategy, plays, pulled-back greatest invariant | Defined objects, not certificate inputs |

These semantic interfaces are mathematical parameters of reusable induction
lemmas, **not a new generic RawHandoff structure accepting independent candidate
functions**. This seam alone does not discharge that structure's contract.

## Guards / coverage

| Obligation | Proved semantic guard |
|---|---|
| Activated/realized nonempty entries | `no_entries_no_game`; activation/realization raw guards remain in adapter |
| Withdrawal | `invalid_withdrawal_no_game` |
| Same-package preservation | `entry_package_failure_no_game`; positive entry consequence `game_entry_package` |
| Resource closure | `entry_resource_failure_no_game` |
| Target-owned available legal response | `missing_response_no_game` |
| Every positive support branch, including solvency and advancement | `unavoidable_bad_branch_no_game` |
| Selected actions only | `play_selected_congruence` |
| Finite projection/context maintained along plays | `finite_lift_play_context`; no claim that arbitrary recipes meet its lift obligations |

These are semantic guards, not yet per-cell POS-04 sensitivity controls.

## Outstanding

- Bind raw shared assignment, all graded package rules, acquisition/withdrawal,
  updater and resource/ownership/ledger laws to this semantic engine.
- Prove actual POS-04 finite lifting laws and exact partial-assignment/control
  equivalences. The lift witness type above is an obligation, not their proof.
- Extract generic C6 dynamics/observer/code with its independent full-future
  bisimulation and closure-law guards; prove C6/C8 family equivalences.
- Export actual raw F/O certificates and AF→P after the component binding.

No status or ceiling change. All additions are (b) for TTH-06: the approved
hybrid architecture and its semantic/finite-constructor helper theorems.
Existing Lean statements are unchanged; no (a) renames.

## Verification

- `cd lean && lake build`: exit 0, 375 jobs. New modules compile in about
  two seconds each; no new-module warnings. Existing warnings remain.
- `scripts/validate_lean.sh`: exit 0; inventory matches, no placeholders,
  no high-confidence vacuity findings, no untrusted axioms. Existing 29
  non-gating heuristic leads remain.
- `/tmp` axiom probes for all 16 new theorem declarations: standard three or
  fewer. Forbidden-construct scan of both new modules and `git diff --check`
  are clean. No registry, inventory, frozen science or vendor changes.
- Self-review checked the causal quantifier order, every positive branch of
  the selected response, nonempty entry use, and the distinction between a
  proved lift theorem and an actual raw-model lift instantiation.
