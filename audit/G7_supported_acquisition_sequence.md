# G7 — actual supported acquisition continuation

TTH-07 remains **conditional**. This packet constructs the next acquisition
from the actual computed first post-exit entry. Raw instruction translation,
actual selected histories and positive row support determine each run. An
independent middle-initializer equation binds the next start to its acquisition
interface. The constructor derives both existing Entry predicates and a
separately defined complete sequential readout; it does not accept a desired
next-entry membership or composite success as a premise.

## Argument table

| Argument/object | Classification | Constraint |
|---|---|---|
| Raw acquisitions | Raw syntax | Own dependent registers, initializer, assigned histories/routes/events/activation, row/updater/receive/response |
| Boundary | Raw typed instructions | First register family to second register family; every consumed primitive is required |
| Primitive assignment | Raw interpreter input | Arbitrary partial assignment |
| Chosen routes/outcomes | Raw selectors | Explicit theorem arguments, not chosen after testing the final readout |
| Supported fold | Defined interpreter output | Actual legality and positive-weight outcome checks at every computed state; unsupported steps return none |
| Initial acquisition | Defined interpreter output | Actual assigned route/history, raw initialized run, supported word and receive instruction |
| Post-exit branch | Defined interpreter output | Actual response expression, positive chosen outcome and updater |
| Next start | Defined interpreter output | Raw boundary translation of the actual first computed post-exit entry |
| Middle initializer equation | Evidence on raw instructions | Translated actual first entry equals actual next initializer on its decoded route/history |
| History checks | Evidence on actual dynamics | First from actual initializer; next from actual translated first entry; no terminal supplied |
| Response checks | Evidence on actual dynamics | Every raw run and decoded route has actual legal normalized response and positive chosen outcome |
| Domain/path/activation | Evidence | Existing raw acquisition predicates and decoded instructions |
| Entries/readout | Derived semantics | Existing Arrival/Entry plus actual computed results and middle initialization interface |
| Stage assignments | Defined stage outputs | Actual existing identity then prior-path-appending globals, in distinct namespace branches |
| Models | Predeclared raw data | Unit→Nat, initializer0/2, one-step word, updater+1, identity receive/boundary |
| Negative controls | Raw mutations | Wrong next initializer, zero weight, consumed absence, normalized assigned unsupported branch |

`ResponseCheck` is intentionally universal over raw runs, a stronger sufficient
condition than checking only reachable contexts. It is not silently inferred
from a parent handoff's closure-relative row gate. The constructor is sound,
not complete for all possible sequential readouts. It quantifies explicitly
over chosen outcomes; a theorem for one choice is not an all-branch autonomy
proof. The support interpreter itself is exact for every word and outcome,
including duplicates and zero-weight row entries. Full handoff assembly must
instantiate continuity for every admitted branch without selecting by success.

## Coverage table

| Obligation | Kernel receipt | Scope |
|---|---|---|
| Actual finite support test | `supports_iff/step_check_iff` | Exact list membership and positive weight; legal disturbance/action lists |
| Supported history execution | `fold_some_iff/fold_none_iff/fold_terminal_defined` | Exact existing HistoryExecution for every partial assignment with readiness |
| Word construction | `checked_fold/fold_append` | Actual support checks and Option sequencing, arbitrary words |
| Unsupported branch | `unsupported_no_execution` | Computed fold returns none before the unsupported update |
| Existing arrival | `from_start_sound/first_arrival_sound/first_arrival_complete/first_arrival_iff` | Actual initialization/support/receive; exact correspondence under independently decoded route checks |
| Existing first entry | `post_exit_sound/first_entry_sound` | Actual selected positive post-exit branch and normalized row |
| Actual next acquisition | `next_arrival_sound/next_entry_sound` | Typed actual first-entry translation, checked initializer interface, actual next supported word/receive/response/update |
| Full sequence construction | `post_exit_exists/response_normalized/constructs` | Raw check family derives availability, both existing entries and actual semantic Readout |
| Semantic absence | `first_none_no_readout/next_none_no_readout/missing_first_no_readout/missing_second_no_readout/missing_boundary_no_readout` | Direct Readout refutation, with no contradictory supplied readiness hypothesis |
| Namespace instruction translation | reindex `boundary_ready_iff/boundary_equation/step_equation/fold_equation` | Every partial assignment, all raw registers and words |
| Actual namespace runs | `from_start_equation/first_arrival_equation/post_exit_equation/first_entry_equation/next_arrival_equation/next_entry_equation` | Exact complete computed functions and absence cases |
| Complete semantic adapters | `route_check_iff/entry_iff/readout_iff` | Existing Entry and complete sequential Readout in both directions, every partial assignment |
| Nat raw positive | model initialization/update/receive/fold/first/next equations and `positive_checked/positive` | Actual initializer0→arrival1→entry2→next arrival3→entry4 |
| Essential middle anchor | `wrong_initial_no_readout/wrong_initial_not_arrival/initializer_anchor_essential` | Actual next arrival3, independently initialized next arrival1; actual Arrival and Readout directly refuted |
| Actual zero weights | `zero_fold/zero_next_arrival/zero_next_no_readout/zero_first_entry/zero_first_no_readout` | Actual supported output none, not just normalized-gate failure |
| Consumed absence | `missing_right_no_readout/staged_missing_final` | Arbitrary assignment, actual consumed raw view unavailable |
| Computed staged contexts | `staged_pullback/staged_actual_pullback/staged_readout_iff/staged_positive/staged_next_entry` | Complete every-partial raw adapter, actual selected middle/final globals and computed final entry4 |
| Normalized branch control | `normalized_branch_row/rejects/has_alternative/first_none/no_readout` | Row [(false,1),(true,0)] normalized; actual assigned true word rejects although false word succeeds; every chosen post-exit outcome |

## Counterexample adjudication and classification

A supported continuation from an arbitrary starting register need not be an
arrival of the next acquisition. The raw first hop computes entry2. With the
wrong next initializer0, continuation executes the assigned word from2 and
returns3, while the independent next acquisition initializes0 and returns1.
`wrong_initial_not_arrival` directly proves the actual supported continuation
result is not Arrival, and `initializer_anchor_essential` refutes the proposed
universal shortcut. `wrong_initial_no_readout` also directly refutes the
complete sequential semantics. The stronger repair explicitly binds the
translated computed first entry to the next raw initializer; it never assumes
next membership or substitutes a candidate terminal.

The normalized two-outcome control has a productive false word, but the raw
assigned history requests the zero-weight true word. The interpreter rejects
that exact word and directly refutes the readout for every post-exit outcome;
it does not substitute another supported history. This isolates actual branch
selection rather than relying only on a failed normalization premise.

All **81 new theorems** (26 sequence, 13 namespace, 42 fixture) and their
definitions are **(b)** additions. No earlier statement, frozen exact row text
or status changes. Only TTH-07 metadata/imports/export coverage change. No new
axioms, holes, native_decide or global toolchain changes.

## Remaining full composition scope

The actual supported selected-history/entry seam is now constructed. This is
not a full Temporal-FIACH witness. The existing raw corridor fixture's seed0
is still independent of its Nat executed register; this packet does not
promote that geometry fixture to runtime lineage. Physical seed/clock/owner
coherence, funded runtime-route continuity, complete cross-stage executed
bridge applicability, original source-package retention and final withdrawal/
autonomy still require assembly. All existing TTH-06 interpretations and
C4–C7 grades remain. A genuine full two-hop Temporal-FIACH positive is required
before promotion.

The raw model/control instructions were declared before evaluation in
`audit/proposed_models/TTH07-SUPPORTED-ACQUISITION-SEQUENCE.model.json`. The
checker observes actual initialization/history/row/updater/receive/response/
domain/selector and boundary instructions, executes their finite observation
interpreter, compiles actual semantic equations/controls and exact all-partial
staged adapters, and plants five initializer/boundary/history/weight/namespace
drifts. The observation interpreter does not replace the unbounded kernel
supported-execution or Entry proofs.

## Independent review and verification

Fresh mandatory reviewer `supported_acquisition_sequence_review`
(gpt-6.1-sol, high, read-only) returned **ACCEPT at the disclosed
supported-entry component grade**, with no blocking findings. The report is
`lean/.validate-logs/supported-sequence-independent-review.md`. Independent
fresh source elaboration, exact 26/13/42 export coverage, all 81 axiom checks,
and the dedicated five-drift checker passed. Only propext, Classical.choice
and Quot.sound occur. An extra independent semantic probe directly refutes
existing Entry for the wrong-initializer computed final run4. The reviewer
confirmed that full TTH-07 remains conditional and all frozen statements and
statuses are unchanged.

Fresh manager full `lake build` passes (564 jobs). The dedicated supported
sequence checker passes with five caught drifts. TTH-06 and the stage, global
package, receiver, register, span and corridor regression checkers pass; their
receipts are `lean/.validate-logs/supported-sequence-*-transcription.log`.
Fresh full `scripts/validate_lean.sh` passes in
`lean/.validate-logs/run-20261009T203931-199745Z`: 39 rows,
915 inventory entries, 914 unique declarations, 906 theorem-kind declarations,
8 statement-only declarations and 1 definition. Inventory matches, build and
probe exit0, zero placeholders/high-confidence findings, no untrusted axioms
or issues. TTH-07 has 408 theorem exports and remains conditional. The
TTH-06 checker catches all 38 planted drifts; stage/global/receiver/register/
span catch four each and corridor catches five. Every frozen statement/status
and every non-TTH-07 registry/inventory row is unchanged. Only the standard
three axioms are used; all 81 additions are covered by independent review.
