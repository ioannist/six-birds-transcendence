# G6d — raw source-absence rerun

TTH-06 remains conditional, with the frozen statement unchanged. This packet
completes a receiver counterfactual component: remove source presence in the raw
primitive and rerun the **same** receiver, while preserving its latent factor
data and prepared actual run. Final owning-gate integration and the generic
nominal-protocol/whole-gate adapters remain open.

## Exact semantics and argument table

`ReceiverIntervention.withoutSource` transforms the value at the existing raw
receiver cell with `Option.map` and leaves every other cell unchanged. The
value operation is raw syntax-level data, with `ErasureLaw` separately checking
that its projected receiver equals the original receiver with only
`sourcePresent` set to false. Missing values stay missing. All scope completeness,
register initialization, program and runtime readout readiness are preserved in
both directions on every partial assignment.

`decoded_receiver` extracts the receiver from the **actual** owning endpoint
decode. The generic `no_reception` and `not_faithful` theorems rerun
`ReceiverContent.receive/receivedClass` with the same model, recipe and input at
the transformed assignment. Successful decoding has source presence false;
failed decoding stays `none`. These proofs directly reject the semantic
readouts. No failed sufficient certificate is used as a semantic negative.

| Argument/object | Classification | Binding |
|---|---|---|
| Existing owning model and receiver recipe | Raw data | Identical before/after intervention |
| `erase : Value receiver.cell → Value receiver.cell` | Raw value instruction | No verdict, candidate run or derived receiver class |
| `ErasureLaw` | Evidence about raw projection | Sets source presence false; preserves the other projected receiver fields |
| Original and intervened assignments | Defined raw inputs | `put` at the same primitive cell, `Option.map` preserves absence |
| Initialization/runtime readiness | Evidence | Scope completeness transported exactly; target-factor decoding additionally checked in POS04 |
| Counterfactual reception/class/faithfulness | Defined semantic readouts | Actual rerun using the original model, recipe, terminal, history and path |

The generic erasure law preserves the projected receiver and all other cells.
It does not assert that every hidden field of an arbitrary receiver-cell value
is preserved, or that a generic target factor using that cell is unchanged.
POS04's raw record update preserves every field except source presence, and
its additional exact latent and prepared-run theorems establish those stronger
properties for that instance.

## Coverage table

| Obligation | Receipt | Scope/control |
|---|---|---|
| Every missing input remains missing | `missing_unchanged` | Every cell of every partial assignment, both directions |
| Every other raw cell stays fixed | `other_unchanged` | Entire dependent primitive value, not just a projected label |
| Initializer/program/future readiness | `complete_iff`, `initial_ready_iff`, `program_ready_iff`, `future_ready_iff` | Exact biconditionals for all scopes/programs/assignments |
| Projected receiver counterfactual | `receiver_read`, `receiver_absent` | Every partial assignment, including absent receiver primitive |
| Actual absence readouts | Generic `no_reception`, `not_faithful` | Actual readout definitions after intervention; explicit interpreter readiness |
| POS04 latent target/source data | `latent_factor` | Both entire factor decoders equal before/after on every partial assignment; shared funding primitive handled explicitly |
| POS04 target interpreter readiness | `target_ready_iff` | Exact before/after equivalence, not a contradictory missing-input/readiness premise |
| Every actual register initialization | `evaluation_unchanged`, `initial_unchanged` | All inputs and registers; evaluation equality even on incomplete assignments |
| Prepared actual target run | `prepared_run_unchanged` | Same projected factor/counters/ticks/full past/path/funding |
| Transported readies and rejected rerun together | `rerun_rejected` | For any originally ready assignment, actual run unchanged, returned run/class `none`, faithfulness false |
| Inhabited control | `baseline_rerun_rejected` | Canonical receiver has transported readies; earlier positive faithfulness remains proved |

Preparation is distinct from activation. The prepared run survives the
intervention; actual reception does not. The negative does not erase funding,
change the protocol, replace a realized source route, or relabel a lane result.
This is an in-memory counterfactual, not a new frozen fixture or modification
of historical-support versus funded-lineage semantics.

## Statement classification and integration

All 23 new theorem declarations and definitions are **(b)** mathematical
additions. There are no **(a)** edits or changes to earlier Lean statements,
frozen theorem text/status, models or family declarations. No narrowing or new
axiom is introduced. The receiver interventions are component evidence; an
enclosing final gate must still own the raw recipe and incorporate its laws.
Common-coordinate scope and the earlier historical-support, StrictSparse,
positive-support and finite-constructor limits remain disclosed unchanged.

The registry appends the exact new theorem evidence. The checker retains frozen
factor/record comparisons and adds typed kernel examples for all-partial latent
decoding, target readiness equivalence, actual rejected reception, and inhabited
baseline rejection. It supplies no Boolean autonomy or receiver result.

## Review and verification

A fresh read-only Codex reviewer (`/root/receiver_intervention_review`,
`gpt-6.1-sol`, high reasoning effort) returned **ACCEPT**, with no mathematical
blockers. It independently compiled both final source files, audited all 23
exports, checked actual rerun semantics and latent/reset/run preservation,
verified exact inventory coverage without duplicates, and confirmed unchanged
TTH-06 text/status. It accepted the distinction between generic projected-field
preservation and stronger POS04 preservation. All completion limits above stay
in force.

Fresh `lake build` passed, 527 jobs:
`lean/.validate-logs/intervention-build.log`. All 23 individual axiom probes
passed; `erasure_law` is axiom-free and the other exports use only the standard
axioms: `lean/.validate-logs/intervention-axioms.log`.
`python3 -B scripts/check_tth06_transcription.py` passed, including the new
typed intervention examples and all 38 planted drift checks:
`lean/.validate-logs/intervention-transcription.log`.
`git diff --check` passed. Registry comparison confirms only TTH-06's kernel
evidence, ceiling and rationale change; all other rows and frozen text/status
are unchanged. No paper files were read or changed.

Fresh `scripts/validate_lean.sh` passed: 39 rows, 387 evidence entries / 386
unique names, 378 theorem-kind, 8 statement-only and 1 other definition; no
placeholders, high-confidence vacuity findings or untrusted axioms. Receipt:
`lean/.validate-logs/run-20261009T133742-263368Z/report.json` and
`lean/.validate-logs/intervention-validator.log`.
