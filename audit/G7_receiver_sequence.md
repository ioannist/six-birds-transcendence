# G7 — actual receiver operation sequence

TTH-07 remains **conditional**. This packet composes two actual receiver
operations and their content/counterfactual readouts. It does not establish a
physical three-carrier middle interface or a supported next acquisition.

The sequence executes the first receiver, decodes its actual returned factor,
maps its actual full past and path, and passes the constructed input to the
second receiver. Raw history/route namespace maps preserve input identity.
Absent maps or factor decoding remain absent; no cached terminal/class or
fallback can substitute for the first return.

Public left/right assignments are computed by the original stage and cover
operations. The right assignment equals the closed composed package target for
every partial original assignment. Internal `receiveAt/classAt` interpretation
lemmas allow arbitrary primitive assignments, while the public operation and
`ContentReadout` use those constructed globals.

## Argument table

| Argument/object | Classification | Constraint |
|---|---|---|
| Two raw models and receiver initialization programs | Raw data | Same common typed coordinate interface; no stored received state/class |
| Boundary map view, event/history/route maps | Raw data | Decoded on the left primitives; applied to actual returned factor/past/path |
| Original assignment | Raw data | Public pipeline constructs both intermediate/final globals |
| Internal primitive assignments | Interpretation data | Public stage equations bind them; no independently supplied derived target |
| Endpoint data and parent factor maps inside `Checked` | Decoder witnesses | Actual decoder/reset laws and factor equations bind every witness to primitives |
| Boundary factor/profile/action/tick/owner equations | Evidence | Independently interpreted tables; no composite content conclusion |
| Both activations and a genuine source-class pair | Computed evidence | Actual endpoint checks and actual source profiles; nonempty/distinct classes |
| Delivered input and final run/class | Defined objects | Actual first return and actual second operation |
| Source erasure | Raw intervention | Same first receiver rerun; second assignment retained |
| POS04 witness and constant-state mutation | Raw instruction data | Existing ports/canonical cells; only middle state instruction changes |

## Coverage table

| Obligation | Receipt | Scope |
|---|---|---|
| Actual delivery equation | `deliver_equation` | Decoded raw map and actual returned factor/past/path; no supplied class |
| Sequential class interpretation | `class_sequence` | Every partial assignment with explicit actual interpreter readiness |
| Public stage binding | `shared_final_target`, POS04 `left_cells/right_cells` | Every partial original assignment |
| Direct missing-input/factor/endpoint negatives | `missing_maps`, `undecodable_first_factor`, `first_none`, `missing_maps_receive`, `receive_none_class_none`, `missing_right_endpoint` | Actual delivery/receive/class `none` |
| Full returned run | `first_run`, `actual_receive` | Actual reset squares; counter/ticks zero, funding and mapped full past/path |
| Actual final class | `actual_class` | Both actual receiver operations and activations |
| Content soundness | `content_soundness` | Three checked factor class maps reflect genuine source distinctions |
| Direct source cut | `source_absent`, `source_erasure`, `source_erasure_not_faithful` | Same first operation rerun; no receive/class and directly false total content |
| Decoder-witness-free public conclusion | `ContentReadout`, POS04 `public_content` | Readiness on the two constructed globals, not preloaded targets |
| Inhabited common-coordinate ports | POS04 `bridge_equations`, `checked`, `content_faithful`, `operation_class/actual_class` | Existing actual programs; raw tag-owner reindex, genuine p0w0/p1w0 source classes |
| Constant middle-state control | `constant_other_fields`, `constant_class`, `constant_not_faithful` | All final received classes equal; actual readout refuted, other instructions/primitives retained |
| Source-cut port witness | `source_cut`, `source_cut_not_faithful`, `cut_latent_factors` | Right cells fixed, actual latent factor decoders equal, same sequence returns none |

Content soundness first derives the actual final class from the two raw reset
squares. If two final classes agree, the right factor equation reflects their
source classes; the boundary equation reflects the first received classes;
the left equation reflects the original source classes. This contradicts
actual source distinction. Neither content faithfulness nor a desired
composite class-preservation predicate is a check premise.

The constant control uses the same two receiver programs, activations and
primitive assignments. Only the boundary state map becomes constant p0w0.
The actual operation class equation directly yields the same received class
for every input, so the semantic content readout is false.

## Scope and pending full composition

The POS04 witness reuses the two original canonical receiver ports and the
existing all-input reset tests `inputA/inputB`. It is not a new realized-route
fixture. Its raw owner tag map is checked between factor tables, but it does
not prove equality of physical middle carrier IDs, clock/frontier adjacency,
or delivered histories' membership in the next actual acquisition domain.

The operation currently invokes the second receiver immediately after delivery.
A full composed handoff must separately establish the supported intervening
acquisition/execution span, endpoint applicability and physical interface
equations. The class theorem does not imply those properties. Actual corridor
concatenation, all-run bridge transport, funded resulting-route readouts,
final withdrawal/autonomy transport and a genuine full two-hop positive remain.

Generic source-erasure statements quantify over the actual before/after
ready interpreters. POS04 retains its previously proved initialization and
latent-factor preservation laws, and holds the second assignment fixed.
General latent-map/reset preservation for arbitrary boundary recipes is not
inferred merely from the no-reception theorem.

## Classification, model and verification

All **32 new theorems** (17 generic and 15 POS04) and definitions are **(b)**
additions. No earlier statement, frozen POS04 table, row text or status changes.
No new axioms. The register/source interfaces are common-coordinate at this
component grade; broader typed namespace and physical interface transport
remain the full construction's obligations.

The raw model/control instructions in
`audit/proposed_models/TTH07-RECEIVER-SEQUENCE.model.json` were declared before
evaluation. The checker compares raw map/namespace/erasure instructions and the
genuine source pair, compiles all-partial stage and actual positive/negative
receiver probes, and catches four planted state/owner/route/control drifts.
Finite instruction probes are not substitutes for the all-input kernel proofs.

Fresh read-only reviewer `/root/receiver_sequence_review` (`gpt-6.1-sol`, high
effort) returned **ACCEPT**, with no blocking findings or required repairs. It
independently compiled both sources, checked all 32 standard-only axiom
exports and exact unique registry/inventory coverage, and ran the checker with
all four planted drifts. It traced the actual input/run/class sequence and
three-map reflection argument, the public stage binding, direct constant
collision and source cut. It accepted the immediate common-coordinate grade
while explicitly retaining the full temporal/physical/applicability gaps.
Logs: `lean/.validate-logs/receiver-sequence-independent-*`.

Manager self-review confirmed the actual returned tapes, raw decoder binding,
genuine class-pair non-vacuity, direct semantic negatives and stated interface
limits. Fresh final checks on the current sources:

- `(cd lean && lake build)` passed, 545 jobs;
  `lean/.validate-logs/receiver-sequence-build.log`.
- `scripts/validate_lean.sh` passed, 39 rows, 624 entries, 623 unique exports,
  615 theorems, eight statement-only declarations and one definition; zero
  placeholders, high-confidence findings, untrusted axioms or issues. Receipt:
  `lean/.validate-logs/run-20261009T175258-859573Z/report.json`.
- `python3 -B scripts/check_tth06_transcription.py` passed, all 38 planted
  drifts; `lean/.validate-logs/receiver-sequence-tth06-transcription.log`.
- Stage, global-package and receiver checkers passed, each catching its four
  planted drifts; `receiver-sequence-{stage,global,transcription}.log` in the
  same ignored log directory.
- `git diff --check` passed. Only TTH-07's evidence/ceiling/rationale changed
  in the registry; frozen statements and statuses remain unchanged.
