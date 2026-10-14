# G6d — receiver content and activation component

TTH-06 remains conditional. The frozen exact statement and earlier declarations
are unchanged. This packet proves the receiver square in the committed common
finite coordinate interface. It does not yet incorporate these laws into the
owning handoff certificate or prove the nominal-protocol and whole-gate adapters.

## Exact result

`ReceiverContent.Instructions` contains raw typed register initialization syntax
and an outcome-coordinate injection. It supplies no receiver run, predictive class,
activation verdict, or success flag. `receivedRun` interprets that syntax in the
actual target frame and projects its actual registers. `receive` decodes the
owning endpoint and gates that run on actual activation; `receivedClass` classifies
the factor of that returned run against the decoded target primitives. Missing
endpoint data and missing factor destinations return `none`.

`Laws` binds that interpreter to the same owning raw endpoint, factor maps,
historical histories/routes/receiver/realization, historical reset and target
presentation. The equations cover every input terminal, full past and event path,
and all five reset coordinates: factor, counter, ticks, residue and funding.
The factor map must be the decoded owning map and agree with the frame transfer.
No terminal-only agreement substitutes for the full history/path equations.

`arrival_endpoint_frame` starts with an actual `HistoricalAcquisition.Arrival`
and an actual decoded source-route reference. It derives the same full past,
event path and terminal at the historical reset, the actual receiver registers,
the endpoint reception and the projected target-frame factor. Activation comes
from the actual historical activation records, not from merely initializing a
run. The proof uses the existing checked execution embedding.

`factor_equations` obtains predictive-class transport from the actual owning
`RuntimeLineage.FactorReadout`, identifying both decoded tables and the map.
`content_faithful` combines it with active reception and an explicit pair of
distinct source classes. `ContentFaithful` requires decoded raw data, a genuine
distinct pair, a returned class for **every** raw input, and distinct returned
classes for **every** pair of distinct source classes. Neither empty input
coverage nor a `none`/`some` comparison satisfies this semantic readout.

`POS04ReceiverContent.checked_from_inputs` discharges the equations on every
partial assignment whose actual `acquisitionDependencies` are present, for every
raw `Protocol`, independently of package/lineage/autonomy acceptance. Interpreter
readiness is derived from those inputs. This is not a canonical-only proof or a
new assumption of a supplied receiver run.

## Argument classification

| Argument | Kind | Binding |
|---|---|---|
| `m : OwningHandoff.RawHandoff` | Raw model | Existing owning construction defines endpoint, factor, presentations and historical acquisition |
| `resetProgram` | Raw typed syntax | Actual `RegisterInitialization.initial` interpretation |
| `outcome : S → O` | Raw coordinate instruction | Every destination checked by `Laws.outcome` |
| Assignment and receiver input | Raw data | Same partial assignment, terminal, full past, path and identifiers throughout |
| `d`, `maps` in `Laws` | Decoded witnesses | Equalities to actual endpoint and factor-map decoders; absent inputs cannot furnish them |
| Interpreter readiness | Evidence on raw data | POS04 derives all four readies from consumed input completeness |
| `Laws` | Evidence on actual equations | All-input frame/projection equations and raw history/path/activation agreements |
| `FactorReadout` and distinct input pair | Semantic evidence | Existing actual owning factor readout; nonvacuity established separately |
| Received run, returned class, `ContentFaithful` | Defined readouts | No caller supplies these as structure fields |

## Coverage and direct controls

| Field or readout | Positive coverage | Control and exact meaning |
|---|---|---|
| Source/target factor tables and raw map | `factor_equations`, `distinct_source_classes_from_factor` | Constant reset leaves primitives fixed but actually equalizes returned classes |
| All target reset coordinates | `received_run`, universal POS04 `checked_from_inputs` | `reset_coordinate_guard` rejects the sufficient equations on any mismatch; this guard alone is not a semantic negative |
| Full histories and event paths | `arrival_endpoint_frame`, `Laws.histories/paths` | Actual Arrival and decoded route are required for the historical square |
| Activation and source presence | `arrival_frame`, `Laws.activation` | `source_absent_no_reception` directly computes returned run and class as `none`; `source_absent_not_faithful` rejects the named readout |
| Required endpoint inputs | `Laws.decoded` | `missing_endpoint_cell` applies to every missing required endpoint cell |
| Source tick input while target stays ready | `missing_ticks_initial_ready`, `missing_ticks_target_ready` | `missing_ticks_no_reception`, `missing_ticks_not_faithful`; no contradictory readiness premise |
| Every input's returned class and content distinction | `positive_content_faithful` | `constant_not_faithful` uses an actual unequal-source/equal-output pair |

The two explicit POS04 `inputA/inputB` tests are all-input reset probes with
different raw terminals. They are not advertised as new registered realized
historical routes or positive-support fixtures. Actual supported arrivals are
covered separately by the generic Arrival square. The source-absent assignment
is total and typed; the missing-source-tick assignment is genuinely incomplete
for the endpoint while remaining ready for initialization and the target frame.

## Statement classification and remaining limits

All 39 new theorem declarations and new definitions are **(b)** mathematical
additions. There are no **(a)** edits, renames, weakenings, changed existing
statements or new axioms. The strengthened new semantic readout requires total
successful classification as well as nonvacuous discrimination; the preliminary
Option-only definition could have counted `none` against `some` as distinct.
It was repaired before commit and independently reviewed in its final form.

The registry adds this component evidence and retains conditional status and
the frozen exact text. The previous owning audit is a historical receipt; its
receiver obligation is partially discharged here, while gate integration remains
open. Historical-support acquisition semantics, StrictSparse's representation
sensitivity, positive-support coverage, and sound but incomplete finite game
construction remain exactly the earlier disclosed boundaries. Common endpoint
coordinates do not establish arbitrary separate finite source/target embeddings.
The reset recipe is currently an explicit raw instruction argument of this
component, pending incorporation into the final owning interface.

The transcription checker preserves the exact frozen factor/record comparisons
and adds kernel examples for universal reset laws, total content preservation,
constant reset, source absence and missing source inputs. These are theorem
checks, not new empirical/frozen route fixtures or evaluation of noncomputable
classical projections.

## Independent review and verification

A fresh read-only Codex reviewer (`/root/receiver_review`, `gpt-6.1-sol`, high
reasoning effort) returned **ACCEPT for the stated common-coordinate receiver
component**, with no unresolved mathematical findings. The reviewer independently
compiled both final modules without warnings and audited 19 principal exports
transitively for axioms. It agreed with the totality repair and checked the
universal assignment scope, actual Arrival square and direct controls. Its
integration follow-up verified exact correspondence of all 39 new theorem names
with the registry, unchanged frozen text/status and other rows, regenerated
inventory equality, and the exact owning transcription probe plus frozen
factor/record comparison. Acceptance retains every completion limit above.

`lake build` passed with 525 jobs; final receipt:
`lean/.validate-logs/receiver-build.log`. All 39 individual `#print axioms`
probes passed and used only `propext`, `Classical.choice`, `Quot.sound`:
`lean/.validate-logs/receiver-axioms.log`.
`python3 -B scripts/check_tth06_transcription.py` passed with all 38 planted
drifts caught, including the new typed receiver examples:
`lean/.validate-logs/receiver-transcription.log`.
`git diff --check` passed; only TTH-06's kernel evidence, ceiling and rationale
change in the registry. No paper files were read or changed.

Final `scripts/validate_lean.sh` passed after the final registry wording update:
39 rows, 364 evidence entries / 363 unique names, 355 theorem-kind, 8
statement-only, 1 other definition; no placeholders, high-confidence vacuity
findings or untrusted axioms. Receipt:
`lean/.validate-logs/run-20261009T132556-535861Z/report.json` and
`lean/.validate-logs/receiver-final-validator.log`.
