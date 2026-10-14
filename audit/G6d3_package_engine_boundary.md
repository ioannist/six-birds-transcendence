# G6d-3 package engine boundary

## Proved

- Eddy's missing-view guard now concludes
  `¬ ∃ h : AcquisitionExecution.Ready raw a, Entry cfg raw a h entry`.
  It has no conflicting readiness premise. The other resource-seam guards
  were checked; their rejected value conditions are compatible with static
  readiness, or their conclusion itself is `¬ Ready`.
- `ObjecthoodProtocol` extracts a polymorphic C1 reference protocol: tau,
  epsilon, retention, P/C/U comparison tables and prototype order. Acceptance
  decodes raw cells, checks the generic objecthood rule and these raw equations.
  Uniqueness is derived by `verified_unique` through the committed verifier.
  `POS04ObjecthoodReference.generic_c1_iff` is exact in both directions for
  **arbitrary partial assignments**. `deleted_C_rejected` rejects actual input
  deletion on each tag. The published T1 data and thresholds are reused.
- `WeightedFibers` / `FutureLumping` give a generic **single-model** full-word
  induction. Raw mass equality on computed successor-code fibers suffices;
  individual hidden-branch probabilities need not agree. Every actual branch
  remains present. There is no supplied quotient model. Observation,
  successor-code and mass-mismatch guards reject this one-step check.
  `POS04FutureLumping.one_step` derives it on all runs from the existing finite
  class-mass/tick equations, with complete C6 inputs. `accepted_all_words`
  reuses assigned C6 acceptance. No `ActualBisim6` premise is added.
- `PackageEngine.constructs` uses the committed dependent TTH-01 gluing
  theorem to construct restrictions, completeness and global acceptance by
  locality for arbitrary dependent cell types, typed stages and checked covers.
  Locals and global are defined from the source, stage and cover.
- `POS04PackageEngine.p_iff` identifies the constructed-local/total-stage check
  with G6c's P for **every partial assignment**. All eight assigned algorithms
  are evaluated on the local/global assignments. `positive`,
  `deleted_primitive` and `package_controls` give the positive witness,
  rejection of any deleted primitive, and the published package-breaking
  controls through the same stage. This is a POS-04-family interpretation,
  not a completed generic raw-clause dispatcher.

## Argument and coverage boundaries

| Layer | Raw/evidence arguments | Defined objects / checks |
|---|---|---|
| C1 protocol | Typed views, arbitrary finite profile schema, numerical/reference data; evidence on decoded equations | Decoded raw operator, normalized-system candidate and uniqueness; dependency/locality and protocol guards |
| Future induction | Internal semantic model and raw one-step equations | Successor-code fibers, class masses, all finite word probabilities; three mismatch guards |
| POS-04 future boundary | Partial assignment, tag, completeness and finite bisimulation evidence | Existing owned actual-support future; no new candidate or horizon bound |
| Gluing engine | Typed source/stage/cover; checked totality, compatibility, dependencies and locality | Mapped locals, selector/glued global, restrictions and actual global acceptance |
| POS-04 P | Partial assignment only | Fixed-family stage/cover and the eight assigned evaluators; exact P equivalence and direct deletion |

**Engine-only callbacks:** `PackageEngine.rules` and its locality premise are
internal interpretation parameters, analogous to StrategyGame's internal
relations. They are not fields of RawHandoff. The POS-04 adapter fixes them by
`clauseAccept`, which reads assigned primitives. This seam does **not** present
these parameters as the final no-callback generic certificate interface.

Field guards are inherited from Substrate for dropped source/target arrows,
value/reference changes, uncovered/dependency cells, disconnected covers and
incompatible overlaps. The C1 decoder checks every consumed primitive; its
protocol-mismatch guard checks the reference equations. Future guards inspect
computed weights, successor codes and observations. They do not replace the
required whole-closure evolution/availability gates with sufficiency alone.

## Not yet proved

The closed polymorphic **eight-schema aggregator**, including the enclosing C6
trace/funding/profile/coarseness rules and C3 fixed-point completion, remains.
The gluing engine is finished; its full raw-algorithm boundary is not. Thus
G6d-3 as a whole is not yet complete. The exact POS-04 resource/acquisition
runtime adapters, same-cell generic G4/G1c projections, generic TTH-05 transport,
F/O RawHandoff assembly, controls/transcription and promotion follow in order.

TTH-06 remains conditional. No registry/inventory, science-bank, model,
prediction, result or paper files change. New constructions and the missing-view
repair are **(b) mathematical changes for TTH-06**. No existing row is narrowed.

## Checks

- `cd lean && lake build`: exit 0, 416 jobs; no warnings from these modules.
- `/tmp` probes: all 88 public theorems across this and the preceding resource
  seam resolve; only `propext`, `Quot.sound`, `Classical.choice` occur.
- `git diff --check` is clean. Frozen science/status files and the inventory are
  unchanged; no model declaration/evaluation and no `paper/` edits.
- `scripts/validate_lean.sh`: exit 0, all 39 rows / 210 declarations;
  heuristic source scan: placeholders=0 (gating), high-confidence vacuity=0 (gating), ignored-input leads=30 (reported only).
