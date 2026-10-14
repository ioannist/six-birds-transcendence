# G6a predictions — full F and supplementary operational O

**No outcomes computed.** These are revised pre-registration predictions, not
results. Authority: [G6 lane specification](G6_lane_spec.md) and
[TTH06-LANES.model.json](proposed_models/TTH06-LANES.model.json).
The SAME raw models/mutations and P/L predicates are used in both versions;
AF and AO are different fixed autonomy predicates, never per-case choices.

## Version F — primary full package-preserving autonomy

F reads “none ... is inferred” proof-structurally: package, lineage and autonomy
evidence are each constructed separately. **AF logically implies P**, predicted
below, and F explicitly does not assert logical independence of all three lanes.

| Case | Predicate | Prediction | Meaning if wrong |
|---|---|---|---|
| Baseline | P | pass | The assignment/gluing adapter does not reproduce the positive package; no control interpretation from a failing baseline. |
| Baseline | L | pass | The shared corridor/bridge adapter does not reproduce positive lineage. |
| Baseline | AF | pass | Full packageInside, total responses or the retained-resource/run-law extension is not supported. This is a genuine failed FULL-autonomy prediction, even if AO passes. |
| G6-PACKAGE-ONLY | P | fail | Required C1 input/map completeness did not reject the missing publishedC cell. |
| G6-PACKAGE-ONLY | L | pass | Evidence deletion affects lineage as well; report the unanticipated extra side effect. |
| G6-PACKAGE-ONLY | AF | fail | Failure contradicts the declared packageInside implication AF→P, or one of the two predicates was implemented incorrectly. This expected joint rejection is a consequence, **not an isolation control**. |
| G6-LINEAGE-ONLY | P | pass | Support removal also rejects an assigned package clause; this F isolation is confounded. **Lower confidence.** |
| G6-LINEAGE-ONLY | L | fail | The fixed mix_2 source/intervention audit is not gated as declared, or the control does not break lineage. |
| G6-LINEAGE-ONLY | AF | pass | A packageInside or response side effect defeats the F lineage-only isolation. **Lower confidence for the new full adapter.** |
| G6-WITHDRAWAL-ONLY | P | pass | Withdrawal retention leaked into ARRIVAL package acceptance; this F isolation is confounded. |
| G6-WITHDRAWAL-ONLY | L | pass | Post-withdrawal retention changed pre-withdrawal lineage/route evidence; this F isolation is confounded. |
| G6-WITHDRAWAL-ONLY | AF | fail | Missing essential retained recharge did not reject full package/resource/response closure, or a stored safe-set shortcut bypassed the checks. |

**Additional primary theorem prediction:**

```lean
fullAutonomy_implies_package : ∀ m, AF m → P m
```

Predicted true, with endpointInside and packageInside the substantive certificate
obligations supplying the implication. The logical contrapositive `¬P → ¬AF`
is disclosed. If refuted or unproved, report it; do not remove packageInside.
The generic primary readout is predicted to construct its P evidence via G2c,
its L evidence via G4/G1c and AF via the independently checked invariant/response
proofs, rather than using AF to fill the P certificate field.

F vectors `(P,L,AF)`:

- baseline: `(pass, pass, pass)`;
- package deletion: `(fail, pass, fail)` — predicted forced consequence;
- lineage isolation: `(pass, fail, pass)`;
- autonomy isolation: `(pass, pass, fail)`.

## Version O — supplementary operational C8 autonomy (N3)

O omits full packageInside and tests operational C8 controlled viability. It uses
the SAME declared nominal disturbance and response semantics, resource rules,
endpoint/run updates and actual rows; it does not substitute action labels for
disturbances. O cannot serve as the primary full-autonomy result.

| Case | Predicate | Prediction | Meaning if wrong |
|---|---|---|---|
| Baseline | P | pass | Positive package/gluing adapter failed; reject clean isolation interpretation. |
| Baseline | L | pass | Positive raw lineage adapter failed. |
| Baseline | AO | pass | Operational invariant/response/retention adapter failed to reproduce the positive funded target. |
| G6-PACKAGE-ONLY | P | fail | Missing required C1/map input was not detected. |
| G6-PACKAGE-ONLY | L | pass | Package metadata deletion also breaks lineage; the O control is confounded. |
| G6-PACKAGE-ONLY | AO | pass | Operational autonomy reads full package validity or the missing C1 table; the O control is confounded or its predicate was changed. |
| G6-LINEAGE-ONLY | P | pass | Support change breaks another package gate (especially C6/C7); the O control is confounded. **Lower confidence.** |
| G6-LINEAGE-ONLY | L | fail | The fixed audited source vertex/intervention gate does not reject as declared. |
| G6-LINEAGE-ONLY | AO | pass | Operational target responses depend on broken pre-exit support rather than their declared boundary; the O control is confounded. |
| G6-WITHDRAWAL-ONLY | P | pass | Post-exit retention affects arrival package checks; O isolation is confounded. |
| G6-WITHDRAWAL-ONLY | L | pass | Withdrawal affects pre-withdrawal bridge/route checks; O isolation is confounded. **Lower confidence for the new shared adapter.** |
| G6-WITHDRAWAL-ONLY | AO | fail | The essential resource-removal rule did not destroy continuing funded viability/response closure. |

O vectors `(P,L,AO)`:

- baseline: `(pass, pass, pass)`;
- package isolation: `(fail, pass, pass)`;
- lineage isolation: `(pass, fail, pass)`;
- withdrawal isolation: `(pass, pass, fail)`.

Only after all three isolated controls are evaluated and proved do they witness
logical independence in this family. These are predictions, not a concluded
independence theorem.

## Shared and version-specific secondary predictions

| Case/version | Additional prediction | Meaning if absent/different |
|---|---|---|
| All | Unchanged syntax/type/raw-reference/action-row well-formedness passes. Missing C1 evidence is an allowed partial assignment, not an invalid control. | Report invalid control separately; completeness failure is a semantic package gate, not JSON invalidity. |
| All | Disturbance domain is the singleton `nominal`, separate from three control actions; response search quantifies over EVERY state/disturbance and tests EVERY supported successor. | A bounded trace or one lucky successor does not establish either declared autonomy predicate. |
| Baseline F | Computed SF is K; every withdrawn packageAt state passes, and both routes' actual post-probe entry successors are inside; each state has a safe target-owned nominal response (canonical policy predicted as witness). | Exact safe set, failed state/clause and failed disturbance must be reported; AO passing cannot rescue a failed AF prediction. **New-model prediction, lower confidence.** |
| Baseline O | Computed SO is K; all post-probe endpoints are inside and total funded responses exist. | Explicit nominal interface or withdrawal adapter failed. |
| Package deletion F | Source/target C1 and map totality fail; packageAt rejects all candidate states and SF is empty, hence AF fails. | The forced package/full-autonomy dependence was not implemented faithfully. No physical loss of T1 objecthood is inferred from evidence deletion. |
| Package deletion O | AO/SO and their action rows/resources remain identical to baseline; C2–C8 still pass on both tags. | Report exact unexpected within-package effects; L/AO failure defeats isolation. |
| Lineage mutation F/O | Only mix_2.sourceSupport changes; mix_1 remains realized/mixed, mix_2-source audit vertex is absent; every assigned package clause still accepts on both tags, and the pre-withdrawal receiver/route probe remains available. | Any package failure confounds both isolation claims; any full-autonomy-only failure must identify packageInside/response cause. **Lower confidence.** |
| Withdrawal mutation F/O | Assignment B and pre-withdrawal route outputs/corridor/bridge remain identical to baseline. Only post-exit retention changes. | The mutation was not applied exactly as declared. |
| Withdrawal mutation F | Resource closure and continuing responses reject; SF is empty; withdrawn package C6/C8 are predicted to reject computed missing recharge as well. | Report all full-autonomy failure causes, not just an empty-set flag. This does not make arrival P fail. |
| Withdrawal mutation O | Computed recharge availability is false and SO is empty; no declared continuing funded nominal response exists. | Operational essential-resource semantics failed. |

The unchanged 1/1/1 ARRIVAL ledger contains one prepaid token. The negative
predicts failure of a positive conserved-budget **continuing invariant**, not
impossibility of every isolated prepaid action. Effective recharge is zero when
its resource is not retained. No new result is asserted about adversarial
exogenous disturbances: none is declared.

## Separate outcome and confounding rules

Use the standard six categories, with separate F and O reporting and isolation
counts. For F, only lineage and autonomy cases are intended isolated controls;
P/AF joint rejection is `CONFIRMED` as a dependence prediction when observed,
**not** `CONFIRMED-CONFOUNDED` and **not** a clean ablation count. Unexpected extra
failure in either F isolation is confounded. O still requires three clean
isolations; any second false lane is confounded.

A failed baseline prevents clean negative interpretation (`CONFIRMED-NARROW`
where appropriate). Unchanged well-formedness failure is `INVALID-CONTROL`.
Incomplete adapter/predicate coverage is `UNDETERMINED`, never a pass. Report
each scalar prediction separately from whether the full vector is confirmed.
If a prediction fails, it stays failed. No disturbance, package predicate,
audit selector, phase order or mutation may be changed to rescue it.

F's primary ceiling is full preservation of the **declared graded package**,
with total target-owned responses in the nominal environment and proof-structural
lane evidence. C4–C7 remain surrogates; this is not full P05/T17-I or physical
continuation. O has the explicitly narrower N3 operational ceiling. Recognition
is not addressed in either version. No registry promotion happens in G6a.
