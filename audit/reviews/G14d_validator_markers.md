# Independent validator marker review

**Verdict: ACCEPT.** No required fixes or new gate weakening found in the pinned repair. This accepts the validator instrumentation change, not the pending full integration or research goal.

Review scope: `scripts/validate_lean.py` and `scripts/selftest_validate_lean.py` against commit `00eed9557111fcb18fe8604701d2ab7d8df3ee61`, in `/mnt/8tb/six-birds-ml/tmp/csttt-final-integration-00eed955`. The review followed the owner brief at `lean/.validate-logs/validator-marker-review-brief.txt` and the mathematics-proof-review evidence-coverage discipline. Existing root selftest, full validator and original evaluator were neither launched, restarted, killed nor modified by this reviewer. Only ignored review/probe files were written.

## Pins and scope

Both files matched the supplied SHA-256 pins before and after the independent probes:

- `scripts/validate_lean.py`: `21dd514404cffc33df2a64711cf2990215e42b6a3cd525ddafe5ab7b1cbb8a6d`
- `scripts/selftest_validate_lean.py`: `5d39078e8a66ba51b0039a9abf7be06933600bae5bdf45a84fd763c477b409e3`

The isolated two-file diff adds an elaborator at `scripts/validate_lean.py:40`, replaces the two marker `#eval` commands at `scripts/validate_lean.py:189` and `scripts/validate_lean.py:193`, and adds/invokes `marker_cases` at `scripts/selftest_validate_lean.py:100` and `scripts/selftest_validate_lean.py:208`. The wider worktree also contains the owner's pending integration changes; they are not part of this instrumentation verdict.

AST comparison confirmed that `make_probe` is the only changed validator function. All source scanning, registry and inventory checks, attribution parsing, trust checks, row rollups, failure propagation, and final verdict logic are identical to the base. Existing selftest helpers and parser tests are identical; only `main` and the new `marker_cases` differ.

## Safety and kernel coverage

**No blocking findings.**

- `scripts/validate_lean.py:40–41`: the new command reads a string syntax node and logs a quoted message. It adds no axiom, declaration substitute, proof tactic, evaluation-based proof, or source exemption. A delimiter is instrumentation rather than theorem evidence. For the validator's regex-restricted declaration names (`scripts/validate_lean.py:19`, validated at `scripts/validate_lean.py:75`), interpolation cannot inject a quote, newline, or extra Lean command. The new emitted delimiter spelling matches the old `#eval` output.
- `scripts/validate_lean.py:190–192`: every selected declaration still receives the original `#check`, `#print axioms`, and `#audit_kind` commands. Their order, declaration names and full-import probe remain intact. The new delimiters avoid one generated interpreter closure per old `#eval`; no executable delimiter is necessary to inspect the actual declarations.
- `scripts/validate_lean.py:220–281`: the parser is unchanged. It still requires complete boundaries, exactly one correctly attributed check/axiom/kind message, reports marker sequencing errors, and preserves the transitive untrusted-axiom set. Marker messages alone cannot supply accepted declaration evidence.
- `scripts/validate_lean.py:329–332`, `scripts/validate_lean.py:348–358`, `scripts/validate_lean.py:359–399`: the exact three-item trust base, actual `lake build`, probe exit status, declaration failures, non-evidence kinds, statement-only row check and overall fail gates are unchanged. A nonzero or aborted Lean subprocess still prevents an overall PASS, even if some blocks parsed successfully. Fixture mode still cannot report full validation.
- `scripts/selftest_validate_lean.py:105–112`: the new real-declaration case exercises the declaration at the original crash boundary, including attributed kind and wrapped standard axioms. Independent execution confirmed its kind is `theorem`, with the same evidence as the base marker mechanism.
- `scripts/selftest_validate_lean.py:115–124`: the scale case checks 6,000 exact START/END pairs, including process success and complete line-for-line output equality. This tests delimiter scalability; it does not purport to replace declaration or kernel coverage. All eleven planted negatives and existing parser checks remain present.

## Independent checks executed

The reproducible ignored runner is `lean/.validate-logs/validator-marker-independent-checks.py`; detailed receipt and summary are `validator-marker-independent-checks.json` and `validator-marker-independent-checks.log` in the same directory.

1. Seventeen adversarial parser cases rejected identically to base: mislabeled evidence; missing START/END; duplicate START/END and complete blocks; nested alternate START; wrong END name; missing/duplicate check, axiom and kind outputs; an error inside the block; unquoted markers; and marker-only forgery. Wrapped trusted axioms remained attributed and parsed. A synthetic custom axiom remained outside the trust set.
2. Fresh small baseline and new Lean probes both exited 0 on three actual declarations: `CSTTT.PackageTheory.acyclicLocalWitnessGluing`, `CSTTT.Prospects.DetachedCopyCountermodel`, and the long `NativeReceiptExtensionPrototype.canonical_other_source_false` theorem. Their full parsed evidence dictionaries were identical. The Prop definition remained statement-only and the actual theorem remained theorem-kind. Logs: `validator-marker-independent-current.log` and `validator-marker-independent-baseline.log`.
3. A fresh nonexistent-declaration probe exited 1 and remained unresolved. Log: `validator-marker-independent-missing.log`.
4. A fresh independent local theorem depending on a planted custom axiom compiled, while `#print axioms` and the parser retained `CSTTT.MarkerIndependentReview.badAxiom` in `untrusted_axioms`. No repository theorem/source was modified. Log: `validator-marker-independent-transitive-untrusted.log`.
5. A fresh small delimiter probe emitted all 74 expected quoted lines exactly and exited 0. Log: `validator-marker-independent-small-markers.log`.

The base/current real-declaration probes use the pinned local Lean 4.28.0 toolchain. No full validator or full selftest was independently duplicated.

## Retained evidence and limits

`lean/.validate-logs/validator-marker-independent-coverage.json` records the AST comparison and separate inspection of owner-run artifacts. The retained owner scale log contains precisely the 12,000 expected lines; this is independently inspected output, not an independently executed large-scale run. The old full-run report at `run-20261010T161209-661224Z/report.json` records build PASS, probe exit 134, overall FAIL, 39 rows / 2,930 row entries / 2,888 unique declarations, and an explicit Lean-probe failure issue. The crash was not silently counted as success.

As with the base implementation, parsing a text transcript relies on the actual Lean subprocess, generated commands and trusted toolchain. Delimiters are not cryptographic authentication of arbitrary fabricated transcripts. The unchanged exact attribution checks reject forged/mislabeled or evidence-free marker blocks; this repair does not add a claim of immunity to an attacker fabricating every correctly named output message.

At review time the owner's full selftest log had recorded the initial six negative cases; this reviewer did not infer completion from that partial log. The revised full 2,888-declaration integration run was still pending according to the brief. Acceptance therefore permits the owner to continue the unchanged full validation gates; it is not evidence that those pending gates, the fifteen-module integration, or the full research goal have completed.
