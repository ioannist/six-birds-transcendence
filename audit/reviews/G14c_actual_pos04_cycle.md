# Independent review: actual assignment-sensitive POS-04 cycle

**Verdict: ACCEPT, at the existing POS04.Assigned acceptance boundary.** No substantive correction is required for this frozen ignored packet. This is not approval of public promotion, TTN status restoration, a full physical C4–C7 upgrade, or commit readiness.

The exact finite family consists of the eight existing Clause constructors, with local raw assignments `actualLocal c`. Every member satisfies the existing assignment-indexed `clauseAccept` and its actual gate. Every declared cycle edge agrees on every shared primitive cell, but no Assignment restricts to all these locals. In particular, no such restricting Assignment can also satisfy actual `AssignedPackagePass`. This directly establishes the finite-family local/global obstruction at the existing real acceptance boundary, rather than merely demonstrating failure of a sufficient gluing algorithm. A separately accepted canonical global package continues to exist.

## Independence and frozen inputs

I fully read the owner attachment, review brief, mathematics-proof-review skill, candidate source, construction note, explicit inventory, root axiom receipt, manifest, and frozen primitives/predictions. I independently inspected the actual clause predicates, scopes, decoders, future interpreter/bridge, gluing propagation theorem, historical CyclicObstruction construction, and original TTN-08 row. I did not use failed draft compiler output or compiler-generated sorryAx as evidence. No author/public/model/prediction/pin/paper artifact was edited. All reviewer writes are ignored `lean/.validate-logs/pos04-assigned-cycle-independent-*` artifacts. No full build or validator was launched. Root's sole live evaluator PID3263305 was observed live before and after the review and was not restarted, duplicated, interrupted, or killed.

Frozen SHA256 values:

| Artifact under lean/.validate-logs/ | SHA256 |
| --- | --- |
| POS04AssignedCycleCandidate.lean | 5c6e21fe1905c60ad8a81ebc2fbe4356ceb2946bfa804fd90a8f521194d8cf8d |
| pos04-assigned-cycle-primitives-predictions.json | 6d4b2d6381807bd6628ff914841a188e1510db86e1c629d92cfc4022cbbb6992 |
| pos04-assigned-cycle-construction-note.md | f06487b55bb6b71b92749b940cf89be581a7681f4be41b34063f10669e6232e6 |
| pos04-assigned-cycle-explicit-inventory.json | 8b605f730e403fad82cdc4d33ac74d3e82e7bf925b5bea49d49d6e3e21528cf6 |
| pos04-assigned-cycle-axiom-receipt.json | b9aa995395df7783996fccff6b52d85f6ef84b56b0f89e029e6846150d61f3e4 |
| pos04-assigned-cycle-source-hashes.json | a48d683f1db665b1caa271c6da3ba7e91436ee4f1e87d6bcf74f714bdc0bb3f6 |

All **75/75 manifest pins matched both before and after**; no mismatches. Receipts: `pos04-assigned-cycle-independent-pins-before.json` and `pos04-assigned-cycle-independent-pins-after.json`. The explicit inventory matches all 35 source declarations exactly, with the recorded class (b) classification. The construction/assembly is new, with no existing theorem silently narrowed.

## Fresh kernel and axiom evidence

Installed toolchain: Lean 4.28.0, as pinned by lean/lean-toolchain. Fresh direct `lake env lean` checks, without a full build:

| Check | Natural session | Exit | Evidence |
| --- | --- | --- | --- |
| Frozen candidate source | 34082 | 0 | independent-source.log, empty diagnostics |
| Candidate plus all 35 named #print axioms checks | 31157 | 0 | independent-allaxioms.lean/log; independent-kernel-receipt.json |
| Candidate plus eight independent adversarial symbolic proofs and axiom checks | 96067 | 0 | independent-adversarial.lean/log; independent-probe-receipt.json |

Here `independent-*` denotes the full `pos04-assigned-cycle-independent-*` prefix. All **35/35 named declarations** were checked, including definitions; **4 are axiom-free** and the other **31 depend only on subsets of propext, Classical.choice, Quot.sound**. There are no residual diagnostics, nonstandard axioms, holes, sorryAx, or native_decide in this passing evidence. The eight reviewer probes also have only the standard three axioms and no residual diagnostics. Root's older sessions/receipts are not substitutes for these independent natural completions.

## Located mathematical findings

1. **Actual acceptance, no invented diagonal.** Candidate:8,43–58 supplies the explicit raw position shift, exact existing `clauseScope` decoder, and proved acceptance for all eight locals. Assigned/PackageAssembly.lean:12–29 dispatches to C1Accept through C8Accept and establishes locality over arbitrary Assignments. Assigned/Substrate.lean:71–84,104–116 shows actual dependent Option-valued primitive assignments and actual scopes. This differs materially from POS04/CyclicObstruction.lean:98–108, whose new equality rule is conjoined with assignment-independent POS-04 side conditions. No independent acceptance callback or supplied derived future is introduced here.

2. **Whole C6, not a selected fragment.** Candidate:9–33 proves actual C6Gate, FiniteBisim6, and Coarser6. Assigned/C6Acceptance.lean:56–63 confirms this covers Ready/completeness and row validity, M/P reference comparisons, trace/path/tick/writer/resource checks, ledger conservation, exact interface, unit funding, bisimulation, and distinct merged roots. Candidate:35–36 and107–109 uses the actual ambient interpreter for shifted and the SAME decoded cycle C6 local. Assigned/C6ActualSupport.lean:14–16,90–92 retains actual Ambient successors; C6ActualFutureEquivalence.lean:78–95 uses exact probability lumping to obtain all finite word laws over arbitrary runs, not just representatives or audit roots. The bridge requires the proved finite bisimulation, not a free future-sufficiency input.

3. **Every real cycle edge and overlap.** Candidate:68–81 universally checks all shared dependent primitive cells, not only the changed position cell. Candidate:134–165 proves exact successor-cycle adjacency and reachability from C1. Every pair shares `.rows .target`; the reviewer additionally proved those local rows equal `some (actionRow .target)` and that an actual canonical action row is nonempty. Edge compatibility is not vacuous or based on empty local values.

4. **Direct readout refutation.** Candidate:83–91 defines actual literal restrictions and derives `some 0 = some 1` from C1/C6 positions at p0w0 for an arbitrary proposed global Assignment. Candidate:169–172 directly refutes the conjunction of restrictions and actual global package acceptance. This excludes all coherent globals for THESE fixed locals, not all package-passing globals. Candidate:184–190 constructs the repaired unshifted canonical global. Candidate:111–131 proves actual positions disagreement and failure of coordinate-restricted reach through the declared cycle using the established propagation lemma, while the underlying graph remains connected.

5. **Every partial input and missing-data rejection.** Candidate:176–181 proves localization equivalence for every Assignment and Clause;192–211 establishes completeness and actual rejection for every missing consumed cell. Internal totalizations do exist in Assigned/C123.lean:25–36, C457.lean:24–34, C6Dynamics.lean:20–26, and C8.lean:14–18. They do not rescue acceptance when a consumed input is absent. The reviewer proved specifically that deleting C6 positions yields the canonical internal position default AND actual clause rejection. Thus the note's claim concerns acceptance, not absence of internal getD totalizations, and is correct.

## Independent adversarial proofs

All eight successful symbolic probes are in the reviewer-owned adversarial source, not new predictive fixtures or evaluator/preregistration files:

- Outside-scope mutation preserves actual acceptance for every partial Assignment, Clause, Cell and typed replacement value.
- Erasing any consumed cell rejects actual clauseAccept for every partial input.
- C6 position erasure rejects despite the internal canonical position default.
- The completely empty partial Assignment rejects every actual clause.
- Each local really carries the canonical raw target row function, with a nonempty actual action row.
- These locals do NOT agree on all overlaps: the actual C1/C6 positions overlap disagrees. Only the explicitly declared cycle edges agree, as claimed.
- The existing numeric position shift preserves the predictive partition for every pair of KStates.
- The same actual decoded C6 local satisfies fullFuture equality for every pair of equal-code runs, every action word, and every observation trace.

## Exact target return and retained limitations

CST-TT-09_THEOREM_STATUS.csv:19 states the original TTN-08 finite-family claim and discloses the historical designed-control ceiling. The new packet constructively returns that existential obstruction with actual Assigned acceptance rather than the historical ClauseSpec equality rule. Its no-global readout is coherent **literal raw-cell restriction to the supplied locals**. It does not refute package existence on a different family, demand pairwise compatibility of all overlapping scopes, or establish obstruction modulo coordinate relabeling. The +1 shift preserves the predictive partition; the proved conflict is literal position-value disagreement. These qualifications do not defeat the stated finite-family gluing claim.

The construction note:21–23 correctly retains the existing surrogate grades. Assigned/C457.lean:70–84 still contains Exposed4; C5 retains protocol-credit acceptance; C6/C7 retain their declared execution/history semantics. No full physical C4–C7 result, TTN-02/14 restoration, registry/public promotion, or commit readiness follows. Those upgrades remain separate substantive obligations, and the review does not change any public status. Within the frozen packet's expressly declared acceptance and literal coherence semantics, the direct actual gluing obstruction is established and no mathematical fix is required.
