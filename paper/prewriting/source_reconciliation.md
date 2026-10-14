# Source reconciliation: CST-TT-08 paper-facing text versus the CST-TT-09 Lean status

Status date: 2026-10-13 (packet W2). This is a control memo, not paper prose.

## Why this file exists

The repository has two generations of paper-facing material:

- **CST-TT-08** (frozen 2026-09-28): `cst-tt/handoff/CST-TT-08_SCIENCE_HANDOFF.md`,
  `FINAL_CLAIM_CEILING.md`, `PAPER_RESULT_TABLES.md`, `FINAL_THEOREM_AUDIT.md`, `cst-tt/docs/*`,
  and the `FINAL_*` registries. These were written before any Lean build succeeded. They record
  19 conditional rows, 8 open rows, and 0 proved.
- **CST-TT-09** (closed 2026-10-12, `ba3e5dd`): `cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv`
  (`status_09`, `ceiling_09`, `delta_rationale`), `lean/row_inventory.json`, and
  `cst-tt/handoff/CST-TT-09_LEAN_STATUS.md`. All 39 rows were compiled in Lean 4.28 (core only,
  standard axioms). Wrong statements were repaired explicitly.

The paper's claims come only from the CST-TT-09 surface (`paper_plan.md`, "Source authority").
CST-TT-08 text is provenance. It may be quoted as history, never as a current result. This memo
lists every CST-TT-08 paper-facing statement that the current surface changes, so that no drafting
packet copies one forward by accident.

## 1. Status counts

| Status | CST-TT-08 | CST-TT-09 (current) |
|---|---:|---:|
| proved | 0 | 25 |
| checked finite countermodel | 12 | 14 |
| conditional | 19 | 0 |
| open | 8 | 0 |
| **total** | 39 | 39 |

- TTN-04 and TTN-05 moved from conditional to checked finite countermodel.
- Every TTH, TTD and TTS row, and every TTF row, is now proved at its recorded ceiling.

**What the closure covers.** It covers the approved statements at their registered ceilings,
including explicit repairs and disclosed grades (`CST-TT-09_LEAN_STATUS.md`, "Closure scope").
It does not prove unrestricted historical formulations.

## 2. CST-TT-08 statements that are superseded

| CST-TT-08 statement (source) | Current position | Paper consequence |
|---|---|---|
| "no theorem is marked `proved`"; constructive rows "conditional" until `lake build` (handoff §3, §11) | 25 rows proved, 14 countermodels, standard axioms only | Report the CST-TT-09 counts only. Neither paper mentions the old counts. |
| "Temporal-IAPS remains open but unauthorized" (README, handoff §1) | TTF-05 proved on FULL-NATIVE-02 under the two readings the author approved on 2026-10-12 | The ancestry-based result is a main result with its own name, kept distinct from the strict result (style guide, Section 2). |
| "an integrated finite C1-C8-shaped target package with substantive temporal closure" (handoff §2) | On POS-04, POS04.Assigned and the G7 native model, conditions (4)–(7) hold only at **surrogate grade** (see §4). On FULL-NATIVE-02, all eight are computed from one execution at the G17/G30 design interfaces, with condition (4) limited to the current-family privacy statement. | Never write "realizes the architecture" for a strict-continuation instance. Grade wording is fixed per claim row in `claim_ledger.csv`. |
| "post-withdrawal autonomy" as one landed lane (handoff §2; claim-ceiling row "post-withdrawal autonomy") | TTH-05 is a **generic** finite-horizon theorem. The registry delta says that no POS-04 certificate instantiates it. That is superseded: `POS04HistoricalRuntimeInstance.positive_each_entry_exact` and `positive_each_entry_words` derive an instance by projecting the historical runtime to a finite factor. The frozen model data alone still do not supply one. The POS-04 autonomy inside TTH-06 is the nominal-protocol autonomy readout. FULL-NATIVE-02 has package-preserving autonomy (TTF-05). The G7 native model has funded autonomy games (TTH-07). | Say which autonomy notion each result uses. Cite TTH-05's POS-04 instance only as the derived finite-factor instance. |
| "A total policy yields model-relative unbounded maintenance for every admissible disturbance stream" (handoff §7) | TTS-04 is proved only as the N10 successor: a finite factor plus unbounded event registers, a fixed policy, unit disturbances and a unit account. A finite full-state run of that kind provably cannot exist. | State the factor-plus-registers form, and include the impossibility of a finite full-state version. |
| "Route residue may be erased only when an explicit flatness, normalization, or confluence certificate proves that alternative routes agree" (handoff §5; TTH-09's original "only under") | N6 repair: the necessity reading is false (a three-route control has equal endpoints but no license). Sufficiency is proved on a declared comparison domain. | State sufficiency only. The necessity reading is a recorded repair (§3). |
| The direct-successor criterion "excludes … arbitrary data reachability" (TTD-03 original) | N8 repair: literal exclusion is false. Four mechanism exclusions hold, reachability alone does not imply direct succession, and a data path can coexist with direct succession. | State the repaired form. |
| "survives a declared componentwise perturbation box" (claim-ceiling row "robustness"; TTS-03 original) | N9 repair: holds in a rational-register extension on a fixed first event, for the closed five-component half-box, with both complete gates preserved. It is not a return to the original integer differences. | State the rational-register form and its fixed event. |
| "A symmetric live fork can relate one source to two targets" (handoff §6) | Holds on the G7 native fork (17→201/202), with surrogate grade for conditions (4)–(7). A Fin3 counterexample shows the old fork certificate allowed an outside fixed continuer. | Cite the native fork and keep the grade. |
| "13/13 primary/common toy battery"; "174 nodes and 288 edges"; "28 contracts"; "19 statement-level sources"; toy-evidence table 9/16/3 (handoff §2, §8; result tables) | CST-TT-08 artifact counts. Not refreshed for CST-TT-09. | Not used in the paper. Release counts come from a fresh W19 run. |
| "All theorem-core carriers, alphabets, episodes, and certificate data are finite and exact" (AS-01) | Physical factors, alphabets and check objects are finite. The current results also use unbounded run spaces (TTH-06, TTH-07), all future words (TTH-03), unbounded event registers (TTS-04), and growing histories with universal full-history lifting (TTF-05), all proved by invariants in Lean. | State the finite and the unbounded parts separately (ledger DEF-FINITE). |
| Conditioning factorization implicit in joint-law language (G26 target) | Refuted: weights 1 and 9 give a joint of 1/10 against a product of 1/100. The repaired law is a weighted sum of fixed-world products. | If joint laws appear, use the weighted-sum form only. |
| TTN-02 "hidden consciousness-relevant structural predicates"; TTN-14 "integrated binding" (CST-TT-08 wording) | Narrowed in CST-TT-09 to finite predictive-readout nonidentifiability (TTN-02) and to finite joint-coupling and recombination failure for the surrogate (TTN-14). | State the narrowed forms. |
| TTF rows worded "Open fallback target: …" (registry `exact_statement`) | Historical target naming. Every TTF row is proved, and TTF-06/07 are proved in **repaired** form (§3). | Use the repaired statements. The original schemas are false as written. |

## 3. Repairs: original statements found false, and their successors

The paper may mention a repair where it helps the reader, for example "a stronger form is false;
here is why". It must never state an original form as true.

| Row | Original (false as stated) | Counterexample | Successor proved |
|---|---|---|---|
| TTH-09 (N6) | Equal endpoints of same-boundary routes **only under** a flatness, normalization or confluence license | Three one-event routes; r0 and r1 have equal endpoints and no license on the fixed domain | Each license is **sufficient** for equal endpoints on a declared raw-path comparison domain |
| TTD-03 (N8) | Direct succession excludes arbitrary data reachability | `directWithData`: a genuine direct successor with an independent data path | Four mechanism exclusions; reachability does not imply direct succession; the two can coexist |
| TTS-03 (N9) | Every perturbation in the exact margin preserves all advances and every hard gate | A quarter-correction cannot be an original integer difference; a constant receiver keeps the numbers positive but fails the gates | Every correction in the closed rational half-box preserves the advances and both complete gates, in the rational-register extension, on the fixed first event |
| TTS-04 (N10) | A total policy on the finite invariant gives an infinite full-state run | No infinite strictly progressing run fits a finite full-state space | A finite factor plus unbounded event registers, for every positive-supported stream |
| TTF-06 (G16) | Reconstruction/twin separation stated with ancestry from one target to another | Refuted for every partial prefix (target-to-target query) | Rooted separation: the source is an ancestor of the reconstruction and not of the independent twin |
| TTF-07 (G16) | The existential-negative schema for an arbitrary identity relation | Identity := True refutes it | Two ancestry-compatible identity relations give opposite branch verdicts, so ancestry alone underdetermines identity |
| (G26, no row) | Conditioned joint law = product of the conditioned marginals | Weights 1 and 9: 1/10 versus 1/100 | Weighted sum of fixed-world products |

Statement-preserving refutations of **older interfaces** also exist. They do not change any current
claim and belong in the appendix at most:
- TTH-06: the legacy gates are not equivalent to the complete lineage gate.
- TTH-07: the older parent interfaces were refuted.
- TTH-08: the Fin3 certificate counterexample.
- G27: the all-stagings C1 uniqueness gate fails, by a period-two counter-trace.
- G29: the original IAPS schema fails on the G27 candidate only.

## 4. Finite models and condition grades

The detail comes from the W2 research note, checked against `audit/M3_model_spec.md:17-24`,
`audit/G7_native_episode_construction_draft.md`, `audit/G27_full_native_package.md:9-50`,
`audit/G30_full_native_02_preregistration.md:115-125,335-340` and
`audit/G31b_full_native_autonomy.md:66-72`.

| Model | Plain description | Grades of conditions (1)–(8) | Rows |
|---|---|---|---|
| POS-04 / POS04.Assigned | Two tagged copies (source and target) of the companion paper's ten-state deadline system: 24 tagged states, with event, budget and route registers | (1)–(3) substantive, computed from the deadline system. (8) substantive operational viability (greatest funded kernel, empty when underfunded). **(4)–(7) surrogate**: (4) a same-current/different-predictor collision, not full non-exposure; (5) a declared three-cycle credit rule; (6) a newly declared event order and record/tick lift; (7) a declared coupling, not dynamics-derived binding. | TTH-02, 03, 04 (one leg), 05 (derived instance), 06, 10; TTN-02, 04, 06, 08, 09, 13, 14; TTS-03; TTF-01 instance |
| G7 native handoff model | Eight-state finite factor (three bits: phase, visible, hidden) with unbounded counter, tick and history registers; chain 17→55→101 and fork 17→201/202 | (1) genuine nonuniform fixed point after the availability repair. (2) computed factorization split. (3) recursive profile 2→4→4. (8) computed greatest viability, empty after a recharge cut. **(4)–(7) surrogate.** | TTH-07, 08; TTS-04; the native overlap witness in TTD-02/TTS-01; the historical package for TTF-08 |
| FULL-NATIVE-02 | 32 physical states with two installed programs, addresses, tokens and accounts; finite viability factor 64 = 32 × charge | All eight computed from one installed execution, at the design interfaces of the G17/G30 preregistrations. (4) is current-family privacy on maintained support only, not full privacy. (5) and (6) use the first approved reading. (1) has honest stationarity, retention and defect grades, with a period-two two-step counterexample retained. | TTF-04, TTF-05 |
| FULL-NATIVE-01 (G17/G27) | The same 32 physical rows under the first protocol | All eight at the G17 design interfaces, as a checkpoint package. Every immediate successor fails package acceptance under the old admission rule (G29). | Supplementary restorations of TTN-02/14; obstruction evidence. No positive row of its own. |
| Small controls (N2 and others) | Tiny dedicated systems: detached copy, reversible route maps, mod-2 loop, singleton clock, defect vectors, relabeled fork, countdown for every horizon, three-route domain, direct-successor controls | Not package-bearing, unless the row says so | TTN-01, 03, 05, 07, 10, 11, 12; TTH-09; TTD-01–03; TTS-01 |
| Operational fallback (G13/G14) | Snapshot, erase, gap and activation execution, plus guarded-fusion runtime | Not package-bearing | TTF-02, 03, 06, 07 |

**Two facts the paper must not blur:**

1. **No single model carries both strict live-overlap lineage and all eight conditions at their
   design grade.**
   - The strict-continuation instances (POS-04, the G7 native chain and fork) meet conditions
     (4)–(7) only at surrogate grade.
   - FULL-NATIVE-02 computes all eight from one execution, but its lineage is predictive ancestry,
     not strict overlap.

   Any sentence that combines the two results must say this.
2. **The ancestry-based certificates on FULL-NATIVE-02 are certificates at different checkpoints.**
   The source package is an earlier copied checkpoint. The children's certificates precede their
   later retirement, and the fused output's certificate follows its own acquisition. Nothing
   claims they all coexist (`G30:335-339`).

## 5. Interpretive and ontological assumptions

No current row uses any of AS-26 to AS-32 as a premise; all 39 `assumption_ids` cells were
checked. These are AS-26 H-FELT-TIME, AS-27 H-CONT-TIME, AS-28 A1, AS-29 A2-P, AS-30 certificate
soundness, AS-31 recognition and AS-32 personal identity. The paper may state them as hypotheses
or postulates that a reader can grant or decline. No result's conclusion contains them. The
charter forbids using A2 as a transport theorem and forbids formalizing it by quantifying over
system types (`cst-tt/charter/PROJECT_CHARTER.md:61,69`; `NONGOALS_AND_SCOPE_GUARDS.md`). Results
are stated as moving from one finite system to another, never across substrates.

## 6. Deferred to W6

Two questions are deferred to W6, the overlap and cross-paper consistency packet:
- whether the FULL-NATIVE-02 package counts as an "integrated instance" in the architecture
  paper's sense;
- what the paper says about Substrate Indifference.

The ledger rows that depend on that ruling are marked `needs-W6`.
