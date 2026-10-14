# Ledger conventions

This file defines the columns and vocabularies of the paper's control ledgers. It was created in
W2 on 2026-10-13.

## `claim_ledger.csv`

This file is the prose ceiling. Every scientific sentence in the paper must fall under one row, and
no sentence may be stronger than that row's `allowed_claim`.

| Column | Meaning |
|---|---|
| `claim_id` | One of the following. The registry row ID (TTH-, TTN-, TTD-, TTF-, TTS-). A suffixed form of it (`TTH-06-GEN` for the generic theorem, `TTH-06-INST` for the POS-04 instance). Or a paper-level ID: `DEF-*` definitions, `HYP-*` interpretive hypotheses, `POST-*` postulates, `ART-*` artifact statements, `SCOPE-*` scope statements, `JOINT-COND` a supplementary result. |
| `source_rows` | The CST-TT-09 registry rows or assumption IDs the claim rests on. |
| `kind` | One of the following. `theorem`: generic over a class of models. `instance`: on one finite model. `theorem+instance`. `countermodel`: an exact finite refutation. `definition`. `hypothesis`. `postulate`. `method`. `scope`. |
| `status_09` | Copied from `CST-TT-09_THEOREM_STATUS.csv` for registry rows; `n/a` or `not a result` otherwise. |
| `role` | `main`: the main text states it. `supporting`: the main text uses it, or it is stated briefly. `appendix`: appendix only. |
| `model` | The finite model it holds on, with names as in `source_reconciliation.md` §4. `generic` means a theorem over a class of models. |
| `allowed_claim` | The strongest wording the paper may use. The wording is for the audience, but it is a ceiling, not final prose. |
| `evidence` | The headline Lean declarations, all fully qualified. There are two kinds. **Registry evidence** is listed in the closed CST-TT-09 inventory, `lean/row_inventory.json`, the campaign's evidence of record. **Supplemental paper evidence**, marked `[supplemental]`, is a valid declaration that is not in that inventory and is cited because the paper relies on it. Examples include the TTH-05 instance declarations and the three content lemmas behind TTH-06 (`PackageEngine.constructs`, `FutureLumping.all_words`, `StrategyGame.invariant_game_soundness`). The authoritative list is the `in_inventory=no` rows of `lean_declaration_map.csv`. Supplemental names are resolved and axiom-checked by the W3 evidence map like any other; inventory membership is not claimed for them. |
| `assumptions_and_scope` | Premises and scope that must stay visible in the paper, at the result or at its `nonclaim_survival.csv` destination. |
| `condition_grades` | The grade of each of the eight conditions on that model (see "Grade vocabulary" below), or `not package-bearing`. |
| `blocked_stronger_claim` | The nearest stronger claim the paper must not make. Where a repaired statement replaced a false original, the false original is named here. |
| `destination` | A logical slot (see below). W7 maps each slot to a section. |
| `ledger_status` | `ready`; `needs-W6` (depends on the cross-paper ruling); `optional` (may be omitted). |

## Grade vocabulary for the eight conditions

- **Design grade.** The condition as the architecture's design specifies it, at the interface fixed
  by the model's preregistration. On FULL-NATIVE-02 this is the G17/G30 interface. How this relates
  to the architecture paper's own check panel is settled in W6.
- **Surrogate (simplified form).** A declared stand-in that is weaker than the design condition.
  The stand-ins are defined in `audit/M3_model_spec.md:20-23` and summarized in
  `source_reconciliation.md` §4. In prose the word is "simplified form", always followed by what
  is simplified.
- **Substantive.** Computed from the model's own dynamics. This is the word `M3_model_spec.md`
  uses for conditions (1)–(3) and (8) on POS-04.

## Destination slots

| Slot | Content |
|---|---|
| `intro` | introduction |
| `intro-scope` | the single scope paragraph in the introduction |
| `setting` | finite setting, claim-reading convention, informal-word policy |
| `object` | the eight conditions recalled, the temporal signature, episodes, the record arrow |
| `strict` | the strict continuation theorem, its instances and its building blocks |
| `route` | route memory, holonomy, the global present |
| `autonomy` | autonomy after withdrawal, and finite versus unbounded maintenance |
| `boundaries` | copy, gap, public shadow, stalled clock, cyclic obstruction, re-encoding |
| `branching` | fission, symmetric forks, identity underdetermination, recombination |
| `direct` | direct succession and the broader path class |
| `ancestry` | the ancestry-based route: descent, least ancestry, twins, reconstruction, fusion, and the ancestry continuation result |
| `robustness` | defect semantics and the rational box |
| `objections` | Objections and replies |
| `limitations` | limitations (stated once) |
| `related` | related work |
| `availability` | data and code availability |
| `sixbirds` | the marked Six Birds appendix (corpus provenance) |
| `app-index` | result-to-Lean appendix (the only place for registry labels) |
| `app-proofs` | appendix proofs and supplementary results |

## `nonclaim_survival.csv`

Every limit the paper must keep visible. `destination` is one of: a slot from the table above, or
`at-result:<slot>`, meaning the narrative just before or after the result, never inside the theorem
environment. Multiple destinations are separated by `;`. In W17, Eddy checks every row against its
destination.

## `claim_taxonomy.csv`

One row per ledger row, with three columns:
- `lane`: structural, countermodel, definition, interpretive, ontological, recognition (an
  empirical premise, AS-31), bridge (certificate soundness, AS-30), method, or scope;
- `claim_form`;
- `paper_use`. Use it for grouping, not the free text of the ledger.
