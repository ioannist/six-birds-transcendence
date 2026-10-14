# Figure and table plan

Packet W7, 2026-10-13. These are contracts for W14 (Cody, at high effort, TikZ). Claude writes the
captions.

## Global production rules

These rules are carried over from the consciousness papers.

- **Values.** Every value shown comes from `paper/data/current_results.json` through generated
  macros (`paper/figures/generated/figdata.tex`, written by `render_figure_data.py`, W8). Node
  labels never contain hand-typed numbers; a test enforces this. The one exception is the schematic
  Figure 1 (W20): its stage and callout numbers 1 to 4 are labels, not values, declared once in
  `fig_three.tex` and admitted by the manuscript checker only there.
- **Labels.** Only the paper's vocabulary: system, handoff, target, withdrawal. No repository
  dialect (the linter covers captions), and no registry labels.
- **Captions.** Captions describe the figure. Each has at most one scope sentence, and only where
  the figure could be misread.
- **Schematic figures.** A schematic figure says so. It never implies an instance it does not have.
- **Accessibility.** Colour-safe palettes, readable in greyscale. Every distinction is also drawn
  by shape or line style.

## Main figures

| ID | Section | Content | Data (snapshot keys) | Must not suggest |
|---|---|---|---|---|
| F1 | 1 | One passing episode and four look-alikes on aligned stage columns: latent target activated once, realization badge on the target only, live-overlap band between source and target, and autonomy after a shared withdrawal cut; separate R/L/A verdicts, with dashes for unevaluated gap checks. | none (schematic) | That any check implies another; that the target is built incrementally; ticks not proved for a row; full-grade conditions (4)–(7). |
| F2 | 3 | Merged into F1: detached-copy and gap rows now share its stage columns and withdrawal line. ID retained so F3–F7 are unchanged. | none (schematic) | Endpoint readout agreement as an identity verdict; realization or autonomy verdicts for the gap. |
| F3 | 4.1 | Left: an acyclic cover with running intersection. Right: the eight-piece cycle where adjacent pieces agree but a non-adjacent pair shares a cell and disagrees. | `pos04_staged_clause_count` | That the cycle is compatible on every overlap |
| F4 | 5 | The three-system chain with its two handoffs and withdrawal at each hop. | `g7_strict_chain_system_ids`, `g7_c3_trajectory` | Physical persistence; full-grade conditions (4)–(7) (the caption says once that (4)–(7) are simplified) |
| F5 | 6 | The two-state clock-translation loop: equal boundary, different present, nonzero holonomy. | none, or a parity label from a pinned value (to be added in W8 if needed) | A claim about experienced time |
| F6 | 7 | The fork: one source, two swap-related autonomous targets; the swap drawn as an involution. | `g7_fork_system_ids` | An identity verdict for either branch |
| F7 | 8 | The fusion model's timeline. Fission, the source withdrawn, each child's own acquisition, guarded fusion with retired parents, the fused output's acquisition. Checkpoints are marked. Inset: the settlement probabilities and the empty control. | `full_native_02_fusion_outcome_count`, `full_native_02_fusion_settlement_probabilities`, `full_native_02_empty_probability`, `full_native_02_physical_states`, `full_native_02_c8_factor_states` | That all certificates coexist; that fusion itself confers the conditions |

## Main tables

| ID | Section | Content | Data |
|---|---|---|---|
| T1 | 2 | The eight conditions (named, with the companion paper cited) against the three models (two-copy, chain, fusion), giving the grade on each: design grade, simplified form (with what is simplified), or not applicable. | `source_reconciliation.md` §4 and `claim_ledger.csv` `condition_grades`; refinement trajectories from the snapshot |
| T2 | 5 or 9 | The boundaries at a glance. Each countermodel gets one row: the shortcut it refutes, what it keeps equal, what fails. | ledger rows TTN-01–14 (text only; no numbers) |

## Appendix figures and tables

| ID | Appendix | Content | Data |
|---|---|---|---|
| A-T1 | C | Result-to-Lean index: result name, registry row, headline declarations, axioms, in-inventory flag | `lean_declaration_map.csv` (generated) |
| A-T2 | D | Repairs: original statement, counterexample, successor | `source_reconciliation.md` §3 |
| A-T3 | D | Conditioning: joint versus product | `g26_conditioning_event_weights`, `g26_conditioned_joint_mass`, `g26_product_of_conditioned_marginals` |
| A-T4 | B | Two-copy model data card: states, lethal states, C1 mass, TV, defect, staged map | `pos04_*` (state and lethal counts after the W4b pins) |
| A-F1 | B | The fusion model's physical factor and its operational core | `full_native_02_physical_states`, `full_native_02_operational_core_states` |

## Production order and acceptance checks

1. W8: `render_figure_data.py` and the drift test; figure macros for every key above.
2. W14: F1–F7 and T1 (Cody, high effort). Claude checks the rendered pages and Eddy reviews.
3. **Acceptance:**
   - 0 overfull boxes;
   - each figure fits within the text width at 11pt;
   - the drift test passes;
   - the linter is clean on captions;
   - each "Must not suggest" item above is checked by Eddy against the rendered figure.
