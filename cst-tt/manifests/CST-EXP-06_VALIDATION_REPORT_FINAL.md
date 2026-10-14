# CST-EXP-06 Validation Report

**Result:** PASS — 1440/1440 checks passed.

| # | Check | Result | Detail |
|---:|---|---|---|
| 1 | Repository has Git metadata | PASS | .git |
| 2 | Frozen CST-EXP-05 manifest pin exists | PASS | manifests/CST-EXP-05_MANIFEST.json |
| 3 | Prior manifest is labeled CST-EXP-05 | PASS | CST-EXP-05 |
| 4 | Prior manifest has a substantial file bank | PASS | 494 |
| 5 | Inherited CST-EXP-05 scientific surfaces remain byte-frozen | PASS | {"bad": [], "checked": 429} |
| 6 | Phase modifications stay inside the declared CST-EXP-06 scope | PASS | [] |
| 7 | No Lean implementation was added or modified | PASS | [] |
| 8 | Required phase output exists: synthesis/FINALIST_COMPARISON.md | PASS | 13599 |
| 9 | Required phase output exists: synthesis/TARGET_SELECTION_SCORECARD.csv | PASS | 42456 |
| 10 | Required phase output exists: synthesis/PRIMARY_TARGET_SPECIFICATION.md | PASS | 16144 |
| 11 | Required phase output exists: synthesis/FALLBACK_TARGET_SPECIFICATION.md | PASS | 9513 |
| 12 | Required phase output exists: synthesis/COPY_VS_CONTINUATION_AUDIT.md | PASS | 6657 |
| 13 | Required phase output exists: synthesis/EXPLORATION_DOSSIER.md | PASS | 12070 |
| 14 | Required phase output exists: synthesis/LATER_LANDING_HANDOFF.md | PASS | 4567 |
| 15 | Required phase output exists: synthesis/TARGET_REGISTRY.json | PASS | 1432 |
| 16 | Required phase output exists: synthesis/TARGET_SCENARIO_VERDICTS.csv | PASS | 34660 |
| 17 | Required phase output exists: synthesis/FROZEN_THEOREM_FAMILY.csv | PASS | 4340 |
| 18 | Required phase output exists: synthesis/FROZEN_WITNESS_SUITE.csv | PASS | 2296 |
| 19 | Required phase output exists: synthesis/frozen_target_architecture.svg | PASS | 10242 |
| 20 | Required phase output exists: changelog/CST-EXP-06.md | PASS | 995 |
| 21 | Required phase output exists: manifests/EXP06_ASSET_SUMMARY.json | PASS | 974 |
| 22 | Normative plan contains CST-EXP-06 phase | PASS | plan phase |
| 23 | Normative plan names required output synthesis/FINALIST_COMPARISON.md | PASS | synthesis/FINALIST_COMPARISON.md |
| 24 | Normative plan names required output synthesis/TARGET_SELECTION_SCORECARD.csv | PASS | synthesis/TARGET_SELECTION_SCORECARD.csv |
| 25 | Normative plan names required output synthesis/PRIMARY_TARGET_SPECIFICATION.md | PASS | synthesis/PRIMARY_TARGET_SPECIFICATION.md |
| 26 | Normative plan names required output synthesis/FALLBACK_TARGET_SPECIFICATION.md | PASS | synthesis/FALLBACK_TARGET_SPECIFICATION.md |
| 27 | Normative plan names required output synthesis/COPY_VS_CONTINUATION_AUDIT.md | PASS | synthesis/COPY_VS_CONTINUATION_AUDIT.md |
| 28 | Normative plan names required output synthesis/EXPLORATION_DOSSIER.md | PASS | synthesis/EXPLORATION_DOSSIER.md |
| 29 | Normative plan names required output synthesis/LATER_LANDING_HANDOFF.md | PASS | synthesis/LATER_LANDING_HANDOFF.md |
| 30 | Target registry phase is CST-EXP-06 | PASS | CST-EXP-06 |
| 31 | Target registry generated date is frozen | PASS | 2026-08-10 |
| 32 | Primary target ID is FT-01 | PASS | FT-01 |
| 33 | Primary target code is FIACH | PASS | FIACH |
| 34 | Fallback target ID is FT-02 | PASS | FT-02 |
| 35 | Fallback target code is IAPS | PASS | IAPS |
| 36 | Mandatory companion is FT-NG | PASS | FT-NG |
| 37 | primary separately declares S-R, S-L, and A | PASS | ["S-R", "S-L", "A"] |
| 38 | primary has exactly two source survivor families | PASS | ["SF-01", "SF-02"] |
| 39 | primary has a nonempty mandatory component bank | PASS | ["TS-02", "TS-03", "TS-04", "TS-06", "TS-07", "TS-08", "TS-09"] |
| 40 | primary registry states an ontological nonclaim | PASS | no consciousness, personal survival, numerical identity, empirical recognition, certificate soundness, a1, or a2-p conclusion follows. |
| 41 | fallback separately declares S-R, S-L, and A | PASS | ["S-R", "S-L", "A"] |
| 42 | fallback has exactly two source survivor families | PASS | ["SF-01", "SF-03"] |
| 43 | fallback has a nonempty mandatory component bank | PASS | ["TS-01", "TS-02", "TS-04", "TS-06", "TS-07", "TS-09", "TS-10"] |
| 44 | fallback registry states an ontological nonclaim | PASS | structural successorship is relation-valued and is not numerical identity or proof of conscious survival. |
| 45 | Primary uses SF-01 plus SF-02 | PASS | ["SF-01", "SF-02"] |
| 46 | Fallback uses SF-01 plus SF-03 | PASS | ["SF-01", "SF-03"] |
| 47 | Scorecard has 161 rows (7 × (10 hard + 12 soft + 1 summary)) | PASS | 161 |
| 48 | Scorecard covers exactly seven finalist architectures | PASS | ["F-01", "F-02", "F-03", "FT-01", "FT-02", "FT-03", "FT-NG"] |
| 49 | All scorecard candidate/criterion keys are unique | PASS | unique |
| 50 | F-01 has ten hard-gate rows | PASS | 10 |
| 51 | F-01 hard-gate results match frozen data | PASS | {"HG-01": "pass", "HG-02": "pass", "HG-03": "pass", "HG-04": "pass", "HG-05": "pass", "HG-06": "pass", "HG-07": "pass", "HG-08": "pass", "HG-09": "pass", "HG-10": "fail"} |
| 52 | F-01 has twelve soft rows | PASS | 12 |
| 53 | F-01 soft weights total 100 | PASS | 100 |
| 54 | F-01 soft scores stay within 0–5 | PASS | ["3.0", "4.5", "4.0", "4.0", "3.5", "3.5", "5.0", "4.0", "4.0", "5.0", "4.0", "4.0"] |
| 55 | F-01 soft scores match frozen decision data | PASS | all 12 |
| 56 | F-01 per-row weighted points recompute | PASS | 81.1 |
| 57 | F-01 has one summary row | PASS | 1 |
| 58 | F-01 summary total recomputes | PASS | {"calc": 81.1, "file": "81.1"} |
| 59 | F-01 summary gate is correct | PASS | fail |
| 60 | F-01 selection status matches registry data | PASS | not_selected_component_only |
| 61 | F-01 scorecard warns totals are not evidence | PASS | The total is not evidence and does not automatically determine selection. FT-01 is selected for narrowness, substantive copy discrimination, and joint S-R/S-L/A coverage. |
| 62 | F-02 has ten hard-gate rows | PASS | 10 |
| 63 | F-02 hard-gate results match frozen data | PASS | {"HG-01": "pass", "HG-02": "pass", "HG-03": "pass", "HG-04": "pass", "HG-05": "pass", "HG-06": "pass", "HG-07": "pass", "HG-08": "pass", "HG-09": "pass", "HG-10": "fail"} |
| 64 | F-02 has twelve soft rows | PASS | 12 |
| 65 | F-02 soft weights total 100 | PASS | 100 |
| 66 | F-02 soft scores stay within 0–5 | PASS | ["3.5", "4.5", "4.0", "4.5", "4.0", "3.0", "2.5", "4.5", "4.5", "5.0", "4.0", "4.5"] |
| 67 | F-02 soft scores match frozen decision data | PASS | all 12 |
| 68 | F-02 per-row weighted points recompute | PASS | 79.9 |
| 69 | F-02 has one summary row | PASS | 1 |
| 70 | F-02 summary total recomputes | PASS | {"calc": 79.9, "file": "79.9"} |
| 71 | F-02 summary gate is correct | PASS | fail |
| 72 | F-02 selection status matches registry data | PASS | not_selected_component_only |
| 73 | F-02 scorecard warns totals are not evidence | PASS | The total is not evidence and does not automatically determine selection. FT-01 is selected for narrowness, substantive copy discrimination, and joint S-R/S-L/A coverage. |
| 74 | F-03 has ten hard-gate rows | PASS | 10 |
| 75 | F-03 hard-gate results match frozen data | PASS | {"HG-01": "pass", "HG-02": "pass", "HG-03": "pass", "HG-04": "pass", "HG-05": "pass", "HG-06": "pass", "HG-07": "pass", "HG-08": "pass", "HG-09": "pass", "HG-10": "fail"} |
| 76 | F-03 has twelve soft rows | PASS | 12 |
| 77 | F-03 soft weights total 100 | PASS | 100 |
| 78 | F-03 soft scores stay within 0–5 | PASS | ["4.5", "4.5", "3.5", "4.0", "4.0", "4.0", "2.5", "3.5", "4.0", "5.0", "4.5", "4.0"] |
| 79 | F-03 soft scores match frozen decision data | PASS | all 12 |
| 80 | F-03 per-row weighted points recompute | PASS | 78.6 |
| 81 | F-03 has one summary row | PASS | 1 |
| 82 | F-03 summary total recomputes | PASS | {"calc": 78.6, "file": "78.6"} |
| 83 | F-03 summary gate is correct | PASS | fail |
| 84 | F-03 selection status matches registry data | PASS | not_selected_component_only |
| 85 | F-03 scorecard warns totals are not evidence | PASS | The total is not evidence and does not automatically determine selection. FT-01 is selected for narrowness, substantive copy discrimination, and joint S-R/S-L/A coverage. |
| 86 | FT-01 has ten hard-gate rows | PASS | 10 |
| 87 | FT-01 hard-gate results match frozen data | PASS | {"HG-01": "pass", "HG-02": "pass", "HG-03": "pass", "HG-04": "pass", "HG-05": "pass", "HG-06": "pass", "HG-07": "pass", "HG-08": "pass", "HG-09": "pass", "HG-10": "pass"} |
| 88 | FT-01 has twelve soft rows | PASS | 12 |
| 89 | FT-01 soft weights total 100 | PASS | 100 |
| 90 | FT-01 soft scores stay within 0–5 | PASS | ["4.0", "4.5", "4.0", "4.5", "4.0", "3.0", "5.0", "4.0", "4.0", "5.0", "4.0", "4.0"] |
| 91 | FT-01 soft scores match frozen decision data | PASS | all 12 |
| 92 | FT-01 per-row weighted points recompute | PASS | 84.5 |
| 93 | FT-01 has one summary row | PASS | 1 |
| 94 | FT-01 summary total recomputes | PASS | {"calc": 84.5, "file": "84.5"} |
| 95 | FT-01 summary gate is correct | PASS | pass |
| 96 | FT-01 selection status matches registry data | PASS | PRIMARY_FROZEN |
| 97 | FT-01 scorecard warns totals are not evidence | PASS | The total is not evidence and does not automatically determine selection. FT-01 is selected for narrowness, substantive copy discrimination, and joint S-R/S-L/A coverage. |
| 98 | FT-02 has ten hard-gate rows | PASS | 10 |
| 99 | FT-02 hard-gate results match frozen data | PASS | {"HG-01": "pass", "HG-02": "pass", "HG-03": "pass", "HG-04": "pass", "HG-05": "pass", "HG-06": "pass", "HG-07": "pass", "HG-08": "pass", "HG-09": "pass", "HG-10": "pass"} |
| 100 | FT-02 has twelve soft rows | PASS | 12 |
| 101 | FT-02 soft weights total 100 | PASS | 100 |
| 102 | FT-02 soft scores stay within 0–5 | PASS | ["4.5", "4.5", "3.5", "4.0", "4.0", "4.0", "5.0", "3.5", "4.0", "5.0", "4.5", "3.5"] |
| 103 | FT-02 soft scores match frozen decision data | PASS | all 12 |
| 104 | FT-02 per-row weighted points recompute | PASS | 83.6 |
| 105 | FT-02 has one summary row | PASS | 1 |
| 106 | FT-02 summary total recomputes | PASS | {"calc": 83.6, "file": "83.6"} |
| 107 | FT-02 summary gate is correct | PASS | pass |
| 108 | FT-02 selection status matches registry data | PASS | FALLBACK_FROZEN |
| 109 | FT-02 scorecard warns totals are not evidence | PASS | The total is not evidence and does not automatically determine selection. FT-01 is selected for narrowness, substantive copy discrimination, and joint S-R/S-L/A coverage. |
| 110 | FT-03 has ten hard-gate rows | PASS | 10 |
| 111 | FT-03 hard-gate results match frozen data | PASS | {"HG-01": "pass", "HG-02": "pass", "HG-03": "pass", "HG-04": "pass", "HG-05": "pass", "HG-06": "pass", "HG-07": "pass", "HG-08": "pass", "HG-09": "pass", "HG-10": "pass"} |
| 112 | FT-03 has twelve soft rows | PASS | 12 |
| 113 | FT-03 soft weights total 100 | PASS | 100 |
| 114 | FT-03 soft scores stay within 0–5 | PASS | ["5.0", "5.0", "3.0", "4.0", "4.5", "4.0", "5.0", "2.5", "3.0", "5.0", "5.0", "2.5"] |
| 115 | FT-03 soft scores match frozen decision data | PASS | all 12 |
| 116 | FT-03 per-row weighted points recompute | PASS | 80.5 |
| 117 | FT-03 has one summary row | PASS | 1 |
| 118 | FT-03 summary total recomputes | PASS | {"calc": 80.5, "file": "80.5"} |
| 119 | FT-03 summary gate is correct | PASS | pass |
| 120 | FT-03 selection status matches registry data | PASS | DEFERRED_UNIFICATION |
| 121 | FT-03 scorecard warns totals are not evidence | PASS | The total is not evidence and does not automatically determine selection. FT-01 is selected for narrowness, substantive copy discrimination, and joint S-R/S-L/A coverage. |
| 122 | FT-NG has ten hard-gate rows | PASS | 10 |
| 123 | FT-NG hard-gate results match frozen data | PASS | {"HG-01": "pass", "HG-02": "pass", "HG-03": "pass", "HG-04": "pass", "HG-05": "pass", "HG-06": "pass", "HG-07": "pass", "HG-08": "pass", "HG-09": "pass", "HG-10": "fail"} |
| 124 | FT-NG has twelve soft rows | PASS | 12 |
| 125 | FT-NG soft weights total 100 | PASS | 100 |
| 126 | FT-NG soft scores stay within 0–5 | PASS | ["4.0", "4.0", "5.0", "3.0", "4.0", "4.0", "3.0", "5.0", "5.0", "5.0", "4.0", "5.0"] |
| 127 | FT-NG soft scores match frozen decision data | PASS | all 12 |
| 128 | FT-NG per-row weighted points recompute | PASS | 84.8 |
| 129 | FT-NG has one summary row | PASS | 1 |
| 130 | FT-NG summary total recomputes | PASS | {"calc": 84.8, "file": "84.8"} |
| 131 | FT-NG summary gate is correct | PASS | fail |
| 132 | FT-NG selection status matches registry data | PASS | MANDATORY_COMPANION_TERMINAL_FALLBACK |
| 133 | FT-NG scorecard warns totals are not evidence | PASS | The total is not evidence and does not automatically determine selection. FT-01 is selected for narrowness, substantive copy discrimination, and joint S-R/S-L/A coverage. |
| 134 | Only FT-01 is marked primary | PASS | FT-01 |
| 135 | Only FT-02 is marked fallback | PASS | FT-02 |
| 136 | FT-01 and FT-02 pass every hard gate | PASS | both |
| 137 | Standalone families fail only project-completeness HG-10 | PASS | F-01..F-03 |
| 138 | No-go kernel is retained despite failing positive-target HG-10 | PASS | MANDATORY_COMPANION_TERMINAL_FALLBACK |
| 139 | Finalist comparison explicitly distinguishes comparison from ranking | PASS | rule |
| 140 | Finalist comparison contains profile F-01 | PASS | F-01 |
| 141 | F-01 comparison records strongest case | PASS | It is the only standalone family that directly audits an integrated target-nativ |
| 142 | F-01 comparison records strongest counterexample | PASS | An autonomous package-equivalent independent twin passes S-R and A while lacking |
| 143 | F-01 comparison records unique insight | PASS | Target realization and target-native maintenance are independent of ancestry. |
| 144 | F-01 comparison records scenario advantage | PASS | S13/S28 external-decoder and delayed-collapse cases. |
| 145 | F-01 comparison records assumptions | PASS | H-SOURCE-FULL; H-PRESERVE-O; H-GLOBAL-GLUE; H-TARGET-FULL; H-AUTONOMY |
| 146 | F-01 comparison records burden | PASS | TH-04; TH-05; TH-06 plus package/gluing/autonomy toys. |
| 147 | F-01 comparison records abandonment trigger | PASS | No noncircular finite package witness or no target-owned post-withdrawal invaria |
| 148 | Finalist comparison contains profile F-02 | PASS | F-02 |
| 149 | F-02 comparison records strongest case | PASS | It gives the cleanest process-sensitive reason to distinguish gradual handoff fr |
| 150 | F-02 comparison records strongest counterexample | PASS | A source-derived destructive reconstruction may preserve every declared endpoint |
| 151 | F-02 comparison records unique insight | PASS | A continuing causal process is route/history data, not an endpoint property. |
| 152 | F-02 comparison records scenario advantage | PASS | S01/S07 gradual or prolonged overlap versus S02/S06 detached reconstruction/gap. |
| 153 | F-02 comparison records assumptions | PASS | H-LINEAGE; H-BRIDGE-ADM; H-XCI for the selected process signature; H-AUTONOMY if |
| 154 | F-02 comparison records burden | PASS | TH-07; TH-08; TH-22 and an event-graph corridor checker. |
| 155 | F-02 comparison records abandonment trigger | PASS | Every nonredundancy/process definition is verdict-loaded, or valid corridors do  |
| 156 | Finalist comparison contains profile F-03 | PASS | F-03 |
| 157 | F-03 comparison records strongest case | PASS | It handles destructive reconstruction, fission, fusion, empty targets, and indep |
| 158 | F-03 comparison records strongest counterexample | PASS | A permissive provenance seed can act as an ancestry oracle and make the least cl |
| 159 | F-03 comparison records unique insight | PASS | Cross-carrier succession may be a least relation rather than a function or equiv |
| 160 | F-03 comparison records scenario advantage | PASS | S02/S03/S05/S09/S10 destructive reconstruction, copying, fission, and fusion. |
| 161 | F-03 comparison records assumptions | PASS | Operational Seed; monotone Γ; no-ex-nihilo; H-LINEAGE; object-specific H-XCI. |
| 162 | F-03 comparison records burden | PASS | TH-01; TH-09; TH-10; TH-11 plus quotient and closure tools. |
| 163 | F-03 comparison records abandonment trigger | PASS | No operational seed excludes independent twins without already encoding successo |
| 164 | Finalist comparison contains profile FT-01 | PASS | FT-01 |
| 165 | FT-01 comparison records strongest case | PASS | It is the narrowest target that jointly establishes target package, source-deriv |
| 166 | FT-01 comparison records strongest counterexample | PASS | A destructive source-record-target reconstruction can be exact, autonomous, and  |
| 167 | FT-01 comparison records unique insight | PASS | A defensible structural precursor to 'moving' requires a target-native package p |
| 168 | FT-01 comparison records scenario advantage | PASS | Gradual replacement and live migration with a mixed nonredundant stage, contrast |
| 169 | FT-01 comparison records assumptions | PASS | D-CARRIER; H-DISTINCT; H-BRIDGE-ADM; H-SOURCE-FULL (toy stipulation); H-PRESERVE |
| 170 | FT-01 comparison records burden | PASS | TH-04/05/06/07/08 plus combined certificate and composition lemmas; TP-03/04/07/ |
| 171 | FT-01 comparison records abandonment trigger | PASS | Corridor circularity, noncomposition, absence of a nontrivial integrated target  |
| 172 | Finalist comparison contains profile FT-02 | PASS | FT-02 |
| 173 | FT-02 comparison records strongest case | PASS | It retains target realization and autonomy while allowing source-derived destruc |
| 174 | FT-02 comparison records strongest counterexample | PASS | Operational provenance may be too cheap: a record path can exist without carryin |
| 175 | FT-02 comparison records unique insight | PASS | The strongest defensible result for copying may be autonomous source-derived suc |
| 176 | FT-02 comparison records scenario advantage | PASS | Destructive reconstruction, delayed activation with declared dormancy/provenance |
| 177 | FT-02 comparison records assumptions | PASS | All SF-01 structural assumptions plus operational Seed, monotone Γ, no-ex-nihilo |
| 178 | FT-02 comparison records burden | PASS | TH-01/04/05/06/09/10/11 plus integrated successor theorem; TP-01/03/06/07/08/10. |
| 179 | FT-02 comparison records abandonment trigger | PASS | The ancestry seed is circular/universal, independent twins enter, or target pack |
| 180 | Finalist comparison contains profile FT-03 | PASS | FT-03 |
| 181 | FT-03 comparison records strongest case | PASS | It represents the live-handoff and destructive-reconstruction notions simultaneo |
| 182 | FT-03 comparison records strongest counterexample | PASS | Two independently contestable lineage criteria plus the full package may make th |
| 183 | FT-03 comparison records unique insight | PASS | There may be a hierarchy of structural continuation grades rather than one binar |
| 184 | FT-03 comparison records scenario advantage | PASS | The complete scenario atlas, especially the live/destructive split. |
| 185 | FT-03 comparison records assumptions | PASS | Union of FT-01 and FT-02 plus a theorem connecting overlap corridors to ancestry |
| 186 | FT-03 comparison records burden | PASS | Almost the whole constructive reconnaissance bank and both lineage engines. |
| 187 | FT-03 comparison records abandonment trigger | PASS | The unification theorem depends on arbitrary seed choices or prevents a bounded  |
| 188 | Finalist comparison contains profile FT-NG | PASS | FT-NG |
| 189 | FT-NG comparison records strongest case | PASS | Its symmetry, public-shadow, gluing, recombination, decoder, endpoint, route, an |
| 190 | FT-NG comparison records strongest counterexample | PASS | Each no-go can become trivial if its information boundary or criterion class is  |
| 191 | FT-NG comparison records unique insight | PASS | Many attractive transfer tests are provably insufficient even when no positive c |
| 192 | FT-NG comparison records scenario advantage | PASS | Symmetric duplication, public-perfect counterfeits, decoder dependence, local/gl |
| 193 | FT-NG comparison records assumptions | PASS | Finite typed structures and explicitly restricted observation/criterion classes  |
| 194 | FT-NG comparison records burden | PASS | TH-13/14/16/17/18/19/20/22/23 and tiny finite witnesses. |
| 195 | FT-NG comparison records abandonment trigger | PASS | The statement omits its information boundary or is defeated by an obvious comple |
| 196 | Comparison explains FIACH selection independently of decimal score | PASS | copy discriminator |
| 197 | Comparison explains IAPS fallback role | PASS | fallback |
| 198 | Comparison defers dual-lineage unification | PASS | FT-03 |
| 199 | Comparison makes no-go kernel mandatory | PASS | FT-NG |
| 200 | Primary specification contains ## 1. Motivation | PASS | ## 1. Motivation |
| 201 | Primary specification contains ## 2. Typed finite data | PASS | ## 2. Typed finite data |
| 202 | Primary specification contains ## 3. Independently defined predicates | PASS | ## 3. Independently defined predicates |
| 203 | Primary specification contains ## 4. Frozen relation | PASS | ## 4. Frozen relation |
| 204 | Primary specification contains ## 5. Core theorem family | PASS | ## 5. Core theorem family |
| 205 | Primary specification contains ## 6. Exact finite witness suite | PASS | ## 6. Exact finite witness suite |
| 206 | Primary specification contains ## 7. Toy-program contracts | PASS | ## 7. Toy-program contracts |
| 207 | Primary specification contains ## 8. Lean kernel targets | PASS | ## 8. Lean kernel targets |
| 208 | Primary specification contains ## 9. Corpus dependency map | PASS | ## 9. Corpus dependency map |
| 209 | Primary specification contains ## 10. Assumptions and claim tiers | PASS | ## 10. Assumptions and claim tiers |
| 210 | Primary specification contains ## 11. Copy and fission policy | PASS | ## 11. Copy and fission policy |
| 211 | Primary specification contains ## 12. Kill and downgrade criteria | PASS | ## 12. Kill and downgrade criteria |
| 212 | Primary specification contains ## 13. Excluded claims | PASS | ## 13. Excluded claims |
| 213 | Fallback specification contains ## 1. Motivation | PASS | ## 1. Motivation |
| 214 | Fallback specification contains ## 2. Typed finite data | PASS | ## 2. Typed finite data |
| 215 | Fallback specification contains ## 3. Frozen relation | PASS | ## 3. Frozen relation |
| 216 | Fallback specification contains ## 4. Core theorem family | PASS | ## 4. Core theorem family |
| 217 | Fallback specification contains ## 5. Exact finite witness suite | PASS | ## 5. Exact finite witness suite |
| 218 | Fallback specification contains ## 6. Toy-program contracts | PASS | ## 6. Toy-program contracts |
| 219 | Fallback specification contains ## 7. Lean kernel targets | PASS | ## 7. Lean kernel targets |
| 220 | Fallback specification contains ## 8. Assumptions and claim tiers | PASS | ## 8. Assumptions and claim tiers |
| 221 | Fallback specification contains ## 9. Copy, fission, fusion, and gap policy | PASS | ## 9. Copy, fission, fusion, and gap policy |
| 222 | Fallback specification contains ## 10. Kill and downgrade criteria | PASS | ## 10. Kill and downgrade criteria |
| 223 | Fallback specification contains ## 11. Explicit nonclaims | PASS | ## 11. Explicit nonclaims |
| 224 | Primary specification types CarrierId | PASS | CarrierId |
| 225 | Primary specification types DistinctCarrier(S,T) | PASS | DistinctCarrier(S,T) |
| 226 | Primary specification types Stage := Fin | PASS | Stage := Fin |
| 227 | Primary specification types LocalWitness | PASS | LocalWitness |
| 228 | Primary specification types LiveCorridor | PASS | LiveCorridor |
| 229 | Primary specification types Autonomous | PASS | Autonomous |
| 230 | Primary specification types FIACH_e(s,t) | PASS | FIACH_e(s,t) |
| 231 | Fallback specification types Seed | PASS | Seed |
| 232 | Fallback specification types Gamma | PASS | Gamma |
| 233 | Fallback specification types leastFixedPoint | PASS | leastFixedPoint |
| 234 | Fallback specification types Anc | PASS | Anc |
| 235 | Fallback specification types IAPS_e(s,t) | PASS | IAPS_e(s,t) |
| 236 | Fallback specification types no-ex-nihilo | PASS | no-ex-nihilo |
| 237 | Primary relation is explicitly relation-valued rather than identity | PASS | relation boundary |
| 238 | Primary detached-copy boundary is explicit | PASS | copy separation |
| 239 | Primary autonomy uses declared withdrawal | PASS | withdrawal |
| 240 | Primary requires target ownership | PASS | ownership |
| 241 | Fallback excludes independent twins through no-ex-nihilo reachability | PASS | twin exclusion |
| 242 | Fallback permits destructive structural successorship conditionally | PASS | destructive fallback |
| 243 | Fallback does not claim unique identity | PASS | uniqueness boundary |
| 244 | primary states no consciousness proof | PASS | nonclaim |
| 245 | primary states no numerical-identity proof | PASS | nonclaim |
| 246 | primary keeps A2 outside | PASS | assumption boundary |
| 247 | primary contains kill criteria | PASS | falsifier |
| 248 | fallback states no consciousness proof | PASS | nonclaim |
| 249 | fallback states no numerical-identity proof | PASS | nonclaim |
| 250 | fallback keeps A2 outside | PASS | assumption boundary |
| 251 | fallback contains kill criteria | PASS | falsifier |
| 252 | Frozen theorem family has twenty entries | PASS | 20 |
| 253 | Frozen theorem IDs are complete and unique | PASS | ["FTH-01", "FTH-02", "FTH-03", "FTH-04", "FTH-05", "FTH-06", "FTH-07", "FTH-08", "PTH-01", "PTH-02", "PTH-03", "PTH-04", "PTH-05", "PTH-06", "PTH-07", "PTH-08", "PTH-09", "PTH-10", "PTH-11", "PTH-12"] |
| 254 | Primary theorem bank has twelve entries | PASS | {"FT-01": 12, "FT-02": 8} |
| 255 | Fallback theorem bank has eight entries | PASS | {"FT-01": 12, "FT-02": 8} |
| 256 | All theorem entries remain conjecture-grade and unproved | PASS | {"conjecture_grade_not_proved": 20} |
| 257 | Theorem bank contains constructive and no-go/boundary results | PASS | {"constructive": 8, "constructive_boundary": 5, "no_go": 4, "no_go_boundary": 3} |
| 258 | PTH-01 has a nonempty exact conjecture shape | PASS | Acyclic local-witness gluing |
| 259 | PTH-01 source prospectus references resolve | PASS | ["TH-04"] |
| 260 | PTH-02 has a nonempty exact conjecture shape | PASS | Staged heterogeneous package preservation |
| 261 | PTH-02 source prospectus references resolve | PASS | ["TH-05"] |
| 262 | PTH-03 has a nonempty exact conjecture shape | PASS | Live corridor composition |
| 263 | PTH-03 source prospectus references resolve | PASS | ["TH-07"] |
| 264 | PTH-04 has a nonempty exact conjecture shape | PASS | Post-withdrawal controlled invariance |
| 265 | PTH-04 source prospectus references resolve | PASS | ["TH-06"] |
| 266 | PTH-05 has a nonempty exact conjecture shape | PASS | FIACH certificate soundness |
| 267 | PTH-05 source prospectus references resolve | PASS | ["TH-04"] |
| 268 | PTH-06 has a nonempty exact conjecture shape | PASS | FIACH composition |
| 269 | PTH-06 source prospectus references resolve | PASS | [] |
| 270 | PTH-07 has a nonempty exact conjecture shape | PASS | Relation-valued fission |
| 271 | PTH-07 source prospectus references resolve | PASS | ["TH-08", "TH-14"] |
| 272 | PTH-08 has a nonempty exact conjecture shape | PASS | Detached-copy separation |
| 273 | PTH-08 source prospectus references resolve | PASS | ["TH-22"] |
| 274 | PTH-09 has a nonempty exact conjecture shape | PASS | External-support autonomy failure |
| 275 | PTH-09 source prospectus references resolve | PASS | ["TH-17"] |
| 276 | PTH-10 has a nonempty exact conjecture shape | PASS | Local/global package obstruction |
| 277 | PTH-10 source prospectus references resolve | PASS | ["TH-20", "TH-16"] |
| 278 | PTH-11 has a nonempty exact conjecture shape | PASS | Route-memory composition boundary |
| 279 | PTH-11 source prospectus references resolve | PASS | ["TH-23"] |
| 280 | PTH-12 has a nonempty exact conjecture shape | PASS | Public-shadow insufficiency |
| 281 | PTH-12 source prospectus references resolve | PASS | ["TH-13"] |
| 282 | FTH-01 has a nonempty exact conjecture shape | PASS | Predictive quotient and bridge descent |
| 283 | FTH-01 source prospectus references resolve | PASS | ["TH-01"] |
| 284 | FTH-02 has a nonempty exact conjecture shape | PASS | Least operational ancestry relation |
| 285 | FTH-02 source prospectus references resolve | PASS | ["TH-09"] |
| 286 | FTH-03 has a nonempty exact conjecture shape | PASS | Independent-twin exclusion |
| 287 | FTH-03 source prospectus references resolve | PASS | ["TH-11"] |
| 288 | FTH-04 has a nonempty exact conjecture shape | PASS | Fission, fusion, and empty targets |
| 289 | FTH-04 source prospectus references resolve | PASS | ["TH-10", "TH-14", "TH-16"] |
| 290 | FTH-05 has a nonempty exact conjecture shape | PASS | IAPS integrated target theorem |
| 291 | FTH-05 source prospectus references resolve | PASS | ["TH-04", "TH-05", "TH-06", "TH-09"] |
| 292 | FTH-06 has a nonempty exact conjecture shape | PASS | Destructive-reconstruction/twin separation |
| 293 | FTH-06 source prospectus references resolve | PASS | ["TH-11", "TH-21"] |
| 294 | FTH-07 has a nonempty exact conjecture shape | PASS | No unique identity from ancestry |
| 295 | FTH-07 source prospectus references resolve | PASS | ["TH-14"] |
| 296 | FTH-08 has a nonempty exact conjecture shape | PASS | Predictive ancestry is package-insufficient |
| 297 | FTH-08 source prospectus references resolve | PASS | ["TH-15"] |
| 298 | Frozen witness suite has twelve entries | PASS | 12 |
| 299 | Frozen witness IDs are complete and unique | PASS | ["CW-01", "CW-02", "FW-01", "FW-02", "FW-03", "FW-04", "PW-01", "PW-02", "PW-03", "PW-04", "PW-05", "PW-06"] |
| 300 | All witness entries remain specified, not implemented | PASS | {"specified_not_implemented": 12} |
| 301 | Primary suite includes a positive and multiple controls | PASS | {"('common', 'negative')": 2, "('fallback', 'branch')": 1, "('fallback', 'fusion')": 1, "('fallback', 'negative')": 1, "('fallback', 'positive')": 1, "('primary', 'branch')": 1, "('primary', 'negative')": 3, "('primary', 'positive')": 1, "('primary', 'route')": 1} |
| 302 | Fallback suite includes a positive and independent-twin control | PASS | FW-01/FW-02 |
| 303 | PW-01 source model references resolve | PASS | ["MF-02", "MF-07", "MF-10"] |
| 304 | PW-01 states an exact purpose | PASS | Live integrated handoff |
| 305 | PW-02 source model references resolve | PASS | ["MF-03", "MF-07"] |
| 306 | PW-02 states an exact purpose | PASS | Detached exact copy |
| 307 | PW-03 source model references resolve | PASS | ["MF-07"] |
| 308 | PW-03 states an exact purpose | PASS | Decoder shadow |
| 309 | PW-04 source model references resolve | PASS | ["MF-06", "MF-07"] |
| 310 | PW-04 states an exact purpose | PASS | Local-global obstruction |
| 311 | PW-05 source model references resolve | PASS | ["MF-04"] |
| 312 | PW-05 states an exact purpose | PASS | Symmetric live fission |
| 313 | PW-06 source model references resolve | PASS | ["MF-08"] |
| 314 | PW-06 states an exact purpose | PASS | Replacement-order holonomy |
| 315 | FW-01 source model references resolve | PASS | ["MF-03", "MF-07"] |
| 316 | FW-01 states an exact purpose | PASS | Source-derived destructive successor |
| 317 | FW-02 source model references resolve | PASS | ["MF-03", "MF-05"] |
| 318 | FW-02 states an exact purpose | PASS | Independent structural twin |
| 319 | FW-03 source model references resolve | PASS | ["MF-04"] |
| 320 | FW-03 states an exact purpose | PASS | Symmetric duplication |
| 321 | FW-04 source model references resolve | PASS | ["MF-06"] |
| 322 | FW-04 states an exact purpose | PASS | Fusion with recombination conflict |
| 323 | CW-01 source model references resolve | PASS | ["MF-01", "MF-05"] |
| 324 | CW-01 states an exact purpose | PASS | Public-shadow collision |
| 325 | CW-02 source model references resolve | PASS | ["MF-09"] |
| 326 | CW-02 states an exact purpose | PASS | Scalar residual false positive |
| 327 | Target-scenario ledger has seventy rows | PASS | 70 |
| 328 | Scenario registry supplies thirty-five canonical scenarios | PASS | 35 |
| 329 | Each frozen target covers all thirty-five scenarios | PASS | {"FT-01": 35, "FT-02": 35} |
| 330 | Target-scenario keys are unique | PASS | unique |
| 331 | FT-01/S01 scenario title resolves | PASS | Gradual component-by-component replacement |
| 332 | FT-01/S01 S-T outcome ID resolves | PASS | OT-ST-03 |
| 333 | FT-01/S01 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 334 | FT-01/S01 S-R outcome ID resolves | PASS | OT-SR-05 |
| 335 | FT-01/S01 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 336 | FT-01/S01 S-L outcome ID resolves | PASS | OT-SL-03 |
| 337 | FT-01/S01 S-L lane and label match registry | PASS | {"id": "OT-SL-03", "label": "one_to_one_lineage_continuation"} |
| 338 | FT-01/S01 A outcome ID resolves | PASS | OT-A-04 |
| 339 | FT-01/S01 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 340 | FT-01/S01 R outcome ID resolves | PASS | OT-R-03 |
| 341 | FT-01/S01 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 342 | FT-01/S01 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 343 | FT-01/S01 records a lineage basis | PASS | live-corridor lineage |
| 344 | FT-01/S01 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 345 | FT-01/S02 scenario title resolves | PASS | Instantaneous destructive scan and reconstruction |
| 346 | FT-01/S02 S-T outcome ID resolves | PASS | OT-ST-01 |
| 347 | FT-01/S02 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 348 | FT-01/S02 S-R outcome ID resolves | PASS | OT-SR-05 |
| 349 | FT-01/S02 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 350 | FT-01/S02 S-L outcome ID resolves | PASS | OT-SL-01 |
| 351 | FT-01/S02 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 352 | FT-01/S02 A outcome ID resolves | PASS | OT-A-04 |
| 353 | FT-01/S02 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 354 | FT-01/S02 R outcome ID resolves | PASS | OT-R-03 |
| 355 | FT-01/S02 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 356 | FT-01/S02 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 357 | FT-01/S02 records a lineage basis | PASS | live-corridor lineage |
| 358 | FT-01/S02 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 359 | FT-01/S03 scenario title resolves | PASS | Nondestructive exact copy while source continues |
| 360 | FT-01/S03 S-T outcome ID resolves | PASS | OT-ST-01 |
| 361 | FT-01/S03 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 362 | FT-01/S03 S-R outcome ID resolves | PASS | OT-SR-02 |
| 363 | FT-01/S03 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 364 | FT-01/S03 S-L outcome ID resolves | PASS | OT-SL-01 |
| 365 | FT-01/S03 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 366 | FT-01/S03 A outcome ID resolves | PASS | OT-A-04 |
| 367 | FT-01/S03 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 368 | FT-01/S03 R outcome ID resolves | PASS | OT-R-03 |
| 369 | FT-01/S03 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 370 | FT-01/S03 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 371 | FT-01/S03 records a lineage basis | PASS | live-corridor lineage |
| 372 | FT-01/S03 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 373 | FT-01/S04 scenario title resolves | PASS | Copy first, source deletion later |
| 374 | FT-01/S04 S-T outcome ID resolves | PASS | OT-ST-01 |
| 375 | FT-01/S04 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 376 | FT-01/S04 S-R outcome ID resolves | PASS | OT-SR-02 |
| 377 | FT-01/S04 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 378 | FT-01/S04 S-L outcome ID resolves | PASS | OT-SL-01 |
| 379 | FT-01/S04 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 380 | FT-01/S04 A outcome ID resolves | PASS | OT-A-04 |
| 381 | FT-01/S04 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 382 | FT-01/S04 R outcome ID resolves | PASS | OT-R-03 |
| 383 | FT-01/S04 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 384 | FT-01/S04 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 385 | FT-01/S04 records a lineage basis | PASS | live-corridor lineage |
| 386 | FT-01/S04 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 387 | FT-01/S05 scenario title resolves | PASS | Two simultaneous exact targets |
| 388 | FT-01/S05 S-T outcome ID resolves | PASS | OT-ST-01 |
| 389 | FT-01/S05 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 390 | FT-01/S05 S-R outcome ID resolves | PASS | OT-SR-02 |
| 391 | FT-01/S05 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 392 | FT-01/S05 S-L outcome ID resolves | PASS | OT-SL-01 |
| 393 | FT-01/S05 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 394 | FT-01/S05 A outcome ID resolves | PASS | OT-A-04 |
| 395 | FT-01/S05 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 396 | FT-01/S05 R outcome ID resolves | PASS | OT-R-03 |
| 397 | FT-01/S05 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 398 | FT-01/S05 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 399 | FT-01/S05 records a lineage basis | PASS | live-corridor lineage |
| 400 | FT-01/S05 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 401 | FT-01/S06 scenario title resolves | PASS | Target activation after a temporal gap |
| 402 | FT-01/S06 S-T outcome ID resolves | PASS | OT-ST-01 |
| 403 | FT-01/S06 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 404 | FT-01/S06 S-R outcome ID resolves | PASS | OT-SR-05 |
| 405 | FT-01/S06 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 406 | FT-01/S06 S-L outcome ID resolves | PASS | OT-SL-01 |
| 407 | FT-01/S06 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 408 | FT-01/S06 A outcome ID resolves | PASS | OT-A-04 |
| 409 | FT-01/S06 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 410 | FT-01/S06 R outcome ID resolves | PASS | OT-R-03 |
| 411 | FT-01/S06 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 412 | FT-01/S06 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 413 | FT-01/S06 records a lineage basis | PASS | live-corridor lineage |
| 414 | FT-01/S06 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 415 | FT-01/S07 scenario title resolves | PASS | Long-lived source-target overlap |
| 416 | FT-01/S07 S-T outcome ID resolves | PASS | OT-ST-03 |
| 417 | FT-01/S07 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 418 | FT-01/S07 S-R outcome ID resolves | PASS | OT-SR-05 |
| 419 | FT-01/S07 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 420 | FT-01/S07 S-L outcome ID resolves | PASS | OT-SL-03 |
| 421 | FT-01/S07 S-L lane and label match registry | PASS | {"id": "OT-SL-03", "label": "one_to_one_lineage_continuation"} |
| 422 | FT-01/S07 A outcome ID resolves | PASS | OT-A-04 |
| 423 | FT-01/S07 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 424 | FT-01/S07 R outcome ID resolves | PASS | OT-R-03 |
| 425 | FT-01/S07 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 426 | FT-01/S07 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 427 | FT-01/S07 records a lineage basis | PASS | live-corridor lineage |
| 428 | FT-01/S07 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 429 | FT-01/S08 scenario title resolves | PASS | Distributed extension with no sharp handoff |
| 430 | FT-01/S08 S-T outcome ID resolves | PASS | OT-ST-04 |
| 431 | FT-01/S08 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 432 | FT-01/S08 S-R outcome ID resolves | PASS | OT-SR-05 |
| 433 | FT-01/S08 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 434 | FT-01/S08 S-L outcome ID resolves | PASS | OT-SL-07 |
| 435 | FT-01/S08 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 436 | FT-01/S08 A outcome ID resolves | PASS | OT-A-04 |
| 437 | FT-01/S08 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 438 | FT-01/S08 R outcome ID resolves | PASS | OT-R-03 |
| 439 | FT-01/S08 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 440 | FT-01/S08 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 441 | FT-01/S08 records a lineage basis | PASS | live-corridor lineage |
| 442 | FT-01/S08 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 443 | FT-01/S09 scenario title resolves | PASS | Fission followed by independent divergence |
| 444 | FT-01/S09 S-T outcome ID resolves | PASS | OT-ST-01 |
| 445 | FT-01/S09 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 446 | FT-01/S09 S-R outcome ID resolves | PASS | OT-SR-02 |
| 447 | FT-01/S09 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 448 | FT-01/S09 S-L outcome ID resolves | PASS | OT-SL-01 |
| 449 | FT-01/S09 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 450 | FT-01/S09 A outcome ID resolves | PASS | OT-A-04 |
| 451 | FT-01/S09 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 452 | FT-01/S09 R outcome ID resolves | PASS | OT-R-03 |
| 453 | FT-01/S09 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 454 | FT-01/S09 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 455 | FT-01/S09 records a lineage basis | PASS | live-corridor lineage |
| 456 | FT-01/S09 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 457 | FT-01/S10 scenario title resolves | PASS | Fission followed by later fusion |
| 458 | FT-01/S10 S-T outcome ID resolves | PASS | OT-ST-01 |
| 459 | FT-01/S10 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 460 | FT-01/S10 S-R outcome ID resolves | PASS | OT-SR-05 |
| 461 | FT-01/S10 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 462 | FT-01/S10 S-L outcome ID resolves | PASS | OT-SL-01 |
| 463 | FT-01/S10 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 464 | FT-01/S10 A outcome ID resolves | PASS | OT-A-04 |
| 465 | FT-01/S10 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 466 | FT-01/S10 R outcome ID resolves | PASS | OT-R-03 |
| 467 | FT-01/S10 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 468 | FT-01/S10 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 469 | FT-01/S10 records a lineage basis | PASS | live-corridor lineage |
| 470 | FT-01/S10 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 471 | FT-01/S11 scenario title resolves | PASS | Public-perfect copy with predictive mismatch |
| 472 | FT-01/S11 S-T outcome ID resolves | PASS | OT-ST-01 |
| 473 | FT-01/S11 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 474 | FT-01/S11 S-R outcome ID resolves | PASS | OT-SR-03 |
| 475 | FT-01/S11 S-R lane and label match registry | PASS | {"id": "OT-SR-03", "label": "public_duplicate_with_hidden_mismatch"} |
| 476 | FT-01/S11 S-L outcome ID resolves | PASS | OT-SL-01 |
| 477 | FT-01/S11 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 478 | FT-01/S11 A outcome ID resolves | PASS | OT-A-04 |
| 479 | FT-01/S11 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 480 | FT-01/S11 R outcome ID resolves | PASS | OT-R-02 |
| 481 | FT-01/S11 R lane and label match registry | PASS | {"id": "OT-R-02", "label": "indeterminate_under_declared_instruments"} |
| 482 | FT-01/S11 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 483 | FT-01/S11 records a lineage basis | PASS | live-corridor lineage |
| 484 | FT-01/S11 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 485 | FT-01/S12 scenario title resolves | PASS | Predictive match with different binding or action-credit structure |
| 486 | FT-01/S12 S-T outcome ID resolves | PASS | OT-ST-01 |
| 487 | FT-01/S12 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 488 | FT-01/S12 S-R outcome ID resolves | PASS | OT-SR-01 |
| 489 | FT-01/S12 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 490 | FT-01/S12 S-L outcome ID resolves | PASS | OT-SL-01 |
| 491 | FT-01/S12 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 492 | FT-01/S12 A outcome ID resolves | PASS | OT-A-04 |
| 493 | FT-01/S12 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 494 | FT-01/S12 R outcome ID resolves | PASS | OT-R-03 |
| 495 | FT-01/S12 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 496 | FT-01/S12 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 497 | FT-01/S12 records a lineage basis | PASS | live-corridor lineage |
| 498 | FT-01/S12 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 499 | FT-01/S13 scenario title resolves | PASS | Target maintained only by an external decoder or source process |
| 500 | FT-01/S13 S-T outcome ID resolves | PASS | OT-ST-01 |
| 501 | FT-01/S13 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 502 | FT-01/S13 S-R outcome ID resolves | PASS | OT-SR-01 |
| 503 | FT-01/S13 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 504 | FT-01/S13 S-L outcome ID resolves | PASS | OT-SL-07 |
| 505 | FT-01/S13 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 506 | FT-01/S13 A outcome ID resolves | PASS | OT-A-01 |
| 507 | FT-01/S13 A lane and label match registry | PASS | {"id": "OT-A-01", "label": "bridge_dependent_shadow"} |
| 508 | FT-01/S13 R outcome ID resolves | PASS | OT-R-02 |
| 509 | FT-01/S13 R lane and label match registry | PASS | {"id": "OT-R-02", "label": "indeterminate_under_declared_instruments"} |
| 510 | FT-01/S13 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 511 | FT-01/S13 records a lineage basis | PASS | live-corridor lineage |
| 512 | FT-01/S13 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 513 | FT-01/S14 scenario title resolves | PASS | Closed route restoring current observables but changing predictive state |
| 514 | FT-01/S14 S-T outcome ID resolves | PASS | OT-ST-01 |
| 515 | FT-01/S14 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 516 | FT-01/S14 S-R outcome ID resolves | PASS | OT-SR-05 |
| 517 | FT-01/S14 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 518 | FT-01/S14 S-L outcome ID resolves | PASS | OT-SL-01 |
| 519 | FT-01/S14 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 520 | FT-01/S14 A outcome ID resolves | PASS | OT-A-04 |
| 521 | FT-01/S14 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 522 | FT-01/S14 R outcome ID resolves | PASS | OT-R-03 |
| 523 | FT-01/S14 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 524 | FT-01/S14 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 525 | FT-01/S14 records a lineage basis | PASS | live-corridor lineage |
| 526 | FT-01/S14 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 527 | FT-01/S15 scenario title resolves | PASS | Local pairwise matches without a global package |
| 528 | FT-01/S15 S-T outcome ID resolves | PASS | OT-ST-01 |
| 529 | FT-01/S15 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 530 | FT-01/S15 S-R outcome ID resolves | PASS | OT-SR-01 |
| 531 | FT-01/S15 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 532 | FT-01/S15 S-L outcome ID resolves | PASS | OT-SL-01 |
| 533 | FT-01/S15 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 534 | FT-01/S15 A outcome ID resolves | PASS | OT-A-04 |
| 535 | FT-01/S15 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 536 | FT-01/S15 R outcome ID resolves | PASS | OT-R-03 |
| 537 | FT-01/S15 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 538 | FT-01/S15 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 539 | FT-01/S15 records a lineage basis | PASS | live-corridor lineage |
| 540 | FT-01/S15 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 541 | FT-01/S16 scenario title resolves | PASS | Residual-bounded transfer near a viability boundary |
| 542 | FT-01/S16 S-T outcome ID resolves | PASS | OT-ST-01 |
| 543 | FT-01/S16 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 544 | FT-01/S16 S-R outcome ID resolves | PASS | OT-SR-05 |
| 545 | FT-01/S16 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 546 | FT-01/S16 S-L outcome ID resolves | PASS | OT-SL-01 |
| 547 | FT-01/S16 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 548 | FT-01/S16 A outcome ID resolves | PASS | OT-A-04 |
| 549 | FT-01/S16 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 550 | FT-01/S16 R outcome ID resolves | PASS | OT-R-03 |
| 551 | FT-01/S16 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 552 | FT-01/S16 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 553 | FT-01/S16 records a lineage basis | PASS | live-corridor lineage |
| 554 | FT-01/S16 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 555 | FT-01/S17 scenario title resolves | PASS | Lossy transfer followed by endogenous repair |
| 556 | FT-01/S17 S-T outcome ID resolves | PASS | OT-ST-01 |
| 557 | FT-01/S17 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 558 | FT-01/S17 S-R outcome ID resolves | PASS | OT-SR-05 |
| 559 | FT-01/S17 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 560 | FT-01/S17 S-L outcome ID resolves | PASS | OT-SL-01 |
| 561 | FT-01/S17 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 562 | FT-01/S17 A outcome ID resolves | PASS | OT-A-04 |
| 563 | FT-01/S17 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 564 | FT-01/S17 R outcome ID resolves | PASS | OT-R-03 |
| 565 | FT-01/S17 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 566 | FT-01/S17 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 567 | FT-01/S17 records a lineage basis | PASS | live-corridor lineage |
| 568 | FT-01/S17 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 569 | FT-01/S18 scenario title resolves | PASS | Exact reversible round trip across carriers |
| 570 | FT-01/S18 S-T outcome ID resolves | PASS | OT-ST-01 |
| 571 | FT-01/S18 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 572 | FT-01/S18 S-R outcome ID resolves | PASS | OT-SR-02 |
| 573 | FT-01/S18 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 574 | FT-01/S18 S-L outcome ID resolves | PASS | OT-SL-01 |
| 575 | FT-01/S18 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 576 | FT-01/S18 A outcome ID resolves | PASS | OT-A-02 |
| 577 | FT-01/S18 A lane and label match registry | PASS | {"id": "OT-A-02", "label": "autonomous_target_realization"} |
| 578 | FT-01/S18 R outcome ID resolves | PASS | OT-R-01 |
| 579 | FT-01/S18 R lane and label match registry | PASS | {"id": "OT-R-01", "label": "determinate_under_declared_instruments"} |
| 580 | FT-01/S18 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 581 | FT-01/S18 records a lineage basis | PASS | live-corridor lineage |
| 582 | FT-01/S18 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 583 | FT-01/S19 scenario title resolves | PASS | Target with a radically rescaled clock |
| 584 | FT-01/S19 S-T outcome ID resolves | PASS | OT-ST-04 |
| 585 | FT-01/S19 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 586 | FT-01/S19 S-R outcome ID resolves | PASS | OT-SR-05 |
| 587 | FT-01/S19 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 588 | FT-01/S19 S-L outcome ID resolves | PASS | OT-SL-07 |
| 589 | FT-01/S19 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 590 | FT-01/S19 A outcome ID resolves | PASS | OT-A-04 |
| 591 | FT-01/S19 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 592 | FT-01/S19 R outcome ID resolves | PASS | OT-R-03 |
| 593 | FT-01/S19 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 594 | FT-01/S19 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 595 | FT-01/S19 records a lineage basis | PASS | live-corridor lineage |
| 596 | FT-01/S19 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 597 | FT-01/S20 scenario title resolves | PASS | Pure representation or gauge change on one carrier |
| 598 | FT-01/S20 S-T outcome ID resolves | PASS | OT-ST-05 |
| 599 | FT-01/S20 S-T lane and label match registry | PASS | {"id": "OT-ST-05", "label": "not_applicable_same_carrier"} |
| 600 | FT-01/S20 S-R outcome ID resolves | PASS | OT-SR-06 |
| 601 | FT-01/S20 S-R lane and label match registry | PASS | {"id": "OT-SR-06", "label": "target_package_not_applicable"} |
| 602 | FT-01/S20 S-L outcome ID resolves | PASS | OT-SL-08 |
| 603 | FT-01/S20 S-L lane and label match registry | PASS | {"id": "OT-SL-08", "label": "lineage_not_applicable"} |
| 604 | FT-01/S20 A outcome ID resolves | PASS | OT-A-05 |
| 605 | FT-01/S20 A lane and label match registry | PASS | {"id": "OT-A-05", "label": "autonomy_not_tested"} |
| 606 | FT-01/S20 R outcome ID resolves | PASS | OT-R-01 |
| 607 | FT-01/S20 R lane and label match registry | PASS | {"id": "OT-R-01", "label": "determinate_under_declared_instruments"} |
| 608 | FT-01/S20 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 609 | FT-01/S20 records a lineage basis | PASS | live-corridor lineage |
| 610 | FT-01/S20 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 611 | FT-01/S21 scenario title resolves | PASS | Checkpoint/restart while the source is paused |
| 612 | FT-01/S21 S-T outcome ID resolves | PASS | OT-ST-01 |
| 613 | FT-01/S21 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 614 | FT-01/S21 S-R outcome ID resolves | PASS | OT-SR-05 |
| 615 | FT-01/S21 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 616 | FT-01/S21 S-L outcome ID resolves | PASS | OT-SL-01 |
| 617 | FT-01/S21 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 618 | FT-01/S21 A outcome ID resolves | PASS | OT-A-04 |
| 619 | FT-01/S21 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 620 | FT-01/S21 R outcome ID resolves | PASS | OT-R-03 |
| 621 | FT-01/S21 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 622 | FT-01/S21 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 623 | FT-01/S21 records a lineage basis | PASS | live-corridor lineage |
| 624 | FT-01/S21 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 625 | FT-01/S22 scenario title resolves | PASS | Live migration under concurrent source updates |
| 626 | FT-01/S22 S-T outcome ID resolves | PASS | OT-ST-03 |
| 627 | FT-01/S22 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 628 | FT-01/S22 S-R outcome ID resolves | PASS | OT-SR-05 |
| 629 | FT-01/S22 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 630 | FT-01/S22 S-L outcome ID resolves | PASS | OT-SL-03 |
| 631 | FT-01/S22 S-L lane and label match registry | PASS | {"id": "OT-SL-03", "label": "one_to_one_lineage_continuation"} |
| 632 | FT-01/S22 A outcome ID resolves | PASS | OT-A-04 |
| 633 | FT-01/S22 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 634 | FT-01/S22 R outcome ID resolves | PASS | OT-R-03 |
| 635 | FT-01/S22 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 636 | FT-01/S22 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 637 | FT-01/S22 records a lineage basis | PASS | live-corridor lineage |
| 638 | FT-01/S22 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 639 | FT-01/S23 scenario title resolves | PASS | Many-source fusion into one target |
| 640 | FT-01/S23 S-T outcome ID resolves | PASS | OT-ST-01 |
| 641 | FT-01/S23 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 642 | FT-01/S23 S-R outcome ID resolves | PASS | OT-SR-05 |
| 643 | FT-01/S23 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 644 | FT-01/S23 S-L outcome ID resolves | PASS | OT-SL-01 |
| 645 | FT-01/S23 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 646 | FT-01/S23 A outcome ID resolves | PASS | OT-A-04 |
| 647 | FT-01/S23 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 648 | FT-01/S23 R outcome ID resolves | PASS | OT-R-03 |
| 649 | FT-01/S23 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 650 | FT-01/S23 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 651 | FT-01/S23 records a lineage basis | PASS | live-corridor lineage |
| 652 | FT-01/S23 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 653 | FT-01/S24 scenario title resolves | PASS | Many-to-many sharded reconfiguration |
| 654 | FT-01/S24 S-T outcome ID resolves | PASS | OT-ST-03 |
| 655 | FT-01/S24 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 656 | FT-01/S24 S-R outcome ID resolves | PASS | OT-SR-05 |
| 657 | FT-01/S24 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 658 | FT-01/S24 S-L outcome ID resolves | PASS | OT-SL-07 |
| 659 | FT-01/S24 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 660 | FT-01/S24 A outcome ID resolves | PASS | OT-A-04 |
| 661 | FT-01/S24 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 662 | FT-01/S24 R outcome ID resolves | PASS | OT-R-03 |
| 663 | FT-01/S24 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 664 | FT-01/S24 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 665 | FT-01/S24 records a lineage basis | PASS | live-corridor lineage |
| 666 | FT-01/S24 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 667 | FT-01/S25 scenario title resolves | PASS | Adaptive error-corrected migration |
| 668 | FT-01/S25 S-T outcome ID resolves | PASS | OT-ST-04 |
| 669 | FT-01/S25 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 670 | FT-01/S25 S-R outcome ID resolves | PASS | OT-SR-05 |
| 671 | FT-01/S25 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 672 | FT-01/S25 S-L outcome ID resolves | PASS | OT-SL-03 |
| 673 | FT-01/S25 S-L lane and label match registry | PASS | {"id": "OT-SL-03", "label": "one_to_one_lineage_continuation"} |
| 674 | FT-01/S25 A outcome ID resolves | PASS | OT-A-04 |
| 675 | FT-01/S25 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 676 | FT-01/S25 R outcome ID resolves | PASS | OT-R-03 |
| 677 | FT-01/S25 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 678 | FT-01/S25 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 679 | FT-01/S25 records a lineage basis | PASS | live-corridor lineage |
| 680 | FT-01/S25 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 681 | FT-01/S26 scenario title resolves | PASS | Independently built package-equivalent target |
| 682 | FT-01/S26 S-T outcome ID resolves | PASS | OT-ST-01 |
| 683 | FT-01/S26 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 684 | FT-01/S26 S-R outcome ID resolves | PASS | OT-SR-02 |
| 685 | FT-01/S26 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 686 | FT-01/S26 S-L outcome ID resolves | PASS | OT-SL-01 |
| 687 | FT-01/S26 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 688 | FT-01/S26 A outcome ID resolves | PASS | OT-A-04 |
| 689 | FT-01/S26 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 690 | FT-01/S26 R outcome ID resolves | PASS | OT-R-03 |
| 691 | FT-01/S26 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 692 | FT-01/S26 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 693 | FT-01/S26 records a lineage basis | PASS | live-corridor lineage |
| 694 | FT-01/S26 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 695 | FT-01/S27 scenario title resolves | PASS | Partial replacement around a persistent shared core |
| 696 | FT-01/S27 S-T outcome ID resolves | PASS | OT-ST-03 |
| 697 | FT-01/S27 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 698 | FT-01/S27 S-R outcome ID resolves | PASS | OT-SR-05 |
| 699 | FT-01/S27 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 700 | FT-01/S27 S-L outcome ID resolves | PASS | OT-SL-03 |
| 701 | FT-01/S27 S-L lane and label match registry | PASS | {"id": "OT-SL-03", "label": "one_to_one_lineage_continuation"} |
| 702 | FT-01/S27 A outcome ID resolves | PASS | OT-A-04 |
| 703 | FT-01/S27 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 704 | FT-01/S27 R outcome ID resolves | PASS | OT-R-03 |
| 705 | FT-01/S27 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 706 | FT-01/S27 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 707 | FT-01/S27 records a lineage basis | PASS | live-corridor lineage |
| 708 | FT-01/S27 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 709 | FT-01/S28 scenario title resolves | PASS | Bridge removal followed by delayed target collapse |
| 710 | FT-01/S28 S-T outcome ID resolves | PASS | OT-ST-01 |
| 711 | FT-01/S28 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 712 | FT-01/S28 S-R outcome ID resolves | PASS | OT-SR-02 |
| 713 | FT-01/S28 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 714 | FT-01/S28 S-L outcome ID resolves | PASS | OT-SL-03 |
| 715 | FT-01/S28 S-L lane and label match registry | PASS | {"id": "OT-SL-03", "label": "one_to_one_lineage_continuation"} |
| 716 | FT-01/S28 A outcome ID resolves | PASS | OT-A-03 |
| 717 | FT-01/S28 A lane and label match registry | PASS | {"id": "OT-A-03", "label": "autonomy_failure_after_withdrawal"} |
| 718 | FT-01/S28 R outcome ID resolves | PASS | OT-R-03 |
| 719 | FT-01/S28 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 720 | FT-01/S28 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 721 | FT-01/S28 records a lineage basis | PASS | live-corridor lineage |
| 722 | FT-01/S28 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 723 | FT-01/S29 scenario title resolves | PASS | External scheduler masquerading as temporal closure |
| 724 | FT-01/S29 S-T outcome ID resolves | PASS | OT-ST-01 |
| 725 | FT-01/S29 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 726 | FT-01/S29 S-R outcome ID resolves | PASS | OT-SR-01 |
| 727 | FT-01/S29 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 728 | FT-01/S29 S-L outcome ID resolves | PASS | OT-SL-01 |
| 729 | FT-01/S29 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 730 | FT-01/S29 A outcome ID resolves | PASS | OT-A-01 |
| 731 | FT-01/S29 A lane and label match registry | PASS | {"id": "OT-A-01", "label": "bridge_dependent_shadow"} |
| 732 | FT-01/S29 R outcome ID resolves | PASS | OT-R-02 |
| 733 | FT-01/S29 R lane and label match registry | PASS | {"id": "OT-R-02", "label": "indeterminate_under_declared_instruments"} |
| 734 | FT-01/S29 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 735 | FT-01/S29 records a lineage basis | PASS | live-corridor lineage |
| 736 | FT-01/S29 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 737 | FT-01/S30 scenario title resolves | PASS | Certificate-only migration with package mismatch |
| 738 | FT-01/S30 S-T outcome ID resolves | PASS | OT-ST-01 |
| 739 | FT-01/S30 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 740 | FT-01/S30 S-R outcome ID resolves | PASS | OT-SR-01 |
| 741 | FT-01/S30 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 742 | FT-01/S30 S-L outcome ID resolves | PASS | OT-SL-01 |
| 743 | FT-01/S30 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 744 | FT-01/S30 A outcome ID resolves | PASS | OT-A-04 |
| 745 | FT-01/S30 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 746 | FT-01/S30 R outcome ID resolves | PASS | OT-R-02 |
| 747 | FT-01/S30 R lane and label match registry | PASS | {"id": "OT-R-02", "label": "indeterminate_under_declared_instruments"} |
| 748 | FT-01/S30 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 749 | FT-01/S30 records a lineage basis | PASS | live-corridor lineage |
| 750 | FT-01/S30 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 751 | FT-01/S31 scenario title resolves | PASS | Event package assembled from locally admissible edges |
| 752 | FT-01/S31 S-T outcome ID resolves | PASS | OT-ST-01 |
| 753 | FT-01/S31 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 754 | FT-01/S31 S-R outcome ID resolves | PASS | OT-SR-01 |
| 755 | FT-01/S31 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 756 | FT-01/S31 S-L outcome ID resolves | PASS | OT-SL-01 |
| 757 | FT-01/S31 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 758 | FT-01/S31 A outcome ID resolves | PASS | OT-A-04 |
| 759 | FT-01/S31 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 760 | FT-01/S31 R outcome ID resolves | PASS | OT-R-03 |
| 761 | FT-01/S31 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 762 | FT-01/S31 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 763 | FT-01/S31 records a lineage basis | PASS | live-corridor lineage |
| 764 | FT-01/S31 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 765 | FT-01/S32 scenario title resolves | PASS | Approximately reversible round trip with accumulated residual |
| 766 | FT-01/S32 S-T outcome ID resolves | PASS | OT-ST-01 |
| 767 | FT-01/S32 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 768 | FT-01/S32 S-R outcome ID resolves | PASS | OT-SR-05 |
| 769 | FT-01/S32 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 770 | FT-01/S32 S-L outcome ID resolves | PASS | OT-SL-01 |
| 771 | FT-01/S32 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 772 | FT-01/S32 A outcome ID resolves | PASS | OT-A-04 |
| 773 | FT-01/S32 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 774 | FT-01/S32 R outcome ID resolves | PASS | OT-R-03 |
| 775 | FT-01/S32 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 776 | FT-01/S32 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 777 | FT-01/S32 records a lineage basis | PASS | live-corridor lineage |
| 778 | FT-01/S32 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 779 | FT-01/S33 scenario title resolves | PASS | Dormant backup activated after source erasure |
| 780 | FT-01/S33 S-T outcome ID resolves | PASS | OT-ST-01 |
| 781 | FT-01/S33 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 782 | FT-01/S33 S-R outcome ID resolves | PASS | OT-SR-05 |
| 783 | FT-01/S33 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 784 | FT-01/S33 S-L outcome ID resolves | PASS | OT-SL-01 |
| 785 | FT-01/S33 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 786 | FT-01/S33 A outcome ID resolves | PASS | OT-A-04 |
| 787 | FT-01/S33 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 788 | FT-01/S33 R outcome ID resolves | PASS | OT-R-03 |
| 789 | FT-01/S33 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 790 | FT-01/S33 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 791 | FT-01/S33 records a lineage basis | PASS | live-corridor lineage |
| 792 | FT-01/S33 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 793 | FT-01/S34 scenario title resolves | PASS | Overlap transfer that degrades the source |
| 794 | FT-01/S34 S-T outcome ID resolves | PASS | OT-ST-03 |
| 795 | FT-01/S34 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 796 | FT-01/S34 S-R outcome ID resolves | PASS | OT-SR-05 |
| 797 | FT-01/S34 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 798 | FT-01/S34 S-L outcome ID resolves | PASS | OT-SL-03 |
| 799 | FT-01/S34 S-L lane and label match registry | PASS | {"id": "OT-SL-03", "label": "one_to_one_lineage_continuation"} |
| 800 | FT-01/S34 A outcome ID resolves | PASS | OT-A-04 |
| 801 | FT-01/S34 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 802 | FT-01/S34 R outcome ID resolves | PASS | OT-R-03 |
| 803 | FT-01/S34 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 804 | FT-01/S34 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 805 | FT-01/S34 records a lineage basis | PASS | live-corridor lineage |
| 806 | FT-01/S34 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 807 | FT-01/S35 scenario title resolves | PASS | Replacement-order critical pair |
| 808 | FT-01/S35 S-T outcome ID resolves | PASS | OT-ST-03 |
| 809 | FT-01/S35 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 810 | FT-01/S35 S-R outcome ID resolves | PASS | OT-SR-05 |
| 811 | FT-01/S35 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 812 | FT-01/S35 S-L outcome ID resolves | PASS | OT-SL-07 |
| 813 | FT-01/S35 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 814 | FT-01/S35 A outcome ID resolves | PASS | OT-A-04 |
| 815 | FT-01/S35 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 816 | FT-01/S35 R outcome ID resolves | PASS | OT-R-03 |
| 817 | FT-01/S35 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 818 | FT-01/S35 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 819 | FT-01/S35 records a lineage basis | PASS | live-corridor lineage |
| 820 | FT-01/S35 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-03; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 821 | FT-02/S01 scenario title resolves | PASS | Gradual component-by-component replacement |
| 822 | FT-02/S01 S-T outcome ID resolves | PASS | OT-ST-03 |
| 823 | FT-02/S01 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 824 | FT-02/S01 S-R outcome ID resolves | PASS | OT-SR-05 |
| 825 | FT-02/S01 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 826 | FT-02/S01 S-L outcome ID resolves | PASS | OT-SL-02 |
| 827 | FT-02/S01 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 828 | FT-02/S01 A outcome ID resolves | PASS | OT-A-04 |
| 829 | FT-02/S01 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 830 | FT-02/S01 R outcome ID resolves | PASS | OT-R-03 |
| 831 | FT-02/S01 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 832 | FT-02/S01 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 833 | FT-02/S01 records a lineage basis | PASS | least operational predictive ancestry |
| 834 | FT-02/S01 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 835 | FT-02/S02 scenario title resolves | PASS | Instantaneous destructive scan and reconstruction |
| 836 | FT-02/S02 S-T outcome ID resolves | PASS | OT-ST-04 |
| 837 | FT-02/S02 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 838 | FT-02/S02 S-R outcome ID resolves | PASS | OT-SR-05 |
| 839 | FT-02/S02 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 840 | FT-02/S02 S-L outcome ID resolves | PASS | OT-SL-02 |
| 841 | FT-02/S02 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 842 | FT-02/S02 A outcome ID resolves | PASS | OT-A-04 |
| 843 | FT-02/S02 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 844 | FT-02/S02 R outcome ID resolves | PASS | OT-R-03 |
| 845 | FT-02/S02 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 846 | FT-02/S02 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 847 | FT-02/S02 records a lineage basis | PASS | least operational predictive ancestry |
| 848 | FT-02/S02 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 849 | FT-02/S03 scenario title resolves | PASS | Nondestructive exact copy while source continues |
| 850 | FT-02/S03 S-T outcome ID resolves | PASS | OT-ST-02 |
| 851 | FT-02/S03 S-T lane and label match registry | PASS | {"id": "OT-ST-02", "label": "structural_transport_satisfied"} |
| 852 | FT-02/S03 S-R outcome ID resolves | PASS | OT-SR-02 |
| 853 | FT-02/S03 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 854 | FT-02/S03 S-L outcome ID resolves | PASS | OT-SL-04 |
| 855 | FT-02/S03 S-L lane and label match registry | PASS | {"id": "OT-SL-04", "label": "branch_valued_continuation"} |
| 856 | FT-02/S03 A outcome ID resolves | PASS | OT-A-04 |
| 857 | FT-02/S03 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 858 | FT-02/S03 R outcome ID resolves | PASS | OT-R-03 |
| 859 | FT-02/S03 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 860 | FT-02/S03 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 861 | FT-02/S03 records a lineage basis | PASS | least operational predictive ancestry |
| 862 | FT-02/S03 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 863 | FT-02/S04 scenario title resolves | PASS | Copy first, source deletion later |
| 864 | FT-02/S04 S-T outcome ID resolves | PASS | OT-ST-02 |
| 865 | FT-02/S04 S-T lane and label match registry | PASS | {"id": "OT-ST-02", "label": "structural_transport_satisfied"} |
| 866 | FT-02/S04 S-R outcome ID resolves | PASS | OT-SR-02 |
| 867 | FT-02/S04 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 868 | FT-02/S04 S-L outcome ID resolves | PASS | OT-SL-04 |
| 869 | FT-02/S04 S-L lane and label match registry | PASS | {"id": "OT-SL-04", "label": "branch_valued_continuation"} |
| 870 | FT-02/S04 A outcome ID resolves | PASS | OT-A-04 |
| 871 | FT-02/S04 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 872 | FT-02/S04 R outcome ID resolves | PASS | OT-R-03 |
| 873 | FT-02/S04 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 874 | FT-02/S04 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 875 | FT-02/S04 records a lineage basis | PASS | least operational predictive ancestry |
| 876 | FT-02/S04 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 877 | FT-02/S05 scenario title resolves | PASS | Two simultaneous exact targets |
| 878 | FT-02/S05 S-T outcome ID resolves | PASS | OT-ST-02 |
| 879 | FT-02/S05 S-T lane and label match registry | PASS | {"id": "OT-ST-02", "label": "structural_transport_satisfied"} |
| 880 | FT-02/S05 S-R outcome ID resolves | PASS | OT-SR-02 |
| 881 | FT-02/S05 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 882 | FT-02/S05 S-L outcome ID resolves | PASS | OT-SL-04 |
| 883 | FT-02/S05 S-L lane and label match registry | PASS | {"id": "OT-SL-04", "label": "branch_valued_continuation"} |
| 884 | FT-02/S05 A outcome ID resolves | PASS | OT-A-04 |
| 885 | FT-02/S05 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 886 | FT-02/S05 R outcome ID resolves | PASS | OT-R-03 |
| 887 | FT-02/S05 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 888 | FT-02/S05 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 889 | FT-02/S05 records a lineage basis | PASS | least operational predictive ancestry |
| 890 | FT-02/S05 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 891 | FT-02/S06 scenario title resolves | PASS | Target activation after a temporal gap |
| 892 | FT-02/S06 S-T outcome ID resolves | PASS | OT-ST-04 |
| 893 | FT-02/S06 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 894 | FT-02/S06 S-R outcome ID resolves | PASS | OT-SR-05 |
| 895 | FT-02/S06 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 896 | FT-02/S06 S-L outcome ID resolves | PASS | OT-SL-02 |
| 897 | FT-02/S06 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 898 | FT-02/S06 A outcome ID resolves | PASS | OT-A-04 |
| 899 | FT-02/S06 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 900 | FT-02/S06 R outcome ID resolves | PASS | OT-R-03 |
| 901 | FT-02/S06 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 902 | FT-02/S06 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 903 | FT-02/S06 records a lineage basis | PASS | least operational predictive ancestry |
| 904 | FT-02/S06 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 905 | FT-02/S07 scenario title resolves | PASS | Long-lived source-target overlap |
| 906 | FT-02/S07 S-T outcome ID resolves | PASS | OT-ST-03 |
| 907 | FT-02/S07 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 908 | FT-02/S07 S-R outcome ID resolves | PASS | OT-SR-05 |
| 909 | FT-02/S07 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 910 | FT-02/S07 S-L outcome ID resolves | PASS | OT-SL-02 |
| 911 | FT-02/S07 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 912 | FT-02/S07 A outcome ID resolves | PASS | OT-A-04 |
| 913 | FT-02/S07 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 914 | FT-02/S07 R outcome ID resolves | PASS | OT-R-03 |
| 915 | FT-02/S07 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 916 | FT-02/S07 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 917 | FT-02/S07 records a lineage basis | PASS | least operational predictive ancestry |
| 918 | FT-02/S07 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 919 | FT-02/S08 scenario title resolves | PASS | Distributed extension with no sharp handoff |
| 920 | FT-02/S08 S-T outcome ID resolves | PASS | OT-ST-04 |
| 921 | FT-02/S08 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 922 | FT-02/S08 S-R outcome ID resolves | PASS | OT-SR-05 |
| 923 | FT-02/S08 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 924 | FT-02/S08 S-L outcome ID resolves | PASS | OT-SL-07 |
| 925 | FT-02/S08 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 926 | FT-02/S08 A outcome ID resolves | PASS | OT-A-04 |
| 927 | FT-02/S08 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 928 | FT-02/S08 R outcome ID resolves | PASS | OT-R-03 |
| 929 | FT-02/S08 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 930 | FT-02/S08 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 931 | FT-02/S08 records a lineage basis | PASS | least operational predictive ancestry |
| 932 | FT-02/S08 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 933 | FT-02/S09 scenario title resolves | PASS | Fission followed by independent divergence |
| 934 | FT-02/S09 S-T outcome ID resolves | PASS | OT-ST-02 |
| 935 | FT-02/S09 S-T lane and label match registry | PASS | {"id": "OT-ST-02", "label": "structural_transport_satisfied"} |
| 936 | FT-02/S09 S-R outcome ID resolves | PASS | OT-SR-02 |
| 937 | FT-02/S09 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 938 | FT-02/S09 S-L outcome ID resolves | PASS | OT-SL-04 |
| 939 | FT-02/S09 S-L lane and label match registry | PASS | {"id": "OT-SL-04", "label": "branch_valued_continuation"} |
| 940 | FT-02/S09 A outcome ID resolves | PASS | OT-A-04 |
| 941 | FT-02/S09 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 942 | FT-02/S09 R outcome ID resolves | PASS | OT-R-03 |
| 943 | FT-02/S09 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 944 | FT-02/S09 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 945 | FT-02/S09 records a lineage basis | PASS | least operational predictive ancestry |
| 946 | FT-02/S09 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 947 | FT-02/S10 scenario title resolves | PASS | Fission followed by later fusion |
| 948 | FT-02/S10 S-T outcome ID resolves | PASS | OT-ST-03 |
| 949 | FT-02/S10 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 950 | FT-02/S10 S-R outcome ID resolves | PASS | OT-SR-05 |
| 951 | FT-02/S10 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 952 | FT-02/S10 S-L outcome ID resolves | PASS | OT-SL-05 |
| 953 | FT-02/S10 S-L lane and label match registry | PASS | {"id": "OT-SL-05", "label": "fusion_valued_continuation"} |
| 954 | FT-02/S10 A outcome ID resolves | PASS | OT-A-04 |
| 955 | FT-02/S10 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 956 | FT-02/S10 R outcome ID resolves | PASS | OT-R-03 |
| 957 | FT-02/S10 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 958 | FT-02/S10 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 959 | FT-02/S10 records a lineage basis | PASS | least operational predictive ancestry |
| 960 | FT-02/S10 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 961 | FT-02/S11 scenario title resolves | PASS | Public-perfect copy with predictive mismatch |
| 962 | FT-02/S11 S-T outcome ID resolves | PASS | OT-ST-01 |
| 963 | FT-02/S11 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 964 | FT-02/S11 S-R outcome ID resolves | PASS | OT-SR-03 |
| 965 | FT-02/S11 S-R lane and label match registry | PASS | {"id": "OT-SR-03", "label": "public_duplicate_with_hidden_mismatch"} |
| 966 | FT-02/S11 S-L outcome ID resolves | PASS | OT-SL-01 |
| 967 | FT-02/S11 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 968 | FT-02/S11 A outcome ID resolves | PASS | OT-A-04 |
| 969 | FT-02/S11 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 970 | FT-02/S11 R outcome ID resolves | PASS | OT-R-02 |
| 971 | FT-02/S11 R lane and label match registry | PASS | {"id": "OT-R-02", "label": "indeterminate_under_declared_instruments"} |
| 972 | FT-02/S11 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 973 | FT-02/S11 records a lineage basis | PASS | least operational predictive ancestry |
| 974 | FT-02/S11 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 975 | FT-02/S12 scenario title resolves | PASS | Predictive match with different binding or action-credit structure |
| 976 | FT-02/S12 S-T outcome ID resolves | PASS | OT-ST-01 |
| 977 | FT-02/S12 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 978 | FT-02/S12 S-R outcome ID resolves | PASS | OT-SR-01 |
| 979 | FT-02/S12 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 980 | FT-02/S12 S-L outcome ID resolves | PASS | OT-SL-04 |
| 981 | FT-02/S12 S-L lane and label match registry | PASS | {"id": "OT-SL-04", "label": "branch_valued_continuation"} |
| 982 | FT-02/S12 A outcome ID resolves | PASS | OT-A-04 |
| 983 | FT-02/S12 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 984 | FT-02/S12 R outcome ID resolves | PASS | OT-R-03 |
| 985 | FT-02/S12 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 986 | FT-02/S12 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 987 | FT-02/S12 records a lineage basis | PASS | least operational predictive ancestry |
| 988 | FT-02/S12 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 989 | FT-02/S13 scenario title resolves | PASS | Target maintained only by an external decoder or source process |
| 990 | FT-02/S13 S-T outcome ID resolves | PASS | OT-ST-01 |
| 991 | FT-02/S13 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 992 | FT-02/S13 S-R outcome ID resolves | PASS | OT-SR-01 |
| 993 | FT-02/S13 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 994 | FT-02/S13 S-L outcome ID resolves | PASS | OT-SL-02 |
| 995 | FT-02/S13 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 996 | FT-02/S13 A outcome ID resolves | PASS | OT-A-01 |
| 997 | FT-02/S13 A lane and label match registry | PASS | {"id": "OT-A-01", "label": "bridge_dependent_shadow"} |
| 998 | FT-02/S13 R outcome ID resolves | PASS | OT-R-03 |
| 999 | FT-02/S13 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1000 | FT-02/S13 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1001 | FT-02/S13 records a lineage basis | PASS | least operational predictive ancestry |
| 1002 | FT-02/S13 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1003 | FT-02/S14 scenario title resolves | PASS | Closed route restoring current observables but changing predictive state |
| 1004 | FT-02/S14 S-T outcome ID resolves | PASS | OT-ST-03 |
| 1005 | FT-02/S14 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 1006 | FT-02/S14 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1007 | FT-02/S14 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1008 | FT-02/S14 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1009 | FT-02/S14 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1010 | FT-02/S14 A outcome ID resolves | PASS | OT-A-04 |
| 1011 | FT-02/S14 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1012 | FT-02/S14 R outcome ID resolves | PASS | OT-R-03 |
| 1013 | FT-02/S14 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1014 | FT-02/S14 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1015 | FT-02/S14 records a lineage basis | PASS | least operational predictive ancestry |
| 1016 | FT-02/S14 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1017 | FT-02/S15 scenario title resolves | PASS | Local pairwise matches without a global package |
| 1018 | FT-02/S15 S-T outcome ID resolves | PASS | OT-ST-01 |
| 1019 | FT-02/S15 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 1020 | FT-02/S15 S-R outcome ID resolves | PASS | OT-SR-01 |
| 1021 | FT-02/S15 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 1022 | FT-02/S15 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1023 | FT-02/S15 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1024 | FT-02/S15 A outcome ID resolves | PASS | OT-A-04 |
| 1025 | FT-02/S15 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1026 | FT-02/S15 R outcome ID resolves | PASS | OT-R-02 |
| 1027 | FT-02/S15 R lane and label match registry | PASS | {"id": "OT-R-02", "label": "indeterminate_under_declared_instruments"} |
| 1028 | FT-02/S15 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1029 | FT-02/S15 records a lineage basis | PASS | least operational predictive ancestry |
| 1030 | FT-02/S15 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1031 | FT-02/S16 scenario title resolves | PASS | Residual-bounded transfer near a viability boundary |
| 1032 | FT-02/S16 S-T outcome ID resolves | PASS | OT-ST-04 |
| 1033 | FT-02/S16 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 1034 | FT-02/S16 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1035 | FT-02/S16 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1036 | FT-02/S16 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1037 | FT-02/S16 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1038 | FT-02/S16 A outcome ID resolves | PASS | OT-A-04 |
| 1039 | FT-02/S16 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1040 | FT-02/S16 R outcome ID resolves | PASS | OT-R-03 |
| 1041 | FT-02/S16 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1042 | FT-02/S16 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1043 | FT-02/S16 records a lineage basis | PASS | least operational predictive ancestry |
| 1044 | FT-02/S16 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1045 | FT-02/S17 scenario title resolves | PASS | Lossy transfer followed by endogenous repair |
| 1046 | FT-02/S17 S-T outcome ID resolves | PASS | OT-ST-04 |
| 1047 | FT-02/S17 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 1048 | FT-02/S17 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1049 | FT-02/S17 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1050 | FT-02/S17 S-L outcome ID resolves | PASS | OT-SL-02 |
| 1051 | FT-02/S17 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 1052 | FT-02/S17 A outcome ID resolves | PASS | OT-A-04 |
| 1053 | FT-02/S17 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1054 | FT-02/S17 R outcome ID resolves | PASS | OT-R-03 |
| 1055 | FT-02/S17 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1056 | FT-02/S17 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1057 | FT-02/S17 records a lineage basis | PASS | least operational predictive ancestry |
| 1058 | FT-02/S17 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1059 | FT-02/S18 scenario title resolves | PASS | Exact reversible round trip across carriers |
| 1060 | FT-02/S18 S-T outcome ID resolves | PASS | OT-ST-02 |
| 1061 | FT-02/S18 S-T lane and label match registry | PASS | {"id": "OT-ST-02", "label": "structural_transport_satisfied"} |
| 1062 | FT-02/S18 S-R outcome ID resolves | PASS | OT-SR-02 |
| 1063 | FT-02/S18 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 1064 | FT-02/S18 S-L outcome ID resolves | PASS | OT-SL-03 |
| 1065 | FT-02/S18 S-L lane and label match registry | PASS | {"id": "OT-SL-03", "label": "one_to_one_lineage_continuation"} |
| 1066 | FT-02/S18 A outcome ID resolves | PASS | OT-A-02 |
| 1067 | FT-02/S18 A lane and label match registry | PASS | {"id": "OT-A-02", "label": "autonomous_target_realization"} |
| 1068 | FT-02/S18 R outcome ID resolves | PASS | OT-R-01 |
| 1069 | FT-02/S18 R lane and label match registry | PASS | {"id": "OT-R-01", "label": "determinate_under_declared_instruments"} |
| 1070 | FT-02/S18 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1071 | FT-02/S18 records a lineage basis | PASS | least operational predictive ancestry |
| 1072 | FT-02/S18 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1073 | FT-02/S19 scenario title resolves | PASS | Target with a radically rescaled clock |
| 1074 | FT-02/S19 S-T outcome ID resolves | PASS | OT-ST-04 |
| 1075 | FT-02/S19 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 1076 | FT-02/S19 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1077 | FT-02/S19 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1078 | FT-02/S19 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1079 | FT-02/S19 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1080 | FT-02/S19 A outcome ID resolves | PASS | OT-A-04 |
| 1081 | FT-02/S19 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1082 | FT-02/S19 R outcome ID resolves | PASS | OT-R-03 |
| 1083 | FT-02/S19 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1084 | FT-02/S19 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1085 | FT-02/S19 records a lineage basis | PASS | least operational predictive ancestry |
| 1086 | FT-02/S19 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1087 | FT-02/S20 scenario title resolves | PASS | Pure representation or gauge change on one carrier |
| 1088 | FT-02/S20 S-T outcome ID resolves | PASS | OT-ST-05 |
| 1089 | FT-02/S20 S-T lane and label match registry | PASS | {"id": "OT-ST-05", "label": "not_applicable_same_carrier"} |
| 1090 | FT-02/S20 S-R outcome ID resolves | PASS | OT-SR-06 |
| 1091 | FT-02/S20 S-R lane and label match registry | PASS | {"id": "OT-SR-06", "label": "target_package_not_applicable"} |
| 1092 | FT-02/S20 S-L outcome ID resolves | PASS | OT-SL-08 |
| 1093 | FT-02/S20 S-L lane and label match registry | PASS | {"id": "OT-SL-08", "label": "lineage_not_applicable"} |
| 1094 | FT-02/S20 A outcome ID resolves | PASS | OT-A-05 |
| 1095 | FT-02/S20 A lane and label match registry | PASS | {"id": "OT-A-05", "label": "autonomy_not_tested"} |
| 1096 | FT-02/S20 R outcome ID resolves | PASS | OT-R-01 |
| 1097 | FT-02/S20 R lane and label match registry | PASS | {"id": "OT-R-01", "label": "determinate_under_declared_instruments"} |
| 1098 | FT-02/S20 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1099 | FT-02/S20 records a lineage basis | PASS | least operational predictive ancestry |
| 1100 | FT-02/S20 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1101 | FT-02/S21 scenario title resolves | PASS | Checkpoint/restart while the source is paused |
| 1102 | FT-02/S21 S-T outcome ID resolves | PASS | OT-ST-04 |
| 1103 | FT-02/S21 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 1104 | FT-02/S21 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1105 | FT-02/S21 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1106 | FT-02/S21 S-L outcome ID resolves | PASS | OT-SL-04 |
| 1107 | FT-02/S21 S-L lane and label match registry | PASS | {"id": "OT-SL-04", "label": "branch_valued_continuation"} |
| 1108 | FT-02/S21 A outcome ID resolves | PASS | OT-A-04 |
| 1109 | FT-02/S21 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1110 | FT-02/S21 R outcome ID resolves | PASS | OT-R-03 |
| 1111 | FT-02/S21 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1112 | FT-02/S21 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1113 | FT-02/S21 records a lineage basis | PASS | least operational predictive ancestry |
| 1114 | FT-02/S21 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1115 | FT-02/S22 scenario title resolves | PASS | Live migration under concurrent source updates |
| 1116 | FT-02/S22 S-T outcome ID resolves | PASS | OT-ST-03 |
| 1117 | FT-02/S22 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 1118 | FT-02/S22 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1119 | FT-02/S22 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1120 | FT-02/S22 S-L outcome ID resolves | PASS | OT-SL-02 |
| 1121 | FT-02/S22 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 1122 | FT-02/S22 A outcome ID resolves | PASS | OT-A-04 |
| 1123 | FT-02/S22 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1124 | FT-02/S22 R outcome ID resolves | PASS | OT-R-03 |
| 1125 | FT-02/S22 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1126 | FT-02/S22 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1127 | FT-02/S22 records a lineage basis | PASS | least operational predictive ancestry |
| 1128 | FT-02/S22 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1129 | FT-02/S23 scenario title resolves | PASS | Many-source fusion into one target |
| 1130 | FT-02/S23 S-T outcome ID resolves | PASS | OT-ST-04 |
| 1131 | FT-02/S23 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 1132 | FT-02/S23 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1133 | FT-02/S23 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1134 | FT-02/S23 S-L outcome ID resolves | PASS | OT-SL-05 |
| 1135 | FT-02/S23 S-L lane and label match registry | PASS | {"id": "OT-SL-05", "label": "fusion_valued_continuation"} |
| 1136 | FT-02/S23 A outcome ID resolves | PASS | OT-A-04 |
| 1137 | FT-02/S23 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1138 | FT-02/S23 R outcome ID resolves | PASS | OT-R-03 |
| 1139 | FT-02/S23 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1140 | FT-02/S23 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1141 | FT-02/S23 records a lineage basis | PASS | least operational predictive ancestry |
| 1142 | FT-02/S23 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1143 | FT-02/S24 scenario title resolves | PASS | Many-to-many sharded reconfiguration |
| 1144 | FT-02/S24 S-T outcome ID resolves | PASS | OT-ST-03 |
| 1145 | FT-02/S24 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 1146 | FT-02/S24 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1147 | FT-02/S24 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1148 | FT-02/S24 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1149 | FT-02/S24 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1150 | FT-02/S24 A outcome ID resolves | PASS | OT-A-04 |
| 1151 | FT-02/S24 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1152 | FT-02/S24 R outcome ID resolves | PASS | OT-R-03 |
| 1153 | FT-02/S24 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1154 | FT-02/S24 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1155 | FT-02/S24 records a lineage basis | PASS | least operational predictive ancestry |
| 1156 | FT-02/S24 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1157 | FT-02/S25 scenario title resolves | PASS | Adaptive error-corrected migration |
| 1158 | FT-02/S25 S-T outcome ID resolves | PASS | OT-ST-04 |
| 1159 | FT-02/S25 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 1160 | FT-02/S25 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1161 | FT-02/S25 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1162 | FT-02/S25 S-L outcome ID resolves | PASS | OT-SL-03 |
| 1163 | FT-02/S25 S-L lane and label match registry | PASS | {"id": "OT-SL-03", "label": "one_to_one_lineage_continuation"} |
| 1164 | FT-02/S25 A outcome ID resolves | PASS | OT-A-04 |
| 1165 | FT-02/S25 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1166 | FT-02/S25 R outcome ID resolves | PASS | OT-R-03 |
| 1167 | FT-02/S25 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1168 | FT-02/S25 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1169 | FT-02/S25 records a lineage basis | PASS | least operational predictive ancestry |
| 1170 | FT-02/S25 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1171 | FT-02/S26 scenario title resolves | PASS | Independently built package-equivalent target |
| 1172 | FT-02/S26 S-T outcome ID resolves | PASS | OT-ST-01 |
| 1173 | FT-02/S26 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 1174 | FT-02/S26 S-R outcome ID resolves | PASS | OT-SR-02 |
| 1175 | FT-02/S26 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 1176 | FT-02/S26 S-L outcome ID resolves | PASS | OT-SL-01 |
| 1177 | FT-02/S26 S-L lane and label match registry | PASS | {"id": "OT-SL-01", "label": "no_declared_lineage_reaches_target"} |
| 1178 | FT-02/S26 A outcome ID resolves | PASS | OT-A-04 |
| 1179 | FT-02/S26 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1180 | FT-02/S26 R outcome ID resolves | PASS | OT-R-03 |
| 1181 | FT-02/S26 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1182 | FT-02/S26 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1183 | FT-02/S26 records a lineage basis | PASS | least operational predictive ancestry |
| 1184 | FT-02/S26 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1185 | FT-02/S27 scenario title resolves | PASS | Partial replacement around a persistent shared core |
| 1186 | FT-02/S27 S-T outcome ID resolves | PASS | OT-ST-03 |
| 1187 | FT-02/S27 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 1188 | FT-02/S27 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1189 | FT-02/S27 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1190 | FT-02/S27 S-L outcome ID resolves | PASS | OT-SL-02 |
| 1191 | FT-02/S27 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 1192 | FT-02/S27 A outcome ID resolves | PASS | OT-A-04 |
| 1193 | FT-02/S27 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1194 | FT-02/S27 R outcome ID resolves | PASS | OT-R-03 |
| 1195 | FT-02/S27 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1196 | FT-02/S27 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1197 | FT-02/S27 records a lineage basis | PASS | least operational predictive ancestry |
| 1198 | FT-02/S27 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1199 | FT-02/S28 scenario title resolves | PASS | Bridge removal followed by delayed target collapse |
| 1200 | FT-02/S28 S-T outcome ID resolves | PASS | OT-ST-01 |
| 1201 | FT-02/S28 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 1202 | FT-02/S28 S-R outcome ID resolves | PASS | OT-SR-02 |
| 1203 | FT-02/S28 S-R lane and label match registry | PASS | {"id": "OT-SR-02", "label": "target_package_exists"} |
| 1204 | FT-02/S28 S-L outcome ID resolves | PASS | OT-SL-02 |
| 1205 | FT-02/S28 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 1206 | FT-02/S28 A outcome ID resolves | PASS | OT-A-03 |
| 1207 | FT-02/S28 A lane and label match registry | PASS | {"id": "OT-A-03", "label": "autonomy_failure_after_withdrawal"} |
| 1208 | FT-02/S28 R outcome ID resolves | PASS | OT-R-03 |
| 1209 | FT-02/S28 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1210 | FT-02/S28 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1211 | FT-02/S28 records a lineage basis | PASS | least operational predictive ancestry |
| 1212 | FT-02/S28 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1213 | FT-02/S29 scenario title resolves | PASS | External scheduler masquerading as temporal closure |
| 1214 | FT-02/S29 S-T outcome ID resolves | PASS | OT-ST-01 |
| 1215 | FT-02/S29 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 1216 | FT-02/S29 S-R outcome ID resolves | PASS | OT-SR-01 |
| 1217 | FT-02/S29 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 1218 | FT-02/S29 S-L outcome ID resolves | PASS | OT-SL-02 |
| 1219 | FT-02/S29 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 1220 | FT-02/S29 A outcome ID resolves | PASS | OT-A-01 |
| 1221 | FT-02/S29 A lane and label match registry | PASS | {"id": "OT-A-01", "label": "bridge_dependent_shadow"} |
| 1222 | FT-02/S29 R outcome ID resolves | PASS | OT-R-03 |
| 1223 | FT-02/S29 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1224 | FT-02/S29 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1225 | FT-02/S29 records a lineage basis | PASS | least operational predictive ancestry |
| 1226 | FT-02/S29 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1227 | FT-02/S30 scenario title resolves | PASS | Certificate-only migration with package mismatch |
| 1228 | FT-02/S30 S-T outcome ID resolves | PASS | OT-ST-01 |
| 1229 | FT-02/S30 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 1230 | FT-02/S30 S-R outcome ID resolves | PASS | OT-SR-01 |
| 1231 | FT-02/S30 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 1232 | FT-02/S30 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1233 | FT-02/S30 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1234 | FT-02/S30 A outcome ID resolves | PASS | OT-A-04 |
| 1235 | FT-02/S30 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1236 | FT-02/S30 R outcome ID resolves | PASS | OT-R-02 |
| 1237 | FT-02/S30 R lane and label match registry | PASS | {"id": "OT-R-02", "label": "indeterminate_under_declared_instruments"} |
| 1238 | FT-02/S30 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1239 | FT-02/S30 records a lineage basis | PASS | least operational predictive ancestry |
| 1240 | FT-02/S30 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1241 | FT-02/S31 scenario title resolves | PASS | Event package assembled from locally admissible edges |
| 1242 | FT-02/S31 S-T outcome ID resolves | PASS | OT-ST-01 |
| 1243 | FT-02/S31 S-T lane and label match registry | PASS | {"id": "OT-ST-01", "label": "no_transport"} |
| 1244 | FT-02/S31 S-R outcome ID resolves | PASS | OT-SR-01 |
| 1245 | FT-02/S31 S-R lane and label match registry | PASS | {"id": "OT-SR-01", "label": "no_valid_target_package"} |
| 1246 | FT-02/S31 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1247 | FT-02/S31 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1248 | FT-02/S31 A outcome ID resolves | PASS | OT-A-04 |
| 1249 | FT-02/S31 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1250 | FT-02/S31 R outcome ID resolves | PASS | OT-R-02 |
| 1251 | FT-02/S31 R lane and label match registry | PASS | {"id": "OT-R-02", "label": "indeterminate_under_declared_instruments"} |
| 1252 | FT-02/S31 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1253 | FT-02/S31 records a lineage basis | PASS | least operational predictive ancestry |
| 1254 | FT-02/S31 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1255 | FT-02/S32 scenario title resolves | PASS | Approximately reversible round trip with accumulated residual |
| 1256 | FT-02/S32 S-T outcome ID resolves | PASS | OT-ST-03 |
| 1257 | FT-02/S32 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 1258 | FT-02/S32 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1259 | FT-02/S32 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1260 | FT-02/S32 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1261 | FT-02/S32 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1262 | FT-02/S32 A outcome ID resolves | PASS | OT-A-04 |
| 1263 | FT-02/S32 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1264 | FT-02/S32 R outcome ID resolves | PASS | OT-R-03 |
| 1265 | FT-02/S32 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1266 | FT-02/S32 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1267 | FT-02/S32 records a lineage basis | PASS | least operational predictive ancestry |
| 1268 | FT-02/S32 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1269 | FT-02/S33 scenario title resolves | PASS | Dormant backup activated after source erasure |
| 1270 | FT-02/S33 S-T outcome ID resolves | PASS | OT-ST-04 |
| 1271 | FT-02/S33 S-T lane and label match registry | PASS | {"id": "OT-ST-04", "label": "transport_underdetermined"} |
| 1272 | FT-02/S33 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1273 | FT-02/S33 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1274 | FT-02/S33 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1275 | FT-02/S33 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1276 | FT-02/S33 A outcome ID resolves | PASS | OT-A-04 |
| 1277 | FT-02/S33 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1278 | FT-02/S33 R outcome ID resolves | PASS | OT-R-03 |
| 1279 | FT-02/S33 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1280 | FT-02/S33 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1281 | FT-02/S33 records a lineage basis | PASS | least operational predictive ancestry |
| 1282 | FT-02/S33 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1283 | FT-02/S34 scenario title resolves | PASS | Overlap transfer that degrades the source |
| 1284 | FT-02/S34 S-T outcome ID resolves | PASS | OT-ST-03 |
| 1285 | FT-02/S34 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 1286 | FT-02/S34 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1287 | FT-02/S34 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1288 | FT-02/S34 S-L outcome ID resolves | PASS | OT-SL-02 |
| 1289 | FT-02/S34 S-L lane and label match registry | PASS | {"id": "OT-SL-02", "label": "structural_successor"} |
| 1290 | FT-02/S34 A outcome ID resolves | PASS | OT-A-04 |
| 1291 | FT-02/S34 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1292 | FT-02/S34 R outcome ID resolves | PASS | OT-R-03 |
| 1293 | FT-02/S34 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1294 | FT-02/S34 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1295 | FT-02/S34 records a lineage basis | PASS | least operational predictive ancestry |
| 1296 | FT-02/S34 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1297 | FT-02/S35 scenario title resolves | PASS | Replacement-order critical pair |
| 1298 | FT-02/S35 S-T outcome ID resolves | PASS | OT-ST-03 |
| 1299 | FT-02/S35 S-T lane and label match registry | PASS | {"id": "OT-ST-03", "label": "route_dependent_transport"} |
| 1300 | FT-02/S35 S-R outcome ID resolves | PASS | OT-SR-05 |
| 1301 | FT-02/S35 S-R lane and label match registry | PASS | {"id": "OT-SR-05", "label": "target_package_underdetermined"} |
| 1302 | FT-02/S35 S-L outcome ID resolves | PASS | OT-SL-07 |
| 1303 | FT-02/S35 S-L lane and label match registry | PASS | {"id": "OT-SL-07", "label": "lineage_underdetermined"} |
| 1304 | FT-02/S35 A outcome ID resolves | PASS | OT-A-04 |
| 1305 | FT-02/S35 A lane and label match registry | PASS | {"id": "OT-A-04", "label": "autonomy_underdetermined"} |
| 1306 | FT-02/S35 R outcome ID resolves | PASS | OT-R-03 |
| 1307 | FT-02/S35 R lane and label match registry | PASS | {"id": "OT-R-03", "label": "instrument_not_supplied"} |
| 1308 | FT-02/S35 remains an expected nonempirical verdict | PASS | frozen_expected_verdict_not_empirical_result |
| 1309 | FT-02/S35 records a lineage basis | PASS | least operational predictive ancestry |
| 1310 | FT-02/S35 records a derivation basis | PASS | S-R/A inherited from TS-02; S-L inherited from TS-10; S-T is conservative conjunction; R is the weaker supplied instrument status. |
| 1311 | Joint-status counts match frozen criterion-relative ledger | PASS | {"('FT-01', 'joint_target_fails_on_declared_facts')": 24, "('FT-01', 'joint_target_underdetermined_pending_candidate_specific_witnesses')": 10, "('FT-01', 'not_applicable_same_carrier')": 1, "('FT-02', 'joint_target_fails_on_declared_facts')": 9, "('FT-02', 'joint_target_satisfied_at_declared_scope')": 1, "('FT-02', 'joint_target_underdetermined_pending_candidate_specific_witnesses')": 24, "('FT-02', 'not_applicable_same_carrier')": 1} |
| 1312 | FIACH rejects instantaneous destructive reconstruction lineage | PASS | no_declared_lineage_reaches_target |
| 1313 | IAPS permits conditional destructive structural successorship | PASS | structural_successor |
| 1314 | IAPS treats simultaneous exact targets branch-valuedly | PASS | branch_valued_continuation |
| 1315 | Both targets fail external-decoder autonomy | PASS | S13 |
| 1316 | Both targets fail delayed post-withdrawal collapse | PASS | S28 |
| 1317 | Same-carrier representation control is not misclassified as cross-carrier | PASS | S20 |
| 1318 | Copy audit answers exact duplication | PASS | What differs between the primary and exact duplication? |
| 1319 | Copy audit answers symmetric fission | PASS | relation-valued under symmetric fission |
| 1320 | Copy audit answers uniqueness | PASS | Is any uniqueness claim structural or purchased? |
| 1321 | Copy audit answers destructive transfer | PASS | Can destructive transfer satisfy the criterion? |
| 1322 | Copy audit answers gradual replacement | PASS | Does gradual replacement receive its verdict for substantive reasons? |
| 1323 | Copy audit answers autonomy | PASS | Is post-handoff autonomy demonstrated or assumed? |
| 1324 | Copy audit answers claim ceiling | PASS | What does the result concern? |
| 1325 | Copy audit states an interior operational discriminator | PASS | corridor |
| 1326 | Copy audit refuses uniqueness under exact symmetry | PASS | symmetry |
| 1327 | Copy audit distinguishes FIACH and IAPS on destructive reconstruction | PASS | primary/fallback split |
| 1328 | Copy audit states autonomy is demonstrated only relative to model data | PASS | autonomy boundary |
| 1329 | Copy audit limits result to structural precursor | PASS | claim ceiling |
| 1330 | Later handoff contains ## 1. Authorized target order | PASS | ## 1. Authorized target order |
| 1331 | Later handoff contains ## 2. Theorem statements to attempt | PASS | ## 2. Theorem statements to attempt |
| 1332 | Later handoff contains ## 3. Toy programs to build | PASS | ## 3. Toy programs to build |
| 1333 | Later handoff contains ## 4. Proof/program order | PASS | ## 4. Proof/program order |
| 1334 | Later handoff contains ## 5. Controls required before any positive claim | PASS | ## 5. Controls required before any positive claim |
| 1335 | Later handoff contains ## 6. Switch conditions | PASS | ## 6. Switch conditions |
| 1336 | Later handoff contains ## 7. Completion conditions for the later project | PASS | ## 7. Completion conditions for the later project |
| 1337 | Later handoff starts with no-go/control work before combined positive claim | PASS | order |
| 1338 | Later handoff defines primary-to-fallback switch conditions | PASS | switch |
| 1339 | Later handoff explicitly requires no full Six Birds simulation | PASS | scope |
| 1340 | Later handoff preserves Python-generator/Lean-checker trust split | PASS | trust split |
| 1341 | Dossier recounts CST-EXP-00 | PASS | phase 0 |
| 1342 | Dossier recounts CST-EXP-01 | PASS | phase 1 |
| 1343 | Dossier recounts CST-EXP-02 | PASS | phase 2 |
| 1344 | Dossier recounts CST-EXP-03 | PASS | phase 3 |
| 1345 | Dossier recounts CST-EXP-04 | PASS | phase 4 |
| 1346 | Dossier recounts CST-EXP-05 | PASS | phase 5 |
| 1347 | Dossier recounts CST-EXP-06 | PASS | phase 6 |
| 1348 | Dossier supports exit-gate concept: what exact theorem-and-toy target | PASS | what exact theorem-and-toy target |
| 1349 | Dossier supports exit-gate concept: counterexample | PASS | counterexample |
| 1350 | Dossier supports exit-gate concept: assumption | PASS | assumption |
| 1351 | Dossier supports exit-gate concept: falsifier | PASS | falsifier |
| 1352 | Dossier supports exit-gate concept: would not answer | PASS | would not answer |
| 1353 | Frozen target corpus dependency A-CT-01 resolves | PASS | A-CT-01 |
| 1354 | Frozen target corpus dependency A-PQ-01 resolves | PASS | A-PQ-01 |
| 1355 | Frozen target corpus dependency A-PQ-02 resolves | PASS | A-PQ-02 |
| 1356 | Frozen target corpus dependency A-PR-01 resolves | PASS | A-PR-01 |
| 1357 | Frozen target corpus dependency A-EX-01 resolves | PASS | A-EX-01 |
| 1358 | Frozen target corpus dependency A-EV-01 resolves | PASS | A-EV-01 |
| 1359 | Frozen target corpus dependency A-LG-01 resolves | PASS | A-LG-01 |
| 1360 | Frozen target corpus dependency A-AG-01 resolves | PASS | A-AG-01 |
| 1361 | Frozen target corpus dependency A-VI-01 resolves | PASS | A-VI-01 |
| 1362 | Frozen target corpus dependency A-TM-01 resolves | PASS | A-TM-01 |
| 1363 | Frozen target corpus dependency A-CF-01 resolves | PASS | A-CF-01 |
| 1364 | Frozen target corpus dependency A-HO-01 resolves | PASS | A-HO-01 |
| 1365 | Frozen target corpus dependency A-RE-01 resolves | PASS | A-RE-01 |
| 1366 | Frozen target corpus dependency A-OP-01 resolves | PASS | A-OP-01 |
| 1367 | Frozen target corpus dependency A-QEC-01 resolves | PASS | A-QEC-01 |
| 1368 | Frozen target corpus dependency A-FS-01 resolves | PASS | A-FS-01 |
| 1369 | Frozen target corpus dependency A-NO-01 resolves | PASS | A-NO-01 |
| 1370 | Frozen target assumption D-CARRIER resolves | PASS | D-CARRIER |
| 1371 | Frozen target assumption H-DISTINCT resolves | PASS | H-DISTINCT |
| 1372 | Frozen target assumption H-BRIDGE-ADM resolves | PASS | H-BRIDGE-ADM |
| 1373 | Frozen target assumption H-XCI resolves | PASS | H-XCI |
| 1374 | Frozen target assumption H-SOURCE-FULL resolves | PASS | H-SOURCE-FULL |
| 1375 | Frozen target assumption H-PRESERVE-O resolves | PASS | H-PRESERVE-O |
| 1376 | Frozen target assumption H-GLOBAL-GLUE resolves | PASS | H-GLOBAL-GLUE |
| 1377 | Frozen target assumption H-LINEAGE resolves | PASS | H-LINEAGE |
| 1378 | Frozen target assumption H-AUTONOMY resolves | PASS | H-AUTONOMY |
| 1379 | Frozen target assumption H-CERT-SOUND resolves | PASS | H-CERT-SOUND |
| 1380 | Frozen target assumption H-RECOG resolves | PASS | H-RECOG |
| 1381 | Frozen target assumption A1 resolves | PASS | A1 |
| 1382 | Frozen target assumption A2-P resolves | PASS | A2-P |
| 1383 | Frozen target assumption H-IDENTITY-O resolves | PASS | H-IDENTITY-O |
| 1384 | Dossier keeps certificate soundness and recognition outside structural theorem | PASS | assumption ladder |
| 1385 | Dossier keeps A1/A2-P outside structural theorem | PASS | ontology boundary |
| 1386 | Decision ledger contains ten active CST-EXP-06 decisions | PASS | 10 |
| 1387 | Decision IDs are D06-001..D06-010 | PASS | ["D06-001", "D06-002", "D06-003", "D06-004", "D06-005", "D06-006", "D06-007", "D06-008", "D06-009", "D06-010"] |
| 1388 | Markdown decision ledger contains D06-001 | PASS | D06-001 |
| 1389 | Markdown decision ledger contains D06-002 | PASS | D06-002 |
| 1390 | Markdown decision ledger contains D06-003 | PASS | D06-003 |
| 1391 | Markdown decision ledger contains D06-004 | PASS | D06-004 |
| 1392 | Markdown decision ledger contains D06-005 | PASS | D06-005 |
| 1393 | Markdown decision ledger contains D06-006 | PASS | D06-006 |
| 1394 | Markdown decision ledger contains D06-007 | PASS | D06-007 |
| 1395 | Markdown decision ledger contains D06-008 | PASS | D06-008 |
| 1396 | Markdown decision ledger contains D06-009 | PASS | D06-009 |
| 1397 | Markdown decision ledger contains D06-010 | PASS | D06-010 |
| 1398 | Rejected-default ledger contains RD06-001 | PASS | RD06-001 |
| 1399 | Rejected-default ledger contains RD06-002 | PASS | RD06-002 |
| 1400 | Rejected-default ledger contains RD06-003 | PASS | RD06-003 |
| 1401 | Rejected-default ledger contains RD06-004 | PASS | RD06-004 |
| 1402 | Rejected-default ledger contains RD06-005 | PASS | RD06-005 |
| 1403 | Rejected-default ledger contains RD06-006 | PASS | RD06-006 |
| 1404 | Rejected-default ledger contains RD06-007 | PASS | RD06-007 |
| 1405 | Rejected-default ledger contains RD06-008 | PASS | RD06-008 |
| 1406 | Rejected-default ledger contains RD06-009 | PASS | RD06-009 |
| 1407 | Rejected-default ledger contains RD06-010 | PASS | RD06-010 |
| 1408 | Unresolved-question ledger contains implementation question 101 | PASS | 101 |
| 1409 | Unresolved-question ledger contains implementation question 102 | PASS | 102 |
| 1410 | Unresolved-question ledger contains implementation question 103 | PASS | 103 |
| 1411 | Unresolved-question ledger contains implementation question 104 | PASS | 104 |
| 1412 | Unresolved-question ledger contains implementation question 105 | PASS | 105 |
| 1413 | Unresolved-question ledger contains implementation question 106 | PASS | 106 |
| 1414 | Unresolved-question ledger contains implementation question 107 | PASS | 107 |
| 1415 | Unresolved-question ledger contains implementation question 108 | PASS | 108 |
| 1416 | Unresolved-question ledger contains implementation question 109 | PASS | 109 |
| 1417 | Unresolved-question ledger contains implementation question 110 | PASS | 110 |
| 1418 | No theorem or toy implementation file was introduced | PASS | [] |
| 1419 | Phase Python files are administrative build/validation only | PASS | ["scripts/build_exp06_assets.py", "scripts/exp06_data.py", "scripts/finalize_exp06_manifest.py", "scripts/validate_exp06.py", "scripts/verify_exp06_rebuild.py"] |
| 1420 | Final synthesis preserves boundary: consciousness nonclaim | PASS | consciousness nonclaim |
| 1421 | Final synthesis preserves boundary: numerical identity nonclaim | PASS | numerical identity nonclaim |
| 1422 | Final synthesis preserves boundary: A2 boundary | PASS | A2 boundary |
| 1423 | Final synthesis preserves boundary: proof nonimplementation | PASS | proof nonimplementation |
| 1424 | Final synthesis preserves boundary: toy nonimplementation | PASS | toy nonimplementation |
| 1425 | Root STATE advances to CST-EXP-06-v1 | PASS | state |
| 1426 | Root README names FIACH primary and IAPS fallback | PASS | root readme |
| 1427 | Root STATUS marks implementation as none | PASS | status |
| 1428 | Root CHANGELOG records CST-EXP-06 | PASS | changelog |
| 1429 | Final manifest exists | PASS | manifests/MANIFEST.json |
| 1430 | Final manifest is labeled CST-EXP-06 | PASS | CST-EXP-06 |
| 1431 | Every final manifest entry verifies | PASS | {"bad": [], "checked": 521} |
| 1432 | Manifest file_count equals entry count | PASS | 521 |
| 1433 | SHA256SUMS exists | PASS | manifests/SHA256SUMS |
| 1434 | Every static SHA256SUMS entry verifies | PASS | {"bad": [], "checked": 523} |
| 1435 | Phase summary is CST-EXP-06-v1 | PASS | {"phase": "CST-EXP-06", "state": "CST-EXP-06-v1"} |
| 1436 | Phase summary freezes FIACH and IAPS | PASS | {"fallback": {"claim_lanes": ["S-R", "S-L", "A"], "code": "IAPS", "id": "FT-02", "soft_score": 83.6, "status": "frozen_fallback", "title": "Integrated Autonomous Predictive Successorship"}, "primary": {"claim_lanes": ["S-R", "S-L", "A"], "code": "FIACH", "id": "FT-01", "soft_score": 84.5, "status": "frozen_for_later_implementation", "title": "Finite Integrated Autonomous Causal Handoff"}} |
| 1437 | Portable rebuild verification passes | PASS | pass |
| 1438 | Portable rebuild compares a substantial phase surface bank | PASS | {"count": 25, "different": [], "missing": []} |
| 1439 | Completion report exists and passes exit gate | PASS | completion |
| 1440 | Restore instructions name CST-EXP-06 tag | PASS | restore |
