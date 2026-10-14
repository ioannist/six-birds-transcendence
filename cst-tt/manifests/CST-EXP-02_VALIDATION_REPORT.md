# CST-EXP-02 Validation Report

**Generated:** 2026-08-09T20:15:41.310329+00:00
**Result:** **PASS**
**Checks passed:** **113/113**
**Scope:** completeness and coherence of the neutral source–target schema, 20 governing-plan scenarios, 15 supplemental controls, ten-axis matrix, lane-typed outcome vocabulary, discriminator/question/asset crosswalks, inherited corpus controls, and strict nonselection boundary. This is not evidence that consciousness transfers or that personal identity is preserved.

## Executed checks

| # | Check | Result | Evidence |
|---:|---|---:|---|
| 1 | All required CST-EXP-02 artifacts exist | PASS | {"missing": [], "required": 67} |
| 2 | Required CST-EXP-02 artifacts are nonempty | PASS | [] |
| 3 | All phase and inherited corpus CSVs parse | PASS | 11 CSV files |
| 4 | Scenario registry and phase metadata JSON parse | PASS | 4 JSON files |
| 5 | Embedded source archives retain ZIP integrity | PASS | both CRC checks pass |
| 6 | Paper archive still contains 60 top-level TeX manuscripts | PASS | 60 |
| 7 | Normative inputs and source archives retain pinned hashes | PASS | {"bad": [], "pinned": 4} |
| 8 | Frozen paper inventory remains P01–P60 | PASS | 60 |
| 9 | Machine and curated statement banks retain 1,359 and 378 rows | PASS | {"curated": 378, "machine": 1359} |
| 10 | Canonical asset bank retains 26 families and 196 links | PASS | {"families": 26, "links": 196} |
| 11 | Typed-map, dependency, source-label, and gap counts remain frozen | PASS | {"gaps": 14, "labels": 3658, "lexical": 1359, "maps": 106} |
| 12 | All 18 embedded duplicate manuscripts remain mapped | PASS | 18 |
| 13 | P46 remains quarantined from substantive statement imports | PASS | machine=0; curated exclusion=1 |
| 14 | P42 remains normative and P60 has zero independent evidential weight | PASS | version log |
| 15 | Registry declares neutral CST-EXP-02 semantics | PASS | Operational edges are not lineage edges; outcome vectors are unfilled. |
| 16 | Registry contains exactly the ten governing protocol axes | PASS | [] |
| 17 | Ten axes expose the complete 44-value vocabulary | PASS | {"branching": 4, "bridge_dependence": 4, "carrier_relation": 3, "change_mode": 7, "fidelity": 5, "granularity": 5, "reversibility": 3, "route_multiplicity": 3, "source_fate": 6, "target_timing": 4} |
| 18 | Axis registry has one unique row per declared value | PASS | 44 |
| 19 | Every axis value has a neutral meaning, question, and blocked inference | PASS | 44/44 |
| 20 | Registry contains exactly S01–S35 | PASS | {"ids": ["S01", "S02", "S03", "S04", "S05", "S06", "S07", "S08", "S09", "S10", "S11", "S12", "S13", "S14", "S15", "S16", "S17", "S18", "S19", "S20", "S21", "S22", "S23", "S24", "S25", "S26", "S27", "S28", "S29", "S30", "S31", "S32", "S33", "S34", "S35"], "rows": 35} |
| 21 | S01–S20 are the governing-plan cases and S21–S35 are supplemental | PASS | {"canonical": 20, "supplemental": 15} |
| 22 | Protocol-axis matrix contains exactly S01–S35 | PASS | {"ids": ["S01", "S02", "S03", "S04", "S05", "S06", "S07", "S08", "S09", "S10", "S11", "S12", "S13", "S14", "S15", "S16", "S17", "S18", "S19", "S20", "S21", "S22", "S23", "S24", "S25", "S26", "S27", "S28", "S29", "S30", "S31", "S32", "S33", "S34", "S35"], "rows": 35} |
| 23 | Every matrix axis cell uses a declared value | PASS | [] |
| 24 | All 44 axis values are represented in the 35-case battery | PASS | [] |
| 25 | JSON registry and CSV matrix agree on IDs, titles, and ten axes | PASS | [] |
| 26 | Every scenario supplies operational detail beyond axis labels | PASS | 35/35 |
| 27 | All matrix card paths resolve | PASS | [] |
| 28 | All twenty governing-plan cases retain their defining protocol profiles | PASS | [] |
| 29 | Every governing-plan case retains explicit canonical prompt wording | PASS | ["Gradual neuron-by-neuron or component-by-component replacement.", "Instantaneous destructive scan and reconstruction.", "Nondestructive exact copy while the source continues.", "Copy first, source deletion later.", "Two simultaneous exact targets.", "Target activation after a temporal gap.", "Transfer through a long-lived source-target overlap.", "Distributed extension in which no sharp handoff exists.", "Fission followed by independent divergence.", "Fission followed by later fusion.", "Public/report-perfect copy with predictive mismatch.", "Predictive match with different binding or action-credit structure.", "Target maintained only by an external decoder or source process.", "Route loop that restores every current observable while changing predictive state.", "Local pairwise matches that fail to glue into one global identity package.", "Transfer near a viability boundary.", "Loss… |
| 30 | S11 stipulates public/report perfection with predictive mismatch | PASS | exact public/report equivalence; explicitly nonexact predictive state |
| 31 | S12 stipulates predictive matching with binding/action-credit mismatch | PASS | exact predictive dynamics; explicitly nonexact binding or action-credit structure |
| 32 | S13 isolates continuing external decoder/source dependence | PASS | remove source process and decoder separately, then jointly; retain ordinary target environment |
| 33 | S14 is a holonomy control rather than the exact round-trip case | PASS | {"fidelity_scope": "exact current observables at loop closure; explicitly nonexact predictive state", "reversibility": "approximately_reversible", "route_multiplicity": "holonomy_bearing_routes"} |
| 34 | S15 isolates local matching with failed global gluing | PASS | exact local records; globally inconsistent package |
| 35 | S16 and S17 separate bounded defect from endogenous repair | PASS | {"S16": "residual_bounded", "S17": "error_corrected"} |
| 36 | S18 is an exact reversible round-trip contrast to S14 | PASS | {"fidelity_scope": "exact preservation of a declared package-state family under B and B^{-1}", "reversibility": "reversible", "route_multiplicity": "multiple_equivalent_routes"} |
| 37 | S19 uses an explicit non-unit clock relation | PASS | explicit non-unit map or order-preserving relation; no canonical simultaneity |
| 38 | S20 is a same-carrier false-positive control | PASS | {"carrier_relation": "same_support_reencoding", "cross_carrier_status": "same_carrier_negative_control"} |
| 39 | Fifteen supplemental controls cover the declared failure-mode extensions | PASS | [] |
| 40 | Supplemental controls remain operational cases rather than candidate verdicts | PASS | 15/15 |
| 41 | Neutral schema covers all required semantic topics | PASS | [] |
| 42 | G_op is explicitly prior to and distinct from candidate G_kappa | PASS | graph separation |
| 43 | Source and target are protocol roles, not a presupposed identity relation | PASS | role typing |
| 44 | Handoff records protocol responsibility rather than subject movement | PASS | handoff neutrality |
| 45 | Time uses local clocks and an optional relation rather than canonical now | PASS | clock neutrality |
| 46 | Autonomy uses a declared withdrawal intervention signature | PASS | withdrawal signature |
| 47 | Fidelity is paired with comparison granularity | PASS | fidelity pair |
| 48 | Verdicts separate S-T, S-R, S-L, A, and R | PASS | five lane slots |
| 49 | Schema explicitly makes no consciousness, identity, survival, uploading, or A2 conclusion | PASS | nonclaims |
| 50 | Exactly 35 scenario cards exist | PASS | ["S01.md", "S02.md", "S03.md", "S04.md", "S05.md", "S06.md", "S07.md", "S08.md", "S09.md", "S10.md", "S11.md", "S12.md", "S13.md", "S14.md", "S15.md", "S16.md", "S17.md", "S18.md", "S19.md", "S20.md", "S21.md", "S22.md", "S23.md", "S24.md", "S25.md", "S26.md", "S27.md", "S28.md", "S29.md", "S30.md", "S31.md", "S32.md", "S33.md", "S34.md", "S35.md"] |
| 51 | Every card contains the complete neutral card schema | PASS | [] |
| 52 | Every card leaves five candidate outcome lanes deliberately unfilled | PASS | [] |
| 53 | Every card applies all ten discriminators | PASS | [] |
| 54 | Stipulated facts do not prefill identity or consciousness verdicts | PASS | [] |
| 55 | Every card states that its operational graph supplies no lineage edge | PASS | [] |
| 56 | Battery declares 20 governing cases plus 15 supplemental controls | PASS | battery size line |
| 57 | Battery index contains every S01–S35 card link | PASS | [] |
| 58 | Battery explicitly names all twenty governing-plan thought experiments | PASS | [] |
| 59 | Battery states that no scenario defines transfer for the others | PASS | anti-paradigm rule |
| 60 | Battery keeps target, lineage, autonomy, and ontology as candidate outputs | PASS | facts/outputs boundary |
| 61 | Outcome registry contains 27 unique labels | PASS | {"rows": 27, "unique": 27} |
| 62 | Outcome labels cover exactly S-T, S-R, S-L, A, and R | PASS | {"A": 5, "R": 3, "S-L": 8, "S-R": 6, "S-T": 5} |
| 63 | Every label has a neutral meaning and blocked inference | PASS | 27/27 |
| 64 | Taxonomy maps all twelve governing-plan outcome concepts | PASS | [] |
| 65 | Canonical outcome labels avoid metaphysically loaded terms | PASS | [] |
| 66 | Taxonomy is explicitly candidate-output vocabulary with no preclassified scenario | PASS | taxonomy status |
| 67 | Underdetermination requires a typed basis | PASS | seven bases |
| 68 | No outcome label licenses an O claim | PASS | ontology boundary |
| 69 | Registry contains the ten required discriminators D01–D10 | PASS | ["D01", "D02", "D03", "D04", "D05", "D06", "D07", "D08", "D09", "D10"] |
| 70 | Discriminators cover all ten governing-plan distinctions | PASS | [] |
| 71 | Discriminator matrix is the complete 35×10 Cartesian product | PASS | {"pairs": 350, "rows": 350} |
| 72 | Every discriminator row permits answer, explicit underdetermination, or scoped nonapplicability | PASS | 350/350 |
| 73 | Discriminator relevance uses a controlled vocabulary | PASS | {"mandatory": 18, "primary": 188, "secondary": 144} |
| 74 | Every scenario has at least four primary/mandatory discriminators | PASS | {"S01": 6, "S02": 6, "S03": 5, "S04": 4, "S05": 4, "S06": 6, "S07": 6, "S08": 6, "S09": 6, "S10": 7, "S11": 5, "S12": 5, "S13": 6, "S14": 7, "S15": 7, "S16": 5, "S17": 7, "S18": 6, "S19": 7, "S20": 6, "S21": 6, "S22": 7, "S23": 7, "S24": 6, "S25": 7, "S26": 5, "S27": 6, "S28": 5, "S29": 4, "S30": 5, "S31": 5, "S32": 6, "S33": 6, "S34": 6, "S35": 8} |
| 75 | Autonomy and continuation-cardinality probes are primary/mandatory in every scenario | PASS | {} |
| 76 | All discriminator claim lanes use the canonical vocabulary | PASS | 350/350 |
| 77 | Scenario-question crosswalk has 1,278 unique valid rows | PASS | {"bank_ids": 100, "rows": 1278, "unique": 1278} |
| 78 | Every scenario is linked to all twelve governing core questions | PASS | {} |
| 79 | Every scenario has at least ten tailored questions beyond the core | PASS | {"S01": 26, "S02": 30, "S03": 24, "S04": 19, "S05": 22, "S06": 27, "S07": 19, "S08": 23, "S09": 21, "S10": 25, "S11": 27, "S12": 23, "S13": 20, "S14": 23, "S15": 24, "S16": 23, "S17": 31, "S18": 30, "S19": 28, "S20": 28, "S21": 26, "S22": 25, "S23": 27, "S24": 25, "S25": 26, "S26": 25, "S27": 26, "S28": 17, "S29": 21, "S30": 24, "S31": 20, "S32": 21, "S33": 29, "S34": 20, "S35": 33} |
| 80 | Scenario-asset crosswalk has 164 unique valid rows | PASS | {"rows": 164, "unique": 164} |
| 81 | Every scenario imports at least three corpus asset families | PASS | {"S01": 5, "S02": 5, "S03": 4, "S04": 4, "S05": 3, "S06": 4, "S07": 5, "S08": 5, "S09": 4, "S10": 5, "S11": 5, "S12": 5, "S13": 5, "S14": 4, "S15": 5, "S16": 4, "S17": 5, "S18": 5, "S19": 4, "S20": 3, "S21": 5, "S22": 5, "S23": 5, "S24": 5, "S25": 5, "S26": 5, "S27": 5, "S28": 5, "S29": 5, "S30": 5, "S31": 5, "S32": 5, "S33": 5, "S34": 5, "S35": 5} |
| 82 | Every scenario asset import preserves fixed-support scope and imports no verdict | PASS | 164/164 |
| 83 | All discriminator asset and question references resolve | PASS | [] |
| 84 | Verdict template contains one row for every S01–S35 case | PASS | 35 |
| 85 | All 175 candidate output cells remain UNFILLED | PASS | 175 |
| 86 | Verdict rows require assumptions, route/approximation scope, evidence, blocks, nonclaims, and underdetermination basis | PASS | ["underdetermination_basis", "criterion_sensitive_scenario_fields", "assumptions_spent", "route_sensitivity", "approximation_scope", "evidence_or_argument", "blocked_inferences", "nonclaims"] |
| 87 | YAML contract requires S01–S35 and all five typed outcome fields | PASS | YAML contract |
| 88 | Scenario exit audit records all required outputs as PASS | PASS | {"pass_rows": 8} |
| 89 | Exit gate requires typed verdict or explicit underdetermination for every battery case | PASS | exit contract |
| 90 | Exit gate forbids any single scenario from defining transfer | PASS | anti-paradigm rule |
| 91 | Decision ledger retains 18 D00, 12 D01, and 14 D02 rulings | PASS | {"missing_D02": [], "rows": 44} |
| 92 | Human decision log mirrors every machine decision ID | PASS | 44 |
| 93 | Eighteen rejected defaults RD02-001–RD02-018 are recorded | PASS | 18/18 |
| 94 | Sixteen phase-specific unresolved questions 45–60 remain open | PASS | 16/16 |
| 95 | Repository state declares CST-EXP-02 complete and CST-EXP-03 next | PASS | state headers |
| 96 | Repository state preserves every phase nonselection boundary | PASS | [] |
| 97 | Generated EXP-02 summary matches every live phase count | PASS | {"axis_values": 44, "battery_scenarios": 35, "discriminators": 10, "governing_plan_scenarios": 20, "outcome_labels": 27, "protocol_axes": 10, "scenario_asset_crosswalk_rows": 164, "scenario_cards": 35, "scenario_discriminator_rows": 350, "scenario_question_crosswalk_rows": 1278, "supplemental_stress_controls": 15, "unfilled_verdict_rows": 35} |
| 98 | Generated summary records no target, verdict, theorem, or program selection | PASS | all false |
| 99 | Frozen phase summary records complete/pass/frozen CST-EXP-02 with CST-EXP-03 next | PASS | {"exit_gate": "pass", "next_phase": "CST-EXP-03", "phase": "CST-EXP-02", "repository_state": "frozen", "status": "complete"} |
| 100 | Frozen phase summary matches all live scenario counts | PASS | {"axis_values": 44, "battery_scenarios": 35, "discriminators": 10, "governing_plan_scenarios": 20, "outcome_labels": 27, "protocol_axes": 10, "scenario_asset_crosswalk_rows": 164, "scenario_cards": 35, "scenario_discriminator_rows": 350, "scenario_question_crosswalk_rows": 1278, "supplemental_stress_controls": 15, "unfilled_verdict_rows": 35} |
| 101 | Frozen phase summary records no scientific target or implementation | PASS | all false |
| 102 | Portable rebuild reproduced all 55 deterministic phase-02 surfaces byte-for-byte | PASS | {"compared_files": 55, "date": "2026-08-09", "exclusions": ["validation report timestamps", "content manifest regenerated after validation", "Git metadata"], "hash_map_serialization": "sorted sha256sum-style lines: <file_sha256><two spaces><relative_path><newline>", "hash_map_sha256": "2ef087e418d50e4ea4e8bb54b7b3ebbeab7652a2f98ce2a74ee70836049a2adb", "method": "copy repository without Git metadata; run scripts/rebuild_exp02.sh; compare deterministic phase-02 generated surfaces byte-for-byte", "phase": "CST-EXP-02", "project": "CST-EXP", "rebuild_validator": {"checks_passed": 113, "checks_total": 113, "status": "pass"}, "result": "pass", "scientific_nonclaim": "This verifies reproducibility and internal integrity only, not the correctness of any transfer or lineage criterion.", "scope": ["scenarios/**", "ledgers/scenario_*", "templates/SCENARIO_VERDICT_RECORD.yml", "manifests/EXP02_AS… |
| 103 | Portable rebuilt repository passed the full validator | PASS | {"checks_passed": 113, "checks_total": 113, "status": "pass"} |
| 104 | Later candidate, challenge, feasibility, and synthesis phases remain unexecuted | PASS | [] |
| 105 | All retained CST-EXP Python sources compile without emitting cache files | PASS | 8/8 |
| 106 | EXP-01 and EXP-02 rebuild scripts pass shell syntax | PASS | 2/2 |
| 107 | All local Markdown file links resolve | PASS | [] |
| 108 | Repository contains no symlinks | PASS | [] |
| 109 | All text artifacts are UTF-8 readable | PASS | [] |
| 110 | No unintended empty files remain | PASS | [] |
| 111 | No generated Python cache files remain | PASS | [] |
| 112 | No Lean proof, compiled proof, notebook, or toy-program artifact was introduced | PASS | [] |
| 113 | Content manifest and SHA256SUMS match every frozen file | PASS | {"checksum_bad": [], "entries": 254, "manifest_bad": []} |

## Exit-gate ruling

**PASS.** CST-EXP-02 supplies a neutral, carrier-typed protocol language and a complete 35-case stress battery. Every later candidate must return separately typed transport, target-realization, lineage, autonomy, and recognition outputs—or explicit underdetermination/nonapplicability—without any scenario, operational edge, or source-fate fact predefining continuation.
