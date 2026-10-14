# CST-EXP-01 Validation Report

**Generated:** 2026-08-09T19:00:01.203377+00:00
**Result:** **PASS**
**Checks passed:** **87/87**
**Scope:** source accounting, complete paper coverage, statement and asset provenance, fixed-support and version discipline, consciousness-repository inventory, phase exit gates, and absence of target implementation. This is not proof of consciousness transfer, personal identity, or A2.

## Executed checks

| # | Check | Result | Evidence |
|---:|---|---:|---|
| 1 | Required phase artifacts exist | PASS | {"missing": [], "required": 55} |
| 2 | Required phase artifacts are nonempty | PASS | {"empty": []} |
| 3 | All phase CSV ledgers parse and contain data | PASS | 19 CSV files |
| 4 | Phase JSON metadata parses | PASS | 2 JSON files |
| 5 | Both embedded source archives pass ZIP integrity | PASS | ZIP CRC checks pass |
| 6 | Paper archive contains exactly 60 top-level TeX manuscripts | PASS | 60 |
| 7 | Normative inputs and source archives match pinned hashes | PASS | {"bad": [], "pinned": 4} |
| 8 | Paper inventory contains P01 through P60 exactly once | PASS | 60 |
| 9 | Original theorem-like environment census is 1,363 | PASS | 1363 |
| 10 | P46 contributes four quarantined environments to the original census | PASS | 4 |
| 11 | Non-quarantined machine statement bank contains 1,359 rows | PASS | 1359 |
| 12 | Machine statement IDs are unique | PASS | {"rows": 1359, "unique": 1359} |
| 13 | P46 is absent from the machine statement bank | PASS | 0 |
| 14 | P42/P60 statement counts retain version delta | PASS | {"P42": 173, "P60": 157} |
| 15 | Paper inventory hashes, bytes, and line counts match source archive | PASS | 60/60 |
| 16 | Exactly 60 paper cards exist | PASS | 60 |
| 17 | Paper-card IDs are exactly P01 through P60 | PASS | [] |
| 18 | Every non-quarantined paper card contains provenance, extraction, support, boundary, generalization, and disposition sections | PASS | 59/59 |
| 19 | P46 card is fail-closed metadata/exclusion only | PASS | # P46 — To Chat a Stone with Six Birds: Language Theory Models  > **Corpus verdict:** quarantine retained   > **Phase role:** metadata/exclusion card only   > **Claim lanes touched:** M   > **Version handling:** quarantined  ## Source identity  \| Field \| Value \| \|---\|---\| \| Corpus ID \| `P46` \| \| Sou |
| 20 | No paper card absorbs report-level triage text | PASS | [] |
| 21 | Paper coverage audit has 60 unique rows | PASS | 60 |
| 22 | Every coverage row resolves to an existing paper card | PASS | [] |
| 23 | Curated statement/provenance ledger has 378 rows | PASS | 378 |
| 24 | Curated statement IDs are unique | PASS | {"rows": 378, "unique": 378} |
| 25 | Every one of 60 papers has an explicit curated disposition | PASS | {"P01": 3, "P02": 4, "P03": 4, "P04": 9, "P05": 30, "P06": 13, "P07": 4, "P08": 5, "P09": 9, "P10": 5, "P11": 4, "P12": 4, "P13": 12, "P14": 10, "P15": 5, "P16": 12, "P17": 9, "P18": 5, "P19": 3, "P20": 3, "P21": 3, "P22": 9, "P23": 12, "P24": 6, "P25": 5, "P26": 3, "P27": 3, "P28": 4, "P29": 12, "P30": 17, "P31": 9, "P32": 12, "P33": 12, "P34": 9, "P35": 3, "P36": 5, "P37": 5, "P38": 2, "P39": 4, "P40": 4, "P41": 1, "P42": 14, "P43": 2, "P44": 6, "P45": 4, "P46": 1, "P47": 1, "P48": 5, "P49": 1, "P50": 9, "P51": 1, "P52": 11, "P53": 5, "P54": 2, "P55": 3, "P56": 5, "P57": 5, "P58": 4, "P59": 1, "P60": 5} |
| 26 | P46 has exactly one exclusion record and no content record | PASS | 1 |
| 27 | Every curated formal record resolves to machine bank and every manual record has a declared manual ID | PASS | {"bad": [], "manual_passages": 55} |
| 28 | Every non-quarantined curated record has a valid source hash and line span | PASS | 377/377 |
| 29 | Curated provenance has all fail-closed scope and nonclaim fields populated | PASS | 377 records |
| 30 | All curated claim lanes use the canonical seven-lane vocabulary | PASS | [] |
| 31 | All 1,359 machine-index statement spans resolve inside source files | PASS | 1359/1359 |
| 32 | Support/carrier ledger includes one paper-level row for every manuscript | PASS | 60 |
| 33 | Every paper-level support record exposes support, carrier, retyping, identity, and autonomy limits | PASS | [] |
| 34 | Nine fixed-support imports are explicitly flagged | PASS | {"actual": ["P03", "P08", "P09", "P14", "P16", "P18", "P23", "P24", "P39"], "expected": ["P03", "P08", "P09", "P14", "P16", "P18", "P23", "P24", "P39"]} |
| 35 | P42 is frozen as normative newer SAU revision and P60 has zero independent weight | PASS | version log |
| 36 | Curated provenance preserves P42/P60 evidential status | PASS | {"P42": ["normative-newer-revision"], "P60": ["superseded-older-revision-no-independent-weight"]} |
| 37 | All 18 embedded paper duplicates are recorded and not double-counted | PASS | 18 |
| 38 | C1–C8 have exactly eight separate clause cards | PASS | ["C1", "C2", "C3", "C4", "C5", "C6", "C7", "C8"] |
| 39 | Every clause card separates design contract, component evidence, transfer use, and integrated-instance boundary | PASS | [] |
| 40 | Theorem-family bank contains 25 source-scoped cards | PASS | 25 |
| 41 | Core lineage, combination, realization, transport, persistence, confluence, and completion cards exist | PASS | [] |
| 42 | T14 card exposes fission, fusion, empty target, and fixed-route/cross-carrier limits | PASS | T14 boundary vocabulary |
| 43 | T15 card is a joint-carrier combination gate, not a lineage theorem | PASS | T15 boundary vocabulary |
| 44 | T17 card records absent A2 invariance theorem, certificate-soundness purchase, and absent integrated target | PASS | T17 boundary vocabulary |
| 45 | Canonical asset provenance has 196 exact links across 26 asset families | PASS | {"families": 26, "links": 196} |
| 46 | Every asset link resolves to a curated provenance record | PASS | [] |
| 47 | Every canonical asset family has at least one exact source link | PASS | {"A-AG-01": 10, "A-AOR-01": 8, "A-AR-01": 9, "A-CD-01": 6, "A-CF-01": 11, "A-CT-01": 3, "A-CU-01": 11, "A-EV-01": 9, "A-EX-01": 4, "A-FS-01": 15, "A-HID-01": 9, "A-HO-01": 8, "A-LG-01": 5, "A-NO-01": 5, "A-ON-01": 7, "A-OP-01": 2, "A-PQ-01": 11, "A-PQ-02": 4, "A-PR-01": 9, "A-PT-01": 9, "A-QEC-01": 4, "A-RE-01": 13, "A-RT-01": 4, "A-ST-01": 4, "A-TM-01": 7, "A-VI-01": 9} |
| 48 | Asset atlas names all 26 canonical asset IDs | PASS | [] |
| 49 | Asset reuse is frozen fail-closed to exact provenance or a genuinely new primitive | PASS | atlas import rule |
| 50 | Typed map ledger contains 106 positive or explicit-negative records | PASS | 106 |
| 51 | Every map record declares source type, target type, import status, and cross-carrier caution | PASS | [] |
| 52 | Typed map ledger covers all 60 papers, including explicit-negative records | PASS | [] |
| 53 | P46 is absent from substantive typed maps | PASS | [{"cross_carrier_caution": "No map content imported.", "fixed_support_flag": "quarantined", "imported_status": "quarantined-no-import", "map_id": "MAP-P46-00", "object_or_map": "none imported", "paper_id": "P46", "paper_title": "To Chat a Stone with Six Birds: Language Theory Models", "source_type": "—", "target_type": "—", "type_signature": "—", "version_status": "quarantined"}] |
| 54 | Lexical dependency ledger covers all and only 1,359 non-quarantined statements | PASS | {"ids": 1359, "rows": 1359} |
| 55 | Every resolved explicit statement dependency points to a live machine-index statement | PASS | [] |
| 56 | P46 is absent from lexical dependency and source-label ledgers | PASS | quarantine exclusion |
| 57 | Source-label index contains 3,658 exact label locations | PASS | 3658 |
| 58 | Dependency graph contains all required structural, obstruction, assumption, and missing-theorem nodes | PASS | [] |
| 59 | Every graph edge resolves to live nodes | PASS | [] |
| 60 | Dependency graph encodes the four critical negative/nonimplication edges | PASS | [] |
| 61 | Rendered graph artifacts are nontrivial | PASS | {"png": 272669, "svg": 35010} |
| 62 | Gap-to-asset matrix contains 14 unique gaps | PASS | 14 |
| 63 | Required G01–G08 gaps are all present | PASS | [] |
| 64 | Every gap states partial assets, missing purchase, needed result type, and kill test | PASS | [] |
| 65 | Consciousness repository inventory contains 350 non-directory files | PASS | 350 |
| 66 | Formal/formal-metadata inventory contains 92 files | PASS | 92 |
| 67 | Python test inventory contains 21 modules | PASS | 21 |
| 68 | T14/T15/T17 and scaffold executable surfaces are inventoried | PASS | [] |
| 69 | Selected consciousness checks honestly report 45 passing tests | PASS | selected verification |
| 70 | Incomplete full-suite, snapshot, and Lean checks are explicitly not reported as passes | PASS | incomplete checks retained |
| 71 | Verification report preserves the no-integrated-instance/no-A2/no-lineage boundary | PASS | scope boundary |
| 72 | Decision ledger retains all 18 CST-EXP-00 rulings and 12 CST-EXP-01 rulings | PASS | {"missing_D01": [], "rows": 30} |
| 73 | Human decision log mirrors every machine decision ID | PASS | {"machine_ids": 30} |
| 74 | Repository state declares CST-EXP-01 complete and CST-EXP-02 next | PASS | state headers |
| 75 | Repository state explicitly says no target, theorem target, or toy program was selected | PASS | nonselection state |
| 76 | Phase summary matches all major live CST-EXP-01 counts | PASS | {"asset_families": 26, "asset_provenance_links": 196, "clause_cards": 8, "consciousness_repo_files": 350, "curated_provenance_records": 378, "embedded_duplicate_papers": 18, "gap_rows": 14, "lexical_dependency_rows": 1359, "machine_statements": 1359, "manual_source_passages": 55, "papers": 60, "source_labels": 3658, "theorem_family_cards": 25, "typed_map_records": 106} |
| 77 | Phase summary records complete/pass/frozen with no target or implementation | PASS | {"completed_at_utc": "2026-08-09T19:10:00+00:00", "counts": {"asset_families": 26, "asset_provenance_links": 196, "clause_cards": 8, "consciousness_repo_files": 350, "curated_provenance_records": 378, "embedded_duplicate_papers": 18, "formal_inventory_files": 92, "gap_rows": 14, "lexical_dependency_rows": 1359, "machine_statements": 1359, "manual_source_passages": 55, "original_theorem_like_environments": 1363, "paper_cards": 60, "papers": 60, "phase_01_decisions": 12, "quarantined_environments": 4, "source_labels": 3658, "test_modules": 21, "theorem_family_cards": 25, "typed_map_records": 106}, "exit_gate": "pass", "frozen_at_utc": "2026-08-09T19:30:00+00:00", "next_phase": "CST-EXP-02", "phase": "CST-EXP-01", "project": "CST-EXP", "repository_state": "frozen", "scientific_conclusion_s… |
| 78 | Later exploration/implementation directories remain unexecuted | PASS | [] |
| 79 | Composition notes are explicitly unranked and do not freeze a target | PASS | composition boundary |
| 80 | All six CST-EXP-01 exit gates are recorded PASS | PASS | 6 |
| 81 | All CST-EXP-01 Python scripts compile | PASS | 4/4 |
| 82 | Portable rebuild shell script passes syntax check | PASS | bash -n |
| 83 | All local Markdown links resolve | PASS | [] |
| 84 | Repository contains no symlinks | PASS | [] |
| 85 | All repository text artifacts are UTF-8 readable | PASS | [] |
| 86 | No unintended empty files remain | PASS | [] |
| 87 | Content manifest entries match live files | PASS | {"bad": [], "entries": 209} |

## Exit-gate ruling

**PASS.** CST-EXP-01 provides a complete, source-traceable, support-audited corpus bank and canonical asset atlas while leaving target selection, theorem conjecture, toy-program design, empirical recognition, and ontological interpretation open for later phases.
