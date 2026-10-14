# CST-EXP-00 Validation Report

**Generated:** 2026-08-09T17:07:54.136691+00:00  
**Result:** **PASS**  
**Checks passed:** **52/52**  
**Scope:** phase artifacts, typing discipline, ledger integrity, source provenance, exit-gate boundaries, and absence of later-phase implementation. This is not validation of a consciousness-transfer hypothesis.

## Executed checks

| # | Check | Result | Evidence |
|---:|---|---:|---|
| 1 | Required phase and persistence artifacts exist | PASS | 39/39; missing=[] |
| 2 | Required artifacts are nonempty | PASS | empty=[] |
| 3 | All YAML, JSON, and CSV artifacts parse | PASS | 6 YAML, 2 JSON, 6 CSV; errors=[] |
| 4 | Glossary machine schema is complete | PASS | columns=['term_id', 'term', 'category', 'provisional_definition', 'use_rule', 'not_to_be_confused_with'] |
| 5 | Glossary has 96 unique sequential IDs | PASS | count=96, first=['G001'], last=['G096'] |
| 6 | Glossary term names are unique | PASS | case-folded uniqueness |
| 7 | Every glossary field is populated | PASS | all required fields nonempty |
| 8 | Human glossary mirrors machine IDs and titles | PASS | Markdown entries=96 |
| 9 | Every human glossary entry has three required fields | PASS | 96 definition/use/anti-confusion fields |
| 10 | All plan-mandated noun families are canonicalized | PASS | missing nouns=[]; adjective families={'destructive': True, 'nondestructive': True, 'gradual': True, 'abrupt': True, 'reversible': True, 'distributed': True, 'autonomous': True, 'realization': True} |
| 11 | Claim lanes are exactly S-T/S-R/S-L/A/R/O/M | PASS | tags=['S-T', 'S-R', 'S-L', 'A', 'R', 'O', 'M'] |
| 12 | Every claim lane has its CST namespace alias | PASS | all namespaced aliases correct |
| 13 | Claim-register template exposes type, status, assumptions, provenance, and nonclaims | PASS | columns=['claim_id', 'statement', 'primary_tag', 'secondary_tags', 'result_status', 'carrier_scope', 'interface_scope', 'route_scope', 'transported_object', 'bridge_type', 'assumptions', 'evidence_type', 'source_provenance', 'connecting_implication', 'falsifier_or_failure_condition', 'blocked_inferences', 'nonclaims', 'owner', 'review_state', 'notes'] |
| 14 | Anti-conflation ledger schema is complete | PASS | columns=['guard_id', 'antecedent', 'forbidden_inference', 'why_blocked', 'minimum_additional_work', 'candidate_stress_test', 'relevant_tags', 'severity', 'status'] |
| 15 | Anti-conflation ledger has 60 sequential active guards | PASS | count=60 |
| 16 | Every anti-conflation guard is fully specified | PASS | all fields nonempty |
| 17 | Every anti-conflation guard has canonical claim tags | PASS | bad=[] |
| 18 | All twelve plan-minimum inference blocks are present | PASS | mapped=['AC-001', 'AC-004', 'AC-006', 'AC-007', 'AC-010', 'AC-012', 'AC-013', 'AC-019', 'AC-021', 'AC-023', 'AC-024', 'AC-038'] |
| 19 | Question bank has 100 unique mandatory questions | PASS | count=100 |
| 20 | Question bank has 12 core and 88 supplementary questions | PASS | 12 core / 88 supplementary |
| 21 | Core question registry matches live core order | PASS | registered=['Q-CORE-001', 'Q-CORE-002', 'Q-CORE-003', 'Q-CORE-004', 'Q-CORE-005', 'Q-CORE-006', 'Q-CORE-007', 'Q-CORE-008', 'Q-CORE-009', 'Q-CORE-010', 'Q-CORE-011', 'Q-CORE-012'] |
| 22 | Core prompts reproduce the governing plan verbatim | PASS | Q-CORE-001..012 exact |
| 23 | Question bank spans 13 declared categories | PASS | categories={'core_plan_questions': 12, 'framing': 4, 'typing': 9, 'bridge': 8, 'preservation': 10, 'route_history': 7, 'lineage': 11, 'autonomy': 6, 'observability_recognition': 7, 'approximation_composition': 7, 'assumptions_conclusions': 8, 'controls_falsification': 6, 'theorem_toy_feasibility': 5} |
| 24 | Every question satisfies the response schema | PASS | all required fields present |
| 25 | All question-to-guard references resolve | PASS | bad=[] |
| 26 | Every anti-conflation guard is exercised by the question bank | PASS | linked=60/60 |
| 27 | Every question has one or more canonical claim tags | PASS | bad=[] |
| 28 | Question response states fail closed | PASS | statuses=['answered', 'underdetermined_with_reason', 'not_applicable_with_reason', 'blocked_with_reason'] |
| 29 | Assumption CSV and YAML mirrors agree exactly | PASS | count=20 |
| 30 | Critical structural, recognition, soundness, A1/A2, and identity premises are separate | PASS | missing=[] |
| 31 | Decision ledger has a complete unique active phase register | PASS | count=18 |
| 32 | Human decision log contains every machine decision ID | PASS | all 18 IDs present |
| 33 | Machine circularity audit has at least 20 passing rows | PASS | count=20 |
| 34 | All three later-phase record templates parse and are nonempty | PASS | templates=[True, True, True] |
| 35 | Normative plan, triage, and source archives match pinned hashes | PASS | inputs/source_archives/six-birds-consciousness_v41.zip=84a1ace956f46e08288653e1f536ef943180f5a46b5d78e67dbe69e1e713e1e8; inputs/source_archives/six_birds_papers_tex.zip=38979ca3c311c55a2210cbfd7c2f40077c8ecdf3b1f5aa50fe51c7a8c178cd70; inputs/normative/PAPER_TRIAGE.md=c270c759560defd5fcd2d261c28d5ca91e5ed911b4ec65e60c3fb668d6bbfd9a; inputs/normative/PREPARATORY_EXPLORATION_PLAN.md=8a7a115bc3b80c3a02859e1a456ce03b48183ba4ec2d94e5f33db78080a26401 |
| 36 | Both retained source archives pass ZIP integrity checks | PASS | errors=[] |
| 37 | Owner source exclusion is preserved | PASS | exclusion language found |
| 38 | Papers 42 and 60 remain one versioned evidence line | PASS | version rule found |
| 39 | A2 non-theorem boundary is explicit | PASS | verbatim boundary found |
| 40 | Phase summary matches all live ledger counts | PASS | summary={'glossary_terms': 96, 'anti_conflation_rows': 60, 'mandatory_questions': 100, 'question_categories': 13, 'core_questions': 12, 'supplementary_questions': 88, 'total_questions': 100} |
| 41 | Phase summary records completion, freeze, and no science implementation | PASS | complete/pass/frozen; science flags false |
| 42 | Transport, realization, lineage, autonomy, recognition, and ontology are independently named | PASS | predicates=['Transport_B', 'TargetPackage_C', 'Lineage_κ', 'Autonomous_h', 'Recognized_E', 'Ontic_Ω'] |
| 43 | Charter blocks every default cross-lane implication | PASS | explicit no-default-arrow rule |
| 44 | Exit-gate audit records PASS without a scientific conclusion | PASS | gate pass and phase boundary present |
| 45 | Later-phase science directories remain unexecuted | PASS | non-placeholder files=[] |
| 46 | No theorem, proof, toy-program, or simulation implementation artifact landed | PASS | forbidden=[] |
| 47 | No accidental TODO/TBD/FIXME placeholders remain | PASS | files=[] |
| 48 | No stale pre-merge anti-conflation counts remain | PASS | files=[] |
| 49 | All local Markdown links resolve | PASS | broken=[] |
| 50 | All repository text is UTF-8 readable | PASS | errors=[] |
| 51 | Repository contains no symlinks | PASS | symlinks=[] |
| 52 | No unintended empty files remain | PASS | empty=[] |

## Live phase state

- Glossary terms: **96**
- Anti-conflation guards: **60**
- Mandatory questions: **100** (**12** core, **88** supplementary; **13** categories)
- Assumption records: **20**
- Decision records: **18**

## Exit-gate ruling

**PASS.** CST-EXP-00 supplies a neutral, carrier-indexed exploration grammar in which structural transport, target realization, lineage, autonomy, recognition, and ontology are independently stateable. Central terms are not defined by successful consciousness transfer, and no theorem target, proof, toy program, simulation, empirical bridge, or ontological conclusion was selected or implemented.
