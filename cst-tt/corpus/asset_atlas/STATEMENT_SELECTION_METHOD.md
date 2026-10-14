# Statement selection and source-reading method

## Two-layer inventory

CST-EXP-01 keeps two deliberately different layers:

1. **Complete lexical layer:** 1359 theorem-like environments from all non-quarantined manuscripts, with source file, exact line span, label, kind, and compact text. This layer is in `../machine_index/all_statement_index.csv` and prevents curated selection from erasing formal source statements.
2. **Curated transfer layer:** 378 source records selected for transfer-oriented navigation. It contains 55 manually bounded source passages for papers or critical sections that do not expose their content through theorem environments, plus formal statements selected by exact label/name and relevance.

The lexical parser is a provenance aid, not a TeX proof checker. Compact text may simplify macros; the original TeX archives are hash-preserved under `../../inputs/source_archives/`, and exact line spans are authoritative.

## Selection rules

- Dependency-order wave papers receive deeper selection than supporting/peripheral papers.
- Definitions, theorem/proposition/corollary statements, postulates, explicit nonclaims, controls, and named open boundaries are preferred.
- A record is not upgraded because Lean, Python, or code is mentioned. Evidence status stays paper-local.
- Every imported statement carries a fixed-support flag and an interface-relative warning.
- P46 is excluded fail-closed; no statement body enters either bank.
- P42 is the normative newer Strict Audited Utility revision. P60 remains for delta/provenance only and has zero independent evidential weight.
- Manual passages are exact line-bounded excerpts, not paraphrases invented without a source span.

## Dependency audit

`../../ledgers/lexical_dependency_index.csv` records explicit local references and citations from statement bodies and immediately following proof environments for 1359 non-quarantined formal statements. It does not infer unreferenced logical dependencies. The source-label index contains 3658 labels.

## Typed maps and asset provenance

`../../ledgers/map_type_ledger.csv` contains 106 positive or explicit-negative map records, including source and target types. `../../ledgers/asset_provenance.csv` contains 196 exact asset-to-statement links for all 26 canonical asset families.

## Nonselection rule

Curation establishes what can be reused and what remains blocked. It does not rank candidate transported objects, bridge types, lineage criteria, scenarios, theorem targets, or toy programs.
