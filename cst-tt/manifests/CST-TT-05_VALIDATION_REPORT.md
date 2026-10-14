# CST-TT-05 Validation Report

**Status:** PASS
**Total:** 2766
**Passed:** 2765
**Failed:** 0
**Skipped:** 1

| Check | Category | Status | Detail |
|---|---|---|---|
| BASE-001 | baseline | PASS | repository is a Git worktree |
| BASE-002 | baseline | PASS | CST-TT-04-v1 resolves to frozen base |
| BASE-003 | baseline | PASS | frozen base is ancestor of HEAD |
| BASE-004 | baseline | PASS | repository has no whitespace errors |
| BASE-005 | baseline | PASS | clean-tree check deferred until release verification |
| BASE-006 | baseline | PASS | phase tag absent before freeze or already resolves to HEAD |
| TOOL-001 | toolchain | PASS | Lean toolchain remains pinned |
| TOOL-PIN-01 | toolchain | PASS | pyproject contains >=3.13,<3.14 |
| TOOL-PIN-02 | toolchain | PASS | pyproject contains pytest==9.0.2 |
| TOOL-PIN-03 | toolchain | PASS | pyproject contains jsonschema==4.26.0 |
| TOOL-PIN-04 | toolchain | PASS | pyproject contains setuptools==82.0.1 |
| TOOL-PY | toolchain | PASS | Python 3.13 is running (3.13.5) |
| TOOL-STATUS-PHASE | toolchain | PASS | toolchain status is phase-current |
| TOOL-STATUS-LEAN | toolchain | PASS | Lean compile status is not overclaimed |
| TOOL-STATUS-PY | toolchain | PASS | Python certificates are checked |
| TOOL-LEAN-BUILD | toolchain | SKIP | lean/lake unavailable; no compilation pass claimed |
| PY-COUNT | python | PASS | at least sixty Python files are present (105) |
| PY-COMPILE-001 | python | PASS | scripts/build_exp01_assets.py compiles |
| PY-COMPILE-002 | python | PASS | scripts/build_exp02_assets.py compiles |
| PY-COMPILE-003 | python | PASS | scripts/build_exp03_assets.py compiles |
| PY-COMPILE-004 | python | PASS | scripts/build_exp04_assets.py compiles |
| PY-COMPILE-005 | python | PASS | scripts/build_exp05_assets.py compiles |
| PY-COMPILE-006 | python | PASS | scripts/build_exp06_assets.py compiles |
| PY-COMPILE-007 | python | PASS | scripts/build_tt00_assets.py compiles |
| PY-COMPILE-008 | python | PASS | scripts/build_tt01_assets.py compiles |
| PY-COMPILE-009 | python | PASS | scripts/build_tt02_assets.py compiles |
| PY-COMPILE-010 | python | PASS | scripts/build_tt03_assets.py compiles |
| PY-COMPILE-011 | python | PASS | scripts/build_tt04_assets.py compiles |
| PY-COMPILE-012 | python | PASS | scripts/build_tt05_assets.py compiles |
| PY-COMPILE-013 | python | PASS | scripts/enrich_exp01_assets.py compiles |
| PY-COMPILE-014 | python | PASS | scripts/exp02_supplemental.py compiles |
| PY-COMPILE-015 | python | PASS | scripts/exp03_data.py compiles |
| PY-COMPILE-016 | python | PASS | scripts/exp04_data.py compiles |
| PY-COMPILE-017 | python | PASS | scripts/exp05_data.py compiles |
| PY-COMPILE-018 | python | PASS | scripts/exp06_data.py compiles |
| PY-COMPILE-019 | python | PASS | scripts/extract_corpus.py compiles |
| PY-COMPILE-020 | python | PASS | scripts/finalize_exp02_manifest.py compiles |
| PY-COMPILE-021 | python | PASS | scripts/finalize_exp03_manifest.py compiles |
| PY-COMPILE-022 | python | PASS | scripts/finalize_exp04_manifest.py compiles |
| PY-COMPILE-023 | python | PASS | scripts/finalize_exp05_manifest.py compiles |
| PY-COMPILE-024 | python | PASS | scripts/finalize_exp06_manifest.py compiles |
| PY-COMPILE-025 | python | PASS | scripts/finalize_tt00_manifest.py compiles |
| PY-COMPILE-026 | python | PASS | scripts/finalize_tt01_manifest.py compiles |
| PY-COMPILE-027 | python | PASS | scripts/finalize_tt02_manifest.py compiles |
| PY-COMPILE-028 | python | PASS | scripts/finalize_tt03_manifest.py compiles |
| PY-COMPILE-029 | python | PASS | scripts/finalize_tt04_manifest.py compiles |
| PY-COMPILE-030 | python | PASS | scripts/finalize_tt05_manifest.py compiles |
| PY-COMPILE-031 | python | PASS | scripts/tt00_data.py compiles |
| PY-COMPILE-032 | python | PASS | scripts/tt02_data.py compiles |
| PY-COMPILE-033 | python | PASS | scripts/tt03_data.py compiles |
| PY-COMPILE-034 | python | PASS | scripts/tt04_data.py compiles |
| PY-COMPILE-035 | python | PASS | scripts/tt05_data.py compiles |
| PY-COMPILE-036 | python | PASS | scripts/validate_exp01.py compiles |
| PY-COMPILE-037 | python | PASS | scripts/validate_exp02.py compiles |
| PY-COMPILE-038 | python | PASS | scripts/validate_exp03.py compiles |
| PY-COMPILE-039 | python | PASS | scripts/validate_exp04.py compiles |
| PY-COMPILE-040 | python | PASS | scripts/validate_exp05.py compiles |
| PY-COMPILE-041 | python | PASS | scripts/validate_exp06.py compiles |
| PY-COMPILE-042 | python | PASS | scripts/validate_tt00.py compiles |
| PY-COMPILE-043 | python | PASS | scripts/validate_tt01.py compiles |
| PY-COMPILE-044 | python | PASS | scripts/validate_tt02.py compiles |
| PY-COMPILE-045 | python | PASS | scripts/validate_tt03.py compiles |
| PY-COMPILE-046 | python | PASS | scripts/validate_tt04.py compiles |
| PY-COMPILE-047 | python | PASS | scripts/validate_tt05.py compiles |
| PY-COMPILE-048 | python | PASS | scripts/verify_exp03_rebuild.py compiles |
| PY-COMPILE-049 | python | PASS | scripts/verify_exp04_rebuild.py compiles |
| PY-COMPILE-050 | python | PASS | scripts/verify_exp05_rebuild.py compiles |
| PY-COMPILE-051 | python | PASS | scripts/verify_exp06_rebuild.py compiles |
| PY-COMPILE-052 | python | PASS | scripts/verify_tt00_rebuild.py compiles |
| PY-COMPILE-053 | python | PASS | scripts/verify_tt01_rebuild.py compiles |
| PY-COMPILE-054 | python | PASS | scripts/verify_tt02_rebuild.py compiles |
| PY-COMPILE-055 | python | PASS | scripts/verify_tt03_rebuild.py compiles |
| PY-COMPILE-056 | python | PASS | scripts/verify_tt04_rebuild.py compiles |
| PY-COMPILE-057 | python | PASS | scripts/verify_tt05_rebuild.py compiles |
| PY-COMPILE-058 | python | PASS | src/cst_tt/__init__.py compiles |
| PY-COMPILE-059 | python | PASS | src/cst_tt/ancestry.py compiles |
| PY-COMPILE-060 | python | PASS | src/cst_tt/autonomy.py compiles |
| PY-COMPILE-061 | python | PASS | src/cst_tt/bridge_composition_checker.py compiles |
| PY-COMPILE-062 | python | PASS | src/cst_tt/circularity.py compiles |
| PY-COMPILE-063 | python | PASS | src/cst_tt/contracts.py compiles |
| PY-COMPILE-064 | python | PASS | src/cst_tt/corridor.py compiles |
| PY-COMPILE-065 | python | PASS | src/cst_tt/corridor_and_branch_checker.py compiles |
| PY-COMPILE-066 | python | PASS | src/cst_tt/countermodels.py compiles |
| PY-COMPILE-067 | python | PASS | src/cst_tt/fiach.py compiles |
| PY-COMPILE-068 | python | PASS | src/cst_tt/hashing.py compiles |
| PY-COMPILE-069 | python | PASS | src/cst_tt/package.py compiles |
| PY-COMPILE-070 | python | PASS | src/cst_tt/package_auditor.py compiles |
| PY-COMPILE-071 | python | PASS | src/cst_tt/package_gluing.py compiles |
| PY-COMPILE-072 | python | PASS | src/cst_tt/predicates.py compiles |
| PY-COMPILE-073 | python | PASS | src/cst_tt/registry.py compiles |
| PY-COMPILE-074 | python | PASS | src/cst_tt/targets.py compiles |
| PY-COMPILE-075 | python | PASS | src/cst_tt/temporal.py compiles |
| PY-COMPILE-076 | python | PASS | src/cst_tt/transport.py compiles |
| PY-COMPILE-077 | python | PASS | src/cst_tt/transport_auditor.py compiles |
| PY-COMPILE-078 | python | PASS | src/cst_tt/types.py compiles |
| PY-COMPILE-079 | python | PASS | src/cst_tt/withdrawal_autonomy_checker.py compiles |
| PY-COMPILE-080 | python | PASS | tests/test_autonomy_certificates.py compiles |
| PY-COMPILE-081 | python | PASS | tests/test_circularity_and_lean_surface.py compiles |
| PY-COMPILE-082 | python | PASS | tests/test_corridor_certificates.py compiles |
| PY-COMPILE-083 | python | PASS | tests/test_corridor_composition.py compiles |
| PY-COMPILE-084 | python | PASS | tests/test_corridor_searches.py compiles |
| PY-COMPILE-085 | python | PASS | tests/test_countermodel_certificates.py compiles |
| PY-COMPILE-086 | python | PASS | tests/test_countermodel_enumeration.py compiles |
| PY-COMPILE-087 | python | PASS | tests/test_direct_successor.py compiles |
| PY-COMPILE-088 | python | PASS | tests/test_fiach_certificate.py compiles |
| PY-COMPILE-089 | python | PASS | tests/test_generated_assets.py compiles |
| PY-COMPILE-090 | python | PASS | tests/test_package_certificates.py compiles |
| PY-COMPILE-091 | python | PASS | tests/test_package_gluing.py compiles |
| PY-COMPILE-092 | python | PASS | tests/test_phase01_boundaries.py compiles |
| PY-COMPILE-093 | python | PASS | tests/test_provenance_and_boundaries.py compiles |
| PY-COMPILE-094 | python | PASS | tests/test_python_types.py compiles |
| PY-COMPILE-095 | python | PASS | tests/test_registries.py compiles |
| PY-COMPILE-096 | python | PASS | tests/test_registry_schema.py compiles |
| PY-COMPILE-097 | python | PASS | tests/test_reproducibility_policy.py compiles |
| PY-COMPILE-098 | python | PASS | tests/test_route_memory_arrow.py compiles |
| PY-COMPILE-099 | python | PASS | tests/test_scaffold_boundaries.py compiles |
| PY-COMPILE-100 | python | PASS | tests/test_schema_examples.py compiles |
| PY-COMPILE-101 | python | PASS | tests/test_temporal_transport_certificates.py compiles |
| PY-COMPILE-102 | python | PASS | tests/test_transport_controls_and_search.py compiles |
| PY-COMPILE-103 | python | PASS | tests/test_tt03_formal_surfaces.py compiles |
| PY-COMPILE-104 | python | PASS | tests/test_tt04_formal_surfaces.py compiles |
| PY-COMPILE-105 | python | PASS | tests/test_tt05_formal_surfaces.py compiles |
| PY-TESTS | python | PASS | full pytest suite passes |
| PROV-TAG-01 | provenance | PASS | CST-TT-00-v1 resolves to frozen commit |
| PROV-TAG-02 | provenance | PASS | CST-TT-01-v1 resolves to frozen commit |
| PROV-TAG-03 | provenance | PASS | CST-TT-02-v1 resolves to frozen commit |
| PROV-TAG-04 | provenance | PASS | CST-TT-03-v1 resolves to frozen commit |
| PROV-TAG-05 | provenance | PASS | CST-TT-04-v1 resolves to frozen commit |
| PROV-INPUT-001 | provenance | PASS | imported surface inputs/normative/cst-tt-00/EXECUTION_PLAN.md is hash-bound |
| PROV-INPUT-002 | provenance | PASS | imported surface inputs/normative/cst-tt-00/FIACH_BASELINE_SPECIFICATION.md is hash-bound |
| PROV-INPUT-003 | provenance | PASS | imported surface inputs/normative/cst-tt-00/IAPS_BASELINE_SPECIFICATION.md is hash-bound |
| PROV-INPUT-004 | provenance | PASS | imported surface inputs/normative/cst-tt-00/TEMPORAL_AUDIT_ORIGINAL_SHA256SUMS.txt is hash-bound |
| PROV-INPUT-005 | provenance | PASS | imported surface inputs/normative/cst-tt-00/TEMPORAL_AUDIT_README.md is hash-bound |
| PROV-INPUT-006 | provenance | PASS | imported surface inputs/normative/cst-tt-00/TEMPORAL_SOURCE_MAP.md is hash-bound |
| PROV-INPUT-007 | provenance | PASS | imported surface inputs/normative/cst-tt-00/TEMPORAL_TRANSCENDENCE_AUDIT.md is hash-bound |
| PROV-INPUT-008 | provenance | PASS | imported surface inputs/reference_surfaces/temporal_audit/Tsiokos_2026_An_Audited_Closure_Architecture_for_Consciousness_Exact_Finite_Models_Structural_Theorems_and_Conditional_Realization.tex is hash-bound |
| PROV-INPUT-009 | provenance | PASS | imported surface inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Glass_Is_an_Unclosed_Layer_Kovacs_Memory_as_Predictive_Quotient_Residue.tex is hash-bound |
| PROV-INPUT-010 | provenance | PASS | imported surface inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex is hash-bound |
| PROV-INPUT-011 | provenance | PASS | imported surface inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex is hash-bound |
| PROV-INPUT-012 | provenance | PASS | imported surface inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_VI_A_Catalog_of_Dynamical_Structural_Laws.tex is hash-bound |
| PROV-INPUT-013 | provenance | PASS | imported surface inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Protocol_Trap_Holonomy_Without_Entropy_Production.tex is hash-bound |
| PROV-INPUT-014 | provenance | PASS | imported surface inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Flatten_a_Stone_with_Six_Birds_Critical_Pairs_Holonomy_and_Confluence_in_Rewriting_Systems.tex is hash-bound |
| PROV-INPUT-015 | provenance | PASS | imported surface inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Lay_a_Stone_with_Six_Birds_Finite_State_Semantics_for_Packaging_Directionality_and_Coarse_Graining.tex is hash-bound |
| PROV-INPUT-016 | provenance | PASS | imported surface inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex is hash-bound |
| PROV-INPUT-017 | provenance | PASS | imported surface inputs/source_archives/CST_temporal_transcendence_audit.zip is hash-bound |
| PROV-SOURCES | provenance | PASS | nine temporal SBT manuscripts are retained |
| SCHEMA-COUNT | schemas | PASS | twenty-six certificate schemas are present |
| EXAMPLE-COUNT | schemas | PASS | twenty-six scaffold examples are present |
| SCHEMA-REGISTRY-COUNT | schemas | PASS | schema registry has twenty-six rows |
| SCHEMA-FILE-01 | schemas | PASS | schema CS-01 exists |
| SCHEMA-EXAMPLE-01 | schemas | PASS | scaffold CS-01 exists |
| SCHEMA-VALID-01 | schemas | PASS | CS-01 schema and scaffold validate |
| SCHEMA-FILE-02 | schemas | PASS | schema CS-02 exists |
| SCHEMA-EXAMPLE-02 | schemas | PASS | scaffold CS-02 exists |
| SCHEMA-VALID-02 | schemas | PASS | CS-02 schema and scaffold validate |
| SCHEMA-FILE-03 | schemas | PASS | schema CS-03 exists |
| SCHEMA-EXAMPLE-03 | schemas | PASS | scaffold CS-03 exists |
| SCHEMA-VALID-03 | schemas | PASS | CS-03 schema and scaffold validate |
| SCHEMA-FILE-04 | schemas | PASS | schema CS-04 exists |
| SCHEMA-EXAMPLE-04 | schemas | PASS | scaffold CS-04 exists |
| SCHEMA-VALID-04 | schemas | PASS | CS-04 schema and scaffold validate |
| SCHEMA-FILE-05 | schemas | PASS | schema CS-05 exists |
| SCHEMA-EXAMPLE-05 | schemas | PASS | scaffold CS-05 exists |
| SCHEMA-VALID-05 | schemas | PASS | CS-05 schema and scaffold validate |
| SCHEMA-FILE-06 | schemas | PASS | schema CS-06 exists |
| SCHEMA-EXAMPLE-06 | schemas | PASS | scaffold CS-06 exists |
| SCHEMA-VALID-06 | schemas | PASS | CS-06 schema and scaffold validate |
| SCHEMA-FILE-07 | schemas | PASS | schema CS-07 exists |
| SCHEMA-EXAMPLE-07 | schemas | PASS | scaffold CS-07 exists |
| SCHEMA-VALID-07 | schemas | PASS | CS-07 schema and scaffold validate |
| SCHEMA-FILE-08 | schemas | PASS | schema CS-08 exists |
| SCHEMA-EXAMPLE-08 | schemas | PASS | scaffold CS-08 exists |
| SCHEMA-VALID-08 | schemas | PASS | CS-08 schema and scaffold validate |
| SCHEMA-FILE-09 | schemas | PASS | schema CS-09 exists |
| SCHEMA-EXAMPLE-09 | schemas | PASS | scaffold CS-09 exists |
| SCHEMA-VALID-09 | schemas | PASS | CS-09 schema and scaffold validate |
| SCHEMA-FILE-10 | schemas | PASS | schema CS-10 exists |
| SCHEMA-EXAMPLE-10 | schemas | PASS | scaffold CS-10 exists |
| SCHEMA-VALID-10 | schemas | PASS | CS-10 schema and scaffold validate |
| SCHEMA-FILE-11 | schemas | PASS | schema CS-11 exists |
| SCHEMA-EXAMPLE-11 | schemas | PASS | scaffold CS-11 exists |
| SCHEMA-VALID-11 | schemas | PASS | CS-11 schema and scaffold validate |
| SCHEMA-FILE-12 | schemas | PASS | schema CS-12 exists |
| SCHEMA-EXAMPLE-12 | schemas | PASS | scaffold CS-12 exists |
| SCHEMA-VALID-12 | schemas | PASS | CS-12 schema and scaffold validate |
| SCHEMA-FILE-13 | schemas | PASS | schema CS-13 exists |
| SCHEMA-EXAMPLE-13 | schemas | PASS | scaffold CS-13 exists |
| SCHEMA-VALID-13 | schemas | PASS | CS-13 schema and scaffold validate |
| SCHEMA-FILE-14 | schemas | PASS | schema CS-14 exists |
| SCHEMA-EXAMPLE-14 | schemas | PASS | scaffold CS-14 exists |
| SCHEMA-VALID-14 | schemas | PASS | CS-14 schema and scaffold validate |
| SCHEMA-FILE-15 | schemas | PASS | schema CS-15 exists |
| SCHEMA-EXAMPLE-15 | schemas | PASS | scaffold CS-15 exists |
| SCHEMA-VALID-15 | schemas | PASS | CS-15 schema and scaffold validate |
| SCHEMA-FILE-16 | schemas | PASS | schema CS-16 exists |
| SCHEMA-EXAMPLE-16 | schemas | PASS | scaffold CS-16 exists |
| SCHEMA-VALID-16 | schemas | PASS | CS-16 schema and scaffold validate |
| SCHEMA-FILE-17 | schemas | PASS | schema CS-17 exists |
| SCHEMA-EXAMPLE-17 | schemas | PASS | scaffold CS-17 exists |
| SCHEMA-VALID-17 | schemas | PASS | CS-17 schema and scaffold validate |
| SCHEMA-FILE-18 | schemas | PASS | schema CS-18 exists |
| SCHEMA-EXAMPLE-18 | schemas | PASS | scaffold CS-18 exists |
| SCHEMA-VALID-18 | schemas | PASS | CS-18 schema and scaffold validate |
| SCHEMA-FILE-19 | schemas | PASS | schema CS-19 exists |
| SCHEMA-EXAMPLE-19 | schemas | PASS | scaffold CS-19 exists |
| SCHEMA-VALID-19 | schemas | PASS | CS-19 schema and scaffold validate |
| SCHEMA-FILE-20 | schemas | PASS | schema CS-20 exists |
| SCHEMA-EXAMPLE-20 | schemas | PASS | scaffold CS-20 exists |
| SCHEMA-VALID-20 | schemas | PASS | CS-20 schema and scaffold validate |
| SCHEMA-FILE-21 | schemas | PASS | schema CS-21 exists |
| SCHEMA-EXAMPLE-21 | schemas | PASS | scaffold CS-21 exists |
| SCHEMA-VALID-21 | schemas | PASS | CS-21 schema and scaffold validate |
| SCHEMA-FILE-22 | schemas | PASS | schema CS-22 exists |
| SCHEMA-EXAMPLE-22 | schemas | PASS | scaffold CS-22 exists |
| SCHEMA-VALID-22 | schemas | PASS | CS-22 schema and scaffold validate |
| SCHEMA-FILE-23 | schemas | PASS | schema CS-23 exists |
| SCHEMA-EXAMPLE-23 | schemas | PASS | scaffold CS-23 exists |
| SCHEMA-VALID-23 | schemas | PASS | CS-23 schema and scaffold validate |
| SCHEMA-FILE-24 | schemas | PASS | schema CS-24 exists |
| SCHEMA-EXAMPLE-24 | schemas | PASS | scaffold CS-24 exists |
| SCHEMA-VALID-24 | schemas | PASS | CS-24 schema and scaffold validate |
| SCHEMA-FILE-25 | schemas | PASS | schema CS-25 exists |
| SCHEMA-EXAMPLE-25 | schemas | PASS | scaffold CS-25 exists |
| SCHEMA-VALID-25 | schemas | PASS | CS-25 schema and scaffold validate |
| SCHEMA-FILE-26 | schemas | PASS | schema CS-26 exists |
| SCHEMA-EXAMPLE-26 | schemas | PASS | scaffold CS-26 exists |
| SCHEMA-VALID-26 | schemas | PASS | CS-26 schema and scaffold validate |
| PKG-ALIGNED-COUNT | packages | PASS | two handoff-aligned package witnesses exist |
| PKG-FILES-01 | packages | PASS | PKG-POS-03-FIACH-SOURCE files exist |
| PKG-SCHEMA-01 | packages | PASS | PKG-POS-03-FIACH-SOURCE schema validates:  |
| PKG-HASH-01 | packages | PASS | PKG-POS-03-FIACH-SOURCE model hash binds |
| PKG-AUDIT-01 | packages | PASS | PKG-POS-03-FIACH-SOURCE package replay passes |
| PKG-ROUTE-01 | packages | PASS | PKG-POS-03-FIACH-SOURCE route frontier aligns |
| PKG-TICK-01 | packages | PASS | PKG-POS-03-FIACH-SOURCE tick frontier aligns |
| PKG-RECORD-01 | packages | PASS | PKG-POS-03-FIACH-SOURCE record frontier aligns |
| PKG-OWNER-01 | packages | PASS | PKG-POS-03-FIACH-SOURCE owner frontier aligns |
| PKG-FILES-02 | packages | PASS | PKG-POS-04-FIACH-TARGET files exist |
| PKG-SCHEMA-02 | packages | PASS | PKG-POS-04-FIACH-TARGET schema validates:  |
| PKG-HASH-02 | packages | PASS | PKG-POS-04-FIACH-TARGET model hash binds |
| PKG-AUDIT-02 | packages | PASS | PKG-POS-04-FIACH-TARGET package replay passes |
| PKG-ROUTE-02 | packages | PASS | PKG-POS-04-FIACH-TARGET route frontier aligns |
| PKG-TICK-02 | packages | PASS | PKG-POS-04-FIACH-TARGET tick frontier aligns |
| PKG-RECORD-02 | packages | PASS | PKG-POS-04-FIACH-TARGET record frontier aligns |
| PKG-OWNER-02 | packages | PASS | PKG-POS-04-FIACH-TARGET owner frontier aligns |
| PKG-STAGED-SCHEMA | packages | PASS | aligned staged certificate validates:  |
| PKG-STAGED-AUDIT | packages | PASS | aligned staged assembly replays |
| AUT-SCHEMA | autonomy | PASS | positive autonomy certificate validates:  |
| AUT-HASH | autonomy | PASS | autonomy model is hash-bound |
| AUT-VALID | autonomy | PASS | positive autonomy witness passes |
| AUT-REPLAY | autonomy | PASS | autonomy audit replays byte-semantically |
| AUT-OBL-01 | autonomy | PASS | autonomy obligation withdrawal passes |
| AUT-OBL-02 | autonomy | PASS | autonomy obligation retained-owner passes |
| AUT-OBL-03 | autonomy | PASS | autonomy obligation endpoint passes |
| AUT-OBL-04 | autonomy | PASS | autonomy obligation package passes |
| AUT-OBL-05 | autonomy | PASS | autonomy obligation resource-closure passes |
| AUT-OBL-06 | autonomy | PASS | autonomy obligation response passes |
| AUT-OBL-07 | autonomy | PASS | autonomy obligation anti-stall passes |
| AUT-OBL-08 | autonomy | PASS | autonomy obligation budget passes |
| AUT-OBL-09 | autonomy | PASS | autonomy obligation finite-horizon passes |
| AUT-OBL-10 | autonomy | PASS | autonomy obligation verdict-separation passes |
| AUT-WORDS | autonomy | PASS | all 127 finite disturbance words are checked |
| AUT-CONTROL-COUNT | autonomy | PASS | twelve autonomy controls exist |
| AUT-CONTROL-SCHEMA-01 | autonomy | PASS | AUT-C01 schema validates:  |
| AUT-CONTROL-FAIL-01 | autonomy | PASS | AUT-C01 fails expected obligation |
| AUT-CONTROL-REPLAY-01 | autonomy | PASS | AUT-C01 replay matches |
| AUT-CONTROL-HASH-01 | autonomy | PASS | AUT-C01 model hash binds |
| AUT-CONTROL-SCHEMA-02 | autonomy | PASS | AUT-C02 schema validates:  |
| AUT-CONTROL-FAIL-02 | autonomy | PASS | AUT-C02 fails expected obligation |
| AUT-CONTROL-REPLAY-02 | autonomy | PASS | AUT-C02 replay matches |
| AUT-CONTROL-HASH-02 | autonomy | PASS | AUT-C02 model hash binds |
| AUT-CONTROL-SCHEMA-03 | autonomy | PASS | AUT-C03 schema validates:  |
| AUT-CONTROL-FAIL-03 | autonomy | PASS | AUT-C03 fails expected obligation |
| AUT-CONTROL-REPLAY-03 | autonomy | PASS | AUT-C03 replay matches |
| AUT-CONTROL-HASH-03 | autonomy | PASS | AUT-C03 model hash binds |
| AUT-CONTROL-SCHEMA-04 | autonomy | PASS | AUT-C04 schema validates:  |
| AUT-CONTROL-FAIL-04 | autonomy | PASS | AUT-C04 fails expected obligation |
| AUT-CONTROL-REPLAY-04 | autonomy | PASS | AUT-C04 replay matches |
| AUT-CONTROL-HASH-04 | autonomy | PASS | AUT-C04 model hash binds |
| AUT-CONTROL-SCHEMA-05 | autonomy | PASS | AUT-C05 schema validates:  |
| AUT-CONTROL-FAIL-05 | autonomy | PASS | AUT-C05 fails expected obligation |
| AUT-CONTROL-REPLAY-05 | autonomy | PASS | AUT-C05 replay matches |
| AUT-CONTROL-HASH-05 | autonomy | PASS | AUT-C05 model hash binds |
| AUT-CONTROL-SCHEMA-06 | autonomy | PASS | AUT-C06 schema validates:  |
| AUT-CONTROL-FAIL-06 | autonomy | PASS | AUT-C06 fails expected obligation |
| AUT-CONTROL-REPLAY-06 | autonomy | PASS | AUT-C06 replay matches |
| AUT-CONTROL-HASH-06 | autonomy | PASS | AUT-C06 model hash binds |
| AUT-CONTROL-SCHEMA-07 | autonomy | PASS | AUT-C07 schema validates:  |
| AUT-CONTROL-FAIL-07 | autonomy | PASS | AUT-C07 fails expected obligation |
| AUT-CONTROL-REPLAY-07 | autonomy | PASS | AUT-C07 replay matches |
| AUT-CONTROL-HASH-07 | autonomy | PASS | AUT-C07 model hash binds |
| AUT-CONTROL-SCHEMA-08 | autonomy | PASS | AUT-C08 schema validates:  |
| AUT-CONTROL-FAIL-08 | autonomy | PASS | AUT-C08 fails expected obligation |
| AUT-CONTROL-REPLAY-08 | autonomy | PASS | AUT-C08 replay matches |
| AUT-CONTROL-HASH-08 | autonomy | PASS | AUT-C08 model hash binds |
| AUT-CONTROL-SCHEMA-09 | autonomy | PASS | AUT-C09 schema validates:  |
| AUT-CONTROL-FAIL-09 | autonomy | PASS | AUT-C09 fails expected obligation |
| AUT-CONTROL-REPLAY-09 | autonomy | PASS | AUT-C09 replay matches |
| AUT-CONTROL-HASH-09 | autonomy | PASS | AUT-C09 model hash binds |
| AUT-CONTROL-SCHEMA-10 | autonomy | PASS | AUT-C10 schema validates:  |
| AUT-CONTROL-FAIL-10 | autonomy | PASS | AUT-C10 fails expected obligation |
| AUT-CONTROL-REPLAY-10 | autonomy | PASS | AUT-C10 replay matches |
| AUT-CONTROL-HASH-10 | autonomy | PASS | AUT-C10 model hash binds |
| AUT-CONTROL-SCHEMA-11 | autonomy | PASS | AUT-C11 schema validates:  |
| AUT-CONTROL-FAIL-11 | autonomy | PASS | AUT-C11 fails expected obligation |
| AUT-CONTROL-REPLAY-11 | autonomy | PASS | AUT-C11 replay matches |
| AUT-CONTROL-HASH-11 | autonomy | PASS | AUT-C11 model hash binds |
| AUT-CONTROL-SCHEMA-12 | autonomy | PASS | AUT-C12 schema validates:  |
| AUT-CONTROL-FAIL-12 | autonomy | PASS | AUT-C12 fails expected obligation |
| AUT-CONTROL-REPLAY-12 | autonomy | PASS | AUT-C12 replay matches |
| AUT-CONTROL-HASH-12 | autonomy | PASS | AUT-C12 model hash binds |
| AUT-SEARCH-01 | autonomy | PASS | autonomy search field candidate_count reproduces |
| AUT-SEARCH-02 | autonomy | PASS | autonomy search field endpoint_autonomous_count reproduces |
| AUT-SEARCH-03 | autonomy | PASS | autonomy search field algorithm_bruteforce_mismatch_count reproduces |
| AUT-SEARCH-04 | autonomy | PASS | autonomy search field all_candidates_verified reproduces |
| AUT-SEARCH-ZERO | autonomy | PASS | 4,096-case fixed-point exhaustion has zero mismatches |
| FIACH-SCHEMA | fiach | PASS | positive FIACH certificate validates:  |
| FIACH-VALID | fiach | PASS | FIACH aggregate passes |
| FIACH-REPLAY | fiach | PASS | FIACH aggregate replay matches |
| FIACH-LANES | fiach | PASS | all four structural lanes are independently positive |
| FIACH-COMPONENT-01 | fiach | PASS | component autonomy replays |
| FIACH-COMPONENT-02 | fiach | PASS | component corridor replays |
| FIACH-COMPONENT-03 | fiach | PASS | component source_package replays |
| FIACH-COMPONENT-04 | fiach | PASS | component staged_assembly replays |
| FIACH-COMPONENT-05 | fiach | PASS | component target_package replays |
| FIACH-LINK-01 | fiach | PASS | FIACH linkage hashes passes |
| FIACH-LINK-02 | fiach | PASS | FIACH linkage distinct passes |
| FIACH-LINK-03 | fiach | PASS | FIACH linkage source passes |
| FIACH-LINK-04 | fiach | PASS | FIACH linkage target passes |
| FIACH-LINK-05 | fiach | PASS | FIACH linkage staged passes |
| FIACH-LINK-06 | fiach | PASS | FIACH linkage temporal-frontier passes |
| FIACH-LINK-07 | fiach | PASS | FIACH linkage handoff-event passes |
| FIACH-LINK-08 | fiach | PASS | FIACH linkage package-contract passes |
| FIACH-LINK-09 | fiach | PASS | FIACH linkage route passes |
| FIACH-LINK-10 | fiach | PASS | FIACH linkage recognition passes |
| FIACH-LINK-11 | fiach | PASS | FIACH linkage ontology passes |
| FIACH-CONTROL-COUNT | fiach | PASS | six one/two-lane controls exist |
| FIACH-CONTROL-SCHEMA-01 | fiach | PASS | FIACH-C01 schema validates:  |
| FIACH-CONTROL-PATTERN-01 | fiach | PASS | FIACH-C01 realizes only its declared lanes |
| FIACH-CONTROL-REPLAY-01 | fiach | PASS | FIACH-C01 replay matches |
| FIACH-CONTROL-SCHEMA-02 | fiach | PASS | FIACH-C02 schema validates:  |
| FIACH-CONTROL-PATTERN-02 | fiach | PASS | FIACH-C02 realizes only its declared lanes |
| FIACH-CONTROL-REPLAY-02 | fiach | PASS | FIACH-C02 replay matches |
| FIACH-CONTROL-SCHEMA-03 | fiach | PASS | FIACH-C03 schema validates:  |
| FIACH-CONTROL-PATTERN-03 | fiach | PASS | FIACH-C03 realizes only its declared lanes |
| FIACH-CONTROL-REPLAY-03 | fiach | PASS | FIACH-C03 replay matches |
| FIACH-CONTROL-SCHEMA-04 | fiach | PASS | FIACH-C04 schema validates:  |
| FIACH-CONTROL-PATTERN-04 | fiach | PASS | FIACH-C04 realizes only its declared lanes |
| FIACH-CONTROL-REPLAY-04 | fiach | PASS | FIACH-C04 replay matches |
| FIACH-CONTROL-SCHEMA-05 | fiach | PASS | FIACH-C05 schema validates:  |
| FIACH-CONTROL-PATTERN-05 | fiach | PASS | FIACH-C05 realizes only its declared lanes |
| FIACH-CONTROL-REPLAY-05 | fiach | PASS | FIACH-C05 replay matches |
| FIACH-CONTROL-SCHEMA-06 | fiach | PASS | FIACH-C06 schema validates:  |
| FIACH-CONTROL-PATTERN-06 | fiach | PASS | FIACH-C06 realizes only its declared lanes |
| FIACH-CONTROL-REPLAY-06 | fiach | PASS | FIACH-C06 replay matches |
| FIACH-PATTERNS | fiach | PASS | all one/two-lane patterns are represented |
| FIACH-TRUTH | fiach | PASS | eight-row exact conjunction table reproduces |
| REG-THEOREM-COUNT | registries | PASS | theorem registry retains 35 contracts |
| REG-THEOREM-UNIQUE | registries | PASS | theorem IDs are unique |
| REG-THEOREM-STATUS | registries | PASS | theorem status accounting is exact |
| REG-ADVANCED-01 | registries | PASS | TTH-05 advanced in CST-TT-05 |
| REG-ADVANCED-02 | registries | PASS | TTH-06 advanced in CST-TT-05 |
| REG-ADVANCED-03 | registries | PASS | TTN-06 advanced in CST-TT-05 |
| REG-DEF-COUNT | registries | PASS | definition registry has 69 rows |
| REG-DEF-UNIQUE | registries | PASS | definition IDs are unique |
| REG-TOY-COUNT | registries | PASS | toy registry retains 23 rows |
| REG-PKG-COUNT | registries | PASS | package registry has legacy and aligned witnesses |
| REG-PROJECT-01 | registries | PASS | project registry phase='CST-TT-05' |
| REG-PROJECT-02 | registries | PASS | project registry phase_base_tag='CST-TT-04-v1' |
| REG-PROJECT-03 | registries | PASS | project registry phase_base_commit='1884214d1bae82442f37fc9e6b013e222da89b1b' |
| REG-PROJECT-04 | registries | PASS | project registry checked_post_withdrawal_autonomy_certificates=1 |
| REG-PROJECT-05 | registries | PASS | project registry checked_autonomy_controls=12 |
| REG-PROJECT-06 | registries | PASS | project registry checked_temporal_fiach_certificates=1 |
| REG-PROJECT-07 | registries | PASS | project registry checked_fiach_lane_controls=6 |
| REG-PROJECT-08 | registries | PASS | project registry positive_handoff_witnesses=1 |
| REG-PROJECT-09 | registries | PASS | project registry fallback_unlocked=False |
| REG-PROJECT-10 | registries | PASS | project registry next_phase='CST-TT-06' |
| REG-KILL-FIACH | registries | PASS | positive witness prevents FIACH kill |
| REG-KILL-AUTO1 | registries | PASS | removed-resource autonomy kill is not triggered |
| REG-KILL-AUTO2 | registries | PASS | stall autonomy kill is not triggered |
| LEAN-FILE-01 | lean-static | PASS | CSTTT/Autonomy/FiniteAutonomy.lean is substantive |
| LEAN-PLACEHOLDER-01-01 | lean-static | PASS | FiniteAutonomy.lean contains no sorry |
| LEAN-PLACEHOLDER-01-02 | lean-static | PASS | FiniteAutonomy.lean contains no admit |
| LEAN-PLACEHOLDER-01-03 | lean-static | PASS | FiniteAutonomy.lean contains no axiom |
| LEAN-PLACEHOLDER-01-04 | lean-static | PASS | FiniteAutonomy.lean contains no unsafe |
| LEAN-NAMESPACE-01 | lean-static | PASS | FiniteAutonomy.lean namespace delimiters balance |
| LEAN-IMPORT-01 | lean-static | PASS | aggregate imports FiniteAutonomy.lean |
| LEAN-FILE-02 | lean-static | PASS | CSTTT/Targets/FiniteTemporalFIACH.lean is substantive |
| LEAN-PLACEHOLDER-02-01 | lean-static | PASS | FiniteTemporalFIACH.lean contains no sorry |
| LEAN-PLACEHOLDER-02-02 | lean-static | PASS | FiniteTemporalFIACH.lean contains no admit |
| LEAN-PLACEHOLDER-02-03 | lean-static | PASS | FiniteTemporalFIACH.lean contains no axiom |
| LEAN-PLACEHOLDER-02-04 | lean-static | PASS | FiniteTemporalFIACH.lean contains no unsafe |
| LEAN-NAMESPACE-02 | lean-static | PASS | FiniteTemporalFIACH.lean namespace delimiters balance |
| LEAN-IMPORT-02 | lean-static | PASS | aggregate imports FiniteTemporalFIACH.lean |
| LEAN-DECL-01 | lean-static | PASS | Lean declaration finiteHorizonRunExists exists |
| LEAN-DECL-02 | lean-static | PASS | Lean declaration postWithdrawalFiniteHorizonInvariance exists |
| LEAN-DECL-03 | lean-static | PASS | Lean declaration removedEssentialResourceExcludesAutonomy exists |
| LEAN-DECL-04 | lean-static | PASS | Lean declaration stalledOnlyResponsesExcludeAutonomy exists |
| LEAN-DECL-05 | lean-static | PASS | Lean declaration insolventOnlyResponsesExcludeAutonomy exists |
| LEAN-DECL-06 | lean-static | PASS | Lean declaration temporalFIACHCertificateSoundness exists |
| LEAN-DECL-07 | lean-static | PASS | Lean declaration temporalFIACHEndpointsLinked exists |
| LEAN-DECL-08 | lean-static | PASS | Lean declaration threeLaneAggregateExact exists |
| LEAN-LAYERING | lean-static | PASS | autonomy module precedes aggregate target module |
| BOUNDARY-DOC-01 | boundaries | PASS | POST_WITHDRAWAL_AUTONOMY.md states the consciousness nonclaim |
| BOUNDARY-DOC-02 | boundaries | PASS | INTEGRATED_TEMPORAL_FIACH_THEOREM.md states the consciousness nonclaim |
| BOUNDARY-DOC-03 | boundaries | PASS | PHASE_BOUNDARY.md states the consciousness nonclaim |
| BOUNDARY-DOC-04 | boundaries | PASS | CST-TT-05_COMPLETION_REPORT.md states the consciousness nonclaim |
| BOUNDARY-RECOGNITION | boundaries | PASS | recognition remains separate |
| BOUNDARY-ONTOLOGY | boundaries | PASS | ontology fields are absent |
| BOUNDARY-FALLBACK | boundaries | PASS | Temporal-IAPS remains locked |
| MANIFEST-PHASE | manifest | PASS | manifest phase is current |
| MANIFEST-COUNT | manifest | PASS | manifest lists 1176 files |
| MANIFEST-FILE-0001 | manifest | PASS | manifest row .gitignore verifies |
| MANIFEST-FILE-0002 | manifest | PASS | manifest row CHANGELOG.md verifies |
| MANIFEST-FILE-0003 | manifest | PASS | manifest row CSTTT.lean verifies |
| MANIFEST-FILE-0004 | manifest | PASS | manifest row CSTTT/Autonomy/FiniteAutonomy.lean verifies |
| MANIFEST-FILE-0005 | manifest | PASS | manifest row CSTTT/Autonomy/System.lean verifies |
| MANIFEST-FILE-0006 | manifest | PASS | manifest row CSTTT/Core/Carrier.lean verifies |
| MANIFEST-FILE-0007 | manifest | PASS | manifest row CSTTT/Core/Episode.lean verifies |
| MANIFEST-FILE-0008 | manifest | PASS | manifest row CSTTT/Core/Finite.lean verifies |
| MANIFEST-FILE-0009 | manifest | PASS | manifest row CSTTT/Corridor/Composition.lean verifies |
| MANIFEST-FILE-0010 | manifest | PASS | manifest row CSTTT/Corridor/DirectSuccessor.lean verifies |
| MANIFEST-FILE-0011 | manifest | PASS | manifest row CSTTT/Corridor/FiniteDirectSuccessor.lean verifies |
| MANIFEST-FILE-0012 | manifest | PASS | manifest row CSTTT/Corridor/FiniteTemporalCorridor.lean verifies |
| MANIFEST-FILE-0013 | manifest | PASS | manifest row CSTTT/Corridor/TemporalCorridor.lean verifies |
| MANIFEST-FILE-0014 | manifest | PASS | manifest row CSTTT/Countermodels/Kernel.lean verifies |
| MANIFEST-FILE-0015 | manifest | PASS | manifest row CSTTT/Fallback/Ancestry.lean verifies |
| MANIFEST-FILE-0016 | manifest | PASS | manifest row CSTTT/Package/Clauses.lean verifies |
| MANIFEST-FILE-0017 | manifest | PASS | manifest row CSTTT/Package/FiniteGluing.lean verifies |
| MANIFEST-FILE-0018 | manifest | PASS | manifest row CSTTT/Package/Gluing.lean verifies |
| MANIFEST-FILE-0019 | manifest | PASS | manifest row CSTTT/Package/TemporalPackage.lean verifies |
| MANIFEST-FILE-0020 | manifest | PASS | manifest row CSTTT/Prospects/Statements.lean verifies |
| MANIFEST-FILE-0021 | manifest | PASS | manifest row CSTTT/Targets/FiniteTemporalFIACH.lean verifies |
| MANIFEST-FILE-0022 | manifest | PASS | manifest row CSTTT/Targets/TemporalFIACH.lean verifies |
| MANIFEST-FILE-0023 | manifest | PASS | manifest row CSTTT/Temporal/Clock.lean verifies |
| MANIFEST-FILE-0024 | manifest | PASS | manifest row CSTTT/Temporal/Closure.lean verifies |
| MANIFEST-FILE-0025 | manifest | PASS | manifest row CSTTT/Temporal/Signature.lean verifies |
| MANIFEST-FILE-0026 | manifest | PASS | manifest row CSTTT/Transport/FiniteExamples.lean verifies |
| MANIFEST-FILE-0027 | manifest | PASS | manifest row CSTTT/Transport/FiniteTemporalTransport.lean verifies |
| MANIFEST-FILE-0028 | manifest | PASS | manifest row CSTTT/Transport/RecordArrow.lean verifies |
| MANIFEST-FILE-0029 | manifest | PASS | manifest row CSTTT/Transport/RouteDiscipline.lean verifies |
| MANIFEST-FILE-0030 | manifest | PASS | manifest row CSTTT/Transport/TemporalBridge.lean verifies |
| MANIFEST-FILE-0031 | manifest | PASS | manifest row README.md verifies |
| MANIFEST-FILE-0032 | manifest | PASS | manifest row RESTORE_AND_VERIFY.md verifies |
| MANIFEST-FILE-0033 | manifest | PASS | manifest row STATE.md verifies |
| MANIFEST-FILE-0034 | manifest | PASS | manifest row STATUS.md verifies |
| MANIFEST-FILE-0035 | manifest | PASS | manifest row candidates/BRIDGE_DESIGN_SPACE.md verifies |
| MANIFEST-FILE-0036 | manifest | PASS | manifest row candidates/CANDIDATE_COMPARISON_GUIDE.md verifies |
| MANIFEST-FILE-0037 | manifest | PASS | manifest row candidates/CANDIDATE_REGISTRY.json verifies |
| MANIFEST-FILE-0038 | manifest | PASS | manifest row candidates/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-FILE-0039 | manifest | PASS | manifest row candidates/INVARIANT_ATLAS.md verifies |
| MANIFEST-FILE-0040 | manifest | PASS | manifest row candidates/TRANSPORTED_OBJECT_ATLAS.md verifies |
| MANIFEST-FILE-0041 | manifest | PASS | manifest row candidates/brainstorms/01_quotient_algebraic.md verifies |
| MANIFEST-FILE-0042 | manifest | PASS | manifest row candidates/brainstorms/02_dynamical_process.md verifies |
| MANIFEST-FILE-0043 | manifest | PASS | manifest row candidates/brainstorms/03_error_correcting_logical_object.md verifies |
| MANIFEST-FILE-0044 | manifest | PASS | manifest row candidates/brainstorms/04_closure_realization.md verifies |
| MANIFEST-FILE-0045 | manifest | PASS | manifest row candidates/brainstorms/05_viability_agent.md verifies |
| MANIFEST-FILE-0046 | manifest | PASS | manifest row candidates/brainstorms/06_branching_philosophical.md verifies |
| MANIFEST-FILE-0047 | manifest | PASS | manifest row candidates/brainstorms/07_wild_hybrid.md verifies |
| MANIFEST-FILE-0048 | manifest | PASS | manifest row candidates/brainstorms/BRAINSTORM_FREEZE.sha256 verifies |
| MANIFEST-FILE-0049 | manifest | PASS | manifest row candidates/brainstorms/INDEX.md verifies |
| MANIFEST-FILE-0050 | manifest | PASS | manifest row candidates/bridge_registry.csv verifies |
| MANIFEST-FILE-0051 | manifest | PASS | manifest row candidates/bridges/.gitkeep verifies |
| MANIFEST-FILE-0052 | manifest | PASS | manifest row candidates/candidate_design_space.dot verifies |
| MANIFEST-FILE-0053 | manifest | PASS | manifest row candidates/candidate_design_space.png verifies |
| MANIFEST-FILE-0054 | manifest | PASS | manifest row candidates/candidate_design_space.svg verifies |
| MANIFEST-FILE-0055 | manifest | PASS | manifest row candidates/invariant_registry.csv verifies |
| MANIFEST-FILE-0056 | manifest | PASS | manifest row candidates/invariants/.gitkeep verifies |
| MANIFEST-FILE-0057 | manifest | PASS | manifest row candidates/target_schemas/.gitkeep verifies |
| MANIFEST-FILE-0058 | manifest | PASS | manifest row candidates/target_schemas/INDEX.md verifies |
| MANIFEST-FILE-0059 | manifest | PASS | manifest row candidates/target_schemas/TS-01.md verifies |
| MANIFEST-FILE-0060 | manifest | PASS | manifest row candidates/target_schemas/TS-02.md verifies |
| MANIFEST-FILE-0061 | manifest | PASS | manifest row candidates/target_schemas/TS-03.md verifies |
| MANIFEST-FILE-0062 | manifest | PASS | manifest row candidates/target_schemas/TS-04.md verifies |
| MANIFEST-FILE-0063 | manifest | PASS | manifest row candidates/target_schemas/TS-05.md verifies |
| MANIFEST-FILE-0064 | manifest | PASS | manifest row candidates/target_schemas/TS-06.md verifies |
| MANIFEST-FILE-0065 | manifest | PASS | manifest row candidates/target_schemas/TS-07.md verifies |
| MANIFEST-FILE-0066 | manifest | PASS | manifest row candidates/target_schemas/TS-08.md verifies |
| MANIFEST-FILE-0067 | manifest | PASS | manifest row candidates/target_schemas/TS-09.md verifies |
| MANIFEST-FILE-0068 | manifest | PASS | manifest row candidates/target_schemas/TS-10.md verifies |
| MANIFEST-FILE-0069 | manifest | PASS | manifest row candidates/transported_object_registry.csv verifies |
| MANIFEST-FILE-0070 | manifest | PASS | manifest row challenges/COUNTEREXAMPLE_CATALOG.md verifies |
| MANIFEST-FILE-0071 | manifest | PASS | manifest row challenges/CST-EXP-04_ADVERSARIAL_SYNTHESIS.md verifies |
| MANIFEST-FILE-0072 | manifest | PASS | manifest row challenges/INTERNAL_STRESS_SYNTHESIS.md verifies |
| MANIFEST-FILE-0073 | manifest | PASS | manifest row challenges/README.md verifies |
| MANIFEST-FILE-0074 | manifest | PASS | manifest row challenges/SURVIVOR_SHORTLIST.md verifies |
| MANIFEST-FILE-0075 | manifest | PASS | manifest row challenges/candidate_stress/INDEX.md verifies |
| MANIFEST-FILE-0076 | manifest | PASS | manifest row challenges/candidate_stress/TS-01.md verifies |
| MANIFEST-FILE-0077 | manifest | PASS | manifest row challenges/candidate_stress/TS-02.md verifies |
| MANIFEST-FILE-0078 | manifest | PASS | manifest row challenges/candidate_stress/TS-03.md verifies |
| MANIFEST-FILE-0079 | manifest | PASS | manifest row challenges/candidate_stress/TS-04.md verifies |
| MANIFEST-FILE-0080 | manifest | PASS | manifest row challenges/candidate_stress/TS-05.md verifies |
| MANIFEST-FILE-0081 | manifest | PASS | manifest row challenges/candidate_stress/TS-06.md verifies |
| MANIFEST-FILE-0082 | manifest | PASS | manifest row challenges/candidate_stress/TS-07.md verifies |
| MANIFEST-FILE-0083 | manifest | PASS | manifest row challenges/candidate_stress/TS-08.md verifies |
| MANIFEST-FILE-0084 | manifest | PASS | manifest row challenges/candidate_stress/TS-09.md verifies |
| MANIFEST-FILE-0085 | manifest | PASS | manifest row challenges/candidate_stress/TS-10.md verifies |
| MANIFEST-FILE-0086 | manifest | PASS | manifest row challenges/counterexamples/.gitkeep verifies |
| MANIFEST-FILE-0087 | manifest | PASS | manifest row challenges/counterexamples/HC-01.md verifies |
| MANIFEST-FILE-0088 | manifest | PASS | manifest row challenges/counterexamples/HC-02.md verifies |
| MANIFEST-FILE-0089 | manifest | PASS | manifest row challenges/counterexamples/HC-03.md verifies |
| MANIFEST-FILE-0090 | manifest | PASS | manifest row challenges/counterexamples/HC-04.md verifies |
| MANIFEST-FILE-0091 | manifest | PASS | manifest row challenges/counterexamples/HC-05.md verifies |
| MANIFEST-FILE-0092 | manifest | PASS | manifest row challenges/counterexamples/HC-06.md verifies |
| MANIFEST-FILE-0093 | manifest | PASS | manifest row challenges/counterexamples/HC-07.md verifies |
| MANIFEST-FILE-0094 | manifest | PASS | manifest row challenges/counterexamples/HC-08.md verifies |
| MANIFEST-FILE-0095 | manifest | PASS | manifest row challenges/counterexamples/HC-09.md verifies |
| MANIFEST-FILE-0096 | manifest | PASS | manifest row challenges/counterexamples/HC-10.md verifies |
| MANIFEST-FILE-0097 | manifest | PASS | manifest row challenges/counterexamples/HC-11.md verifies |
| MANIFEST-FILE-0098 | manifest | PASS | manifest row challenges/counterexamples/HC-12.md verifies |
| MANIFEST-FILE-0099 | manifest | PASS | manifest row challenges/counterexamples/HC-13.md verifies |
| MANIFEST-FILE-0100 | manifest | PASS | manifest row challenges/counterexamples/HC-14.md verifies |
| MANIFEST-FILE-0101 | manifest | PASS | manifest row challenges/counterexamples/HC-15.md verifies |
| MANIFEST-FILE-0102 | manifest | PASS | manifest row challenges/counterexamples/HC-16.md verifies |
| MANIFEST-FILE-0103 | manifest | PASS | manifest row challenges/counterexamples/HC-17.md verifies |
| MANIFEST-FILE-0104 | manifest | PASS | manifest row challenges/counterexamples/HC-18.md verifies |
| MANIFEST-FILE-0105 | manifest | PASS | manifest row challenges/external_literature/.gitkeep verifies |
| MANIFEST-FILE-0106 | manifest | PASS | manifest row challenges/external_literature/LITERATURE_CHALLENGE_MAP.md verifies |
| MANIFEST-FILE-0107 | manifest | PASS | manifest row challenges/external_literature/SEARCH_AND_SCOPE_LOG.md verifies |
| MANIFEST-FILE-0108 | manifest | PASS | manifest row challenges/external_literature/SOURCE_REGISTRY.csv verifies |
| MANIFEST-FILE-0109 | manifest | PASS | manifest row challenges/no_go_conjectures/.gitkeep verifies |
| MANIFEST-FILE-0110 | manifest | PASS | manifest row challenges/no_go_conjectures/INDEX.md verifies |
| MANIFEST-FILE-0111 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-01.md verifies |
| MANIFEST-FILE-0112 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-02.md verifies |
| MANIFEST-FILE-0113 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-03.md verifies |
| MANIFEST-FILE-0114 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-04.md verifies |
| MANIFEST-FILE-0115 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-05.md verifies |
| MANIFEST-FILE-0116 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-06.md verifies |
| MANIFEST-FILE-0117 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-07.md verifies |
| MANIFEST-FILE-0118 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-08.md verifies |
| MANIFEST-FILE-0119 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-09.md verifies |
| MANIFEST-FILE-0120 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-10.md verifies |
| MANIFEST-FILE-0121 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-11.md verifies |
| MANIFEST-FILE-0122 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-12.md verifies |
| MANIFEST-FILE-0123 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-13.md verifies |
| MANIFEST-FILE-0124 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-14.md verifies |
| MANIFEST-FILE-0125 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-15.md verifies |
| MANIFEST-FILE-0126 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-16.md verifies |
| MANIFEST-FILE-0127 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-17.md verifies |
| MANIFEST-FILE-0128 | manifest | PASS | manifest row challenges/no_go_conjectures/NG-18.md verifies |
| MANIFEST-FILE-0129 | manifest | PASS | manifest row challenges/red_team/INDEX.md verifies |
| MANIFEST-FILE-0130 | manifest | PASS | manifest row challenges/red_team/RT-01.md verifies |
| MANIFEST-FILE-0131 | manifest | PASS | manifest row challenges/red_team/RT-02.md verifies |
| MANIFEST-FILE-0132 | manifest | PASS | manifest row challenges/red_team/RT-03.md verifies |
| MANIFEST-FILE-0133 | manifest | PASS | manifest row challenges/red_team/RT-04.md verifies |
| MANIFEST-FILE-0134 | manifest | PASS | manifest row challenges/red_team/RT-05.md verifies |
| MANIFEST-FILE-0135 | manifest | PASS | manifest row challenges/red_team/RT-06.md verifies |
| MANIFEST-FILE-0136 | manifest | PASS | manifest row challenges/red_team/RT-07.md verifies |
| MANIFEST-FILE-0137 | manifest | PASS | manifest row challenges/survivor_architecture.dot verifies |
| MANIFEST-FILE-0138 | manifest | PASS | manifest row challenges/survivor_architecture.png verifies |
| MANIFEST-FILE-0139 | manifest | PASS | manifest row challenges/survivor_architecture.svg verifies |
| MANIFEST-FILE-0140 | manifest | PASS | manifest row changelog/.gitkeep verifies |
| MANIFEST-FILE-0141 | manifest | PASS | manifest row changelog/CST-EXP-00.md verifies |
| MANIFEST-FILE-0142 | manifest | PASS | manifest row changelog/CST-EXP-01.md verifies |
| MANIFEST-FILE-0143 | manifest | PASS | manifest row changelog/CST-EXP-02.md verifies |
| MANIFEST-FILE-0144 | manifest | PASS | manifest row changelog/CST-EXP-03.md verifies |
| MANIFEST-FILE-0145 | manifest | PASS | manifest row changelog/CST-EXP-05.md verifies |
| MANIFEST-FILE-0146 | manifest | PASS | manifest row changelog/CST-EXP-06.md verifies |
| MANIFEST-FILE-0147 | manifest | PASS | manifest row changelog/CST-TT-00.md verifies |
| MANIFEST-FILE-0148 | manifest | PASS | manifest row changelog/CST-TT-01.md verifies |
| MANIFEST-FILE-0149 | manifest | PASS | manifest row changelog/CST-TT-02.md verifies |
| MANIFEST-FILE-0150 | manifest | PASS | manifest row changelog/CST-TT-03.md verifies |
| MANIFEST-FILE-0151 | manifest | PASS | manifest row changelog/CST-TT-04.md verifies |
| MANIFEST-FILE-0152 | manifest | PASS | manifest row changelog/CST-TT-05.md verifies |
| MANIFEST-FILE-0153 | manifest | PASS | manifest row charter/.gitkeep verifies |
| MANIFEST-FILE-0154 | manifest | PASS | manifest row charter/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-FILE-0155 | manifest | PASS | manifest row charter/NONGOALS_AND_SCOPE_GUARDS.md verifies |
| MANIFEST-FILE-0156 | manifest | PASS | manifest row charter/PROJECT_CHARTER.md verifies |
| MANIFEST-FILE-0157 | manifest | PASS | manifest row charter/TYPED_PROBLEM_STATEMENT.md verifies |
| MANIFEST-FILE-0158 | manifest | PASS | manifest row config/REPRODUCIBILITY.json verifies |
| MANIFEST-FILE-0159 | manifest | PASS | manifest row corpus/README.md verifies |
| MANIFEST-FILE-0160 | manifest | PASS | manifest row corpus/asset_atlas/.gitkeep verifies |
| MANIFEST-FILE-0161 | manifest | PASS | manifest row corpus/asset_atlas/ASSET_ATLAS.md verifies |
| MANIFEST-FILE-0162 | manifest | PASS | manifest row corpus/asset_atlas/ASSET_PROVENANCE.md verifies |
| MANIFEST-FILE-0163 | manifest | PASS | manifest row corpus/asset_atlas/COMPOSITION_NOTES.md verifies |
| MANIFEST-FILE-0164 | manifest | PASS | manifest row corpus/asset_atlas/DEPENDENCY_GRAPH_GUIDE.md verifies |
| MANIFEST-FILE-0165 | manifest | PASS | manifest row corpus/asset_atlas/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-FILE-0166 | manifest | PASS | manifest row corpus/asset_atlas/LEXICAL_DEPENDENCY_METHOD.md verifies |
| MANIFEST-FILE-0167 | manifest | PASS | manifest row corpus/asset_atlas/PAPER_COVERAGE_AUDIT.md verifies |
| MANIFEST-FILE-0168 | manifest | PASS | manifest row corpus/asset_atlas/STATEMENT_SELECTION_METHOD.md verifies |
| MANIFEST-FILE-0169 | manifest | PASS | manifest row corpus/asset_atlas/dependency_graph.dot verifies |
| MANIFEST-FILE-0170 | manifest | PASS | manifest row corpus/asset_atlas/dependency_graph.mmd verifies |
| MANIFEST-FILE-0171 | manifest | PASS | manifest row corpus/asset_atlas/dependency_graph.png verifies |
| MANIFEST-FILE-0172 | manifest | PASS | manifest row corpus/asset_atlas/dependency_graph.svg verifies |
| MANIFEST-FILE-0173 | manifest | PASS | manifest row corpus/asset_atlas/dependency_graph_edges.csv verifies |
| MANIFEST-FILE-0174 | manifest | PASS | manifest row corpus/asset_atlas/dependency_graph_nodes.csv verifies |
| MANIFEST-FILE-0175 | manifest | PASS | manifest row corpus/clause_cards/C1.md verifies |
| MANIFEST-FILE-0176 | manifest | PASS | manifest row corpus/clause_cards/C2.md verifies |
| MANIFEST-FILE-0177 | manifest | PASS | manifest row corpus/clause_cards/C3.md verifies |
| MANIFEST-FILE-0178 | manifest | PASS | manifest row corpus/clause_cards/C4.md verifies |
| MANIFEST-FILE-0179 | manifest | PASS | manifest row corpus/clause_cards/C5.md verifies |
| MANIFEST-FILE-0180 | manifest | PASS | manifest row corpus/clause_cards/C6.md verifies |
| MANIFEST-FILE-0181 | manifest | PASS | manifest row corpus/clause_cards/C7.md verifies |
| MANIFEST-FILE-0182 | manifest | PASS | manifest row corpus/clause_cards/C8.md verifies |
| MANIFEST-FILE-0183 | manifest | PASS | manifest row corpus/clause_cards/INDEX.md verifies |
| MANIFEST-FILE-0184 | manifest | PASS | manifest row corpus/consciousness_repo/ASSET_MAP.md verifies |
| MANIFEST-FILE-0185 | manifest | PASS | manifest row corpus/consciousness_repo/VERIFICATION.md verifies |
| MANIFEST-FILE-0186 | manifest | PASS | manifest row corpus/consciousness_repo/consciousness_repo_inventory.csv verifies |
| MANIFEST-FILE-0187 | manifest | PASS | manifest row corpus/consciousness_repo/formal_inventory.csv verifies |
| MANIFEST-FILE-0188 | manifest | PASS | manifest row corpus/consciousness_repo/test_inventory.csv verifies |
| MANIFEST-FILE-0189 | manifest | PASS | manifest row corpus/machine_index/README.md verifies |
| MANIFEST-FILE-0190 | manifest | PASS | manifest row corpus/machine_index/all_statement_index.csv verifies |
| MANIFEST-FILE-0191 | manifest | PASS | manifest row corpus/machine_index/paper_inventory.csv verifies |
| MANIFEST-FILE-0192 | manifest | PASS | manifest row corpus/paper_cards/.gitkeep verifies |
| MANIFEST-FILE-0193 | manifest | PASS | manifest row corpus/paper_cards/INDEX.csv verifies |
| MANIFEST-FILE-0194 | manifest | PASS | manifest row corpus/paper_cards/INDEX.md verifies |
| MANIFEST-FILE-0195 | manifest | PASS | manifest row corpus/paper_cards/P01.md verifies |
| MANIFEST-FILE-0196 | manifest | PASS | manifest row corpus/paper_cards/P02.md verifies |
| MANIFEST-FILE-0197 | manifest | PASS | manifest row corpus/paper_cards/P03.md verifies |
| MANIFEST-FILE-0198 | manifest | PASS | manifest row corpus/paper_cards/P04.md verifies |
| MANIFEST-FILE-0199 | manifest | PASS | manifest row corpus/paper_cards/P05.md verifies |
| MANIFEST-FILE-0200 | manifest | PASS | manifest row corpus/paper_cards/P06.md verifies |
| MANIFEST-FILE-0201 | manifest | PASS | manifest row corpus/paper_cards/P07.md verifies |
| MANIFEST-FILE-0202 | manifest | PASS | manifest row corpus/paper_cards/P08.md verifies |
| MANIFEST-FILE-0203 | manifest | PASS | manifest row corpus/paper_cards/P09.md verifies |
| MANIFEST-FILE-0204 | manifest | PASS | manifest row corpus/paper_cards/P10.md verifies |
| MANIFEST-FILE-0205 | manifest | PASS | manifest row corpus/paper_cards/P11.md verifies |
| MANIFEST-FILE-0206 | manifest | PASS | manifest row corpus/paper_cards/P12.md verifies |
| MANIFEST-FILE-0207 | manifest | PASS | manifest row corpus/paper_cards/P13.md verifies |
| MANIFEST-FILE-0208 | manifest | PASS | manifest row corpus/paper_cards/P14.md verifies |
| MANIFEST-FILE-0209 | manifest | PASS | manifest row corpus/paper_cards/P15.md verifies |
| MANIFEST-FILE-0210 | manifest | PASS | manifest row corpus/paper_cards/P16.md verifies |
| MANIFEST-FILE-0211 | manifest | PASS | manifest row corpus/paper_cards/P17.md verifies |
| MANIFEST-FILE-0212 | manifest | PASS | manifest row corpus/paper_cards/P18.md verifies |
| MANIFEST-FILE-0213 | manifest | PASS | manifest row corpus/paper_cards/P19.md verifies |
| MANIFEST-FILE-0214 | manifest | PASS | manifest row corpus/paper_cards/P20.md verifies |
| MANIFEST-FILE-0215 | manifest | PASS | manifest row corpus/paper_cards/P21.md verifies |
| MANIFEST-FILE-0216 | manifest | PASS | manifest row corpus/paper_cards/P22.md verifies |
| MANIFEST-FILE-0217 | manifest | PASS | manifest row corpus/paper_cards/P23.md verifies |
| MANIFEST-FILE-0218 | manifest | PASS | manifest row corpus/paper_cards/P24.md verifies |
| MANIFEST-FILE-0219 | manifest | PASS | manifest row corpus/paper_cards/P25.md verifies |
| MANIFEST-FILE-0220 | manifest | PASS | manifest row corpus/paper_cards/P26.md verifies |
| MANIFEST-FILE-0221 | manifest | PASS | manifest row corpus/paper_cards/P27.md verifies |
| MANIFEST-FILE-0222 | manifest | PASS | manifest row corpus/paper_cards/P28.md verifies |
| MANIFEST-FILE-0223 | manifest | PASS | manifest row corpus/paper_cards/P29.md verifies |
| MANIFEST-FILE-0224 | manifest | PASS | manifest row corpus/paper_cards/P30.md verifies |
| MANIFEST-FILE-0225 | manifest | PASS | manifest row corpus/paper_cards/P31.md verifies |
| MANIFEST-FILE-0226 | manifest | PASS | manifest row corpus/paper_cards/P32.md verifies |
| MANIFEST-FILE-0227 | manifest | PASS | manifest row corpus/paper_cards/P33.md verifies |
| MANIFEST-FILE-0228 | manifest | PASS | manifest row corpus/paper_cards/P34.md verifies |
| MANIFEST-FILE-0229 | manifest | PASS | manifest row corpus/paper_cards/P35.md verifies |
| MANIFEST-FILE-0230 | manifest | PASS | manifest row corpus/paper_cards/P36.md verifies |
| MANIFEST-FILE-0231 | manifest | PASS | manifest row corpus/paper_cards/P37.md verifies |
| MANIFEST-FILE-0232 | manifest | PASS | manifest row corpus/paper_cards/P38.md verifies |
| MANIFEST-FILE-0233 | manifest | PASS | manifest row corpus/paper_cards/P39.md verifies |
| MANIFEST-FILE-0234 | manifest | PASS | manifest row corpus/paper_cards/P40.md verifies |
| MANIFEST-FILE-0235 | manifest | PASS | manifest row corpus/paper_cards/P41.md verifies |
| MANIFEST-FILE-0236 | manifest | PASS | manifest row corpus/paper_cards/P42.md verifies |
| MANIFEST-FILE-0237 | manifest | PASS | manifest row corpus/paper_cards/P43.md verifies |
| MANIFEST-FILE-0238 | manifest | PASS | manifest row corpus/paper_cards/P44.md verifies |
| MANIFEST-FILE-0239 | manifest | PASS | manifest row corpus/paper_cards/P45.md verifies |
| MANIFEST-FILE-0240 | manifest | PASS | manifest row corpus/paper_cards/P46.md verifies |
| MANIFEST-FILE-0241 | manifest | PASS | manifest row corpus/paper_cards/P47.md verifies |
| MANIFEST-FILE-0242 | manifest | PASS | manifest row corpus/paper_cards/P48.md verifies |
| MANIFEST-FILE-0243 | manifest | PASS | manifest row corpus/paper_cards/P49.md verifies |
| MANIFEST-FILE-0244 | manifest | PASS | manifest row corpus/paper_cards/P50.md verifies |
| MANIFEST-FILE-0245 | manifest | PASS | manifest row corpus/paper_cards/P51.md verifies |
| MANIFEST-FILE-0246 | manifest | PASS | manifest row corpus/paper_cards/P52.md verifies |
| MANIFEST-FILE-0247 | manifest | PASS | manifest row corpus/paper_cards/P53.md verifies |
| MANIFEST-FILE-0248 | manifest | PASS | manifest row corpus/paper_cards/P54.md verifies |
| MANIFEST-FILE-0249 | manifest | PASS | manifest row corpus/paper_cards/P55.md verifies |
| MANIFEST-FILE-0250 | manifest | PASS | manifest row corpus/paper_cards/P56.md verifies |
| MANIFEST-FILE-0251 | manifest | PASS | manifest row corpus/paper_cards/P57.md verifies |
| MANIFEST-FILE-0252 | manifest | PASS | manifest row corpus/paper_cards/P58.md verifies |
| MANIFEST-FILE-0253 | manifest | PASS | manifest row corpus/paper_cards/P59.md verifies |
| MANIFEST-FILE-0254 | manifest | PASS | manifest row corpus/paper_cards/P60.md verifies |
| MANIFEST-FILE-0255 | manifest | PASS | manifest row corpus/theorem_cards/.gitkeep verifies |
| MANIFEST-FILE-0256 | manifest | PASS | manifest row corpus/theorem_cards/INDEX.md verifies |
| MANIFEST-FILE-0257 | manifest | PASS | manifest row corpus/theorem_cards/P06-AOR.md verifies |
| MANIFEST-FILE-0258 | manifest | PASS | manifest row corpus/theorem_cards/P14-PT.md verifies |
| MANIFEST-FILE-0259 | manifest | PASS | manifest row corpus/theorem_cards/P18-RE.md verifies |
| MANIFEST-FILE-0260 | manifest | PASS | manifest row corpus/theorem_cards/P30-F19.md verifies |
| MANIFEST-FILE-0261 | manifest | PASS | manifest row corpus/theorem_cards/P44-CD.md verifies |
| MANIFEST-FILE-0262 | manifest | PASS | manifest row corpus/theorem_cards/P50-CF.md verifies |
| MANIFEST-FILE-0263 | manifest | PASS | manifest row corpus/theorem_cards/P52-NS.md verifies |
| MANIFEST-FILE-0264 | manifest | PASS | manifest row corpus/theorem_cards/T01.md verifies |
| MANIFEST-FILE-0265 | manifest | PASS | manifest row corpus/theorem_cards/T02.md verifies |
| MANIFEST-FILE-0266 | manifest | PASS | manifest row corpus/theorem_cards/T03.md verifies |
| MANIFEST-FILE-0267 | manifest | PASS | manifest row corpus/theorem_cards/T04.md verifies |
| MANIFEST-FILE-0268 | manifest | PASS | manifest row corpus/theorem_cards/T05.md verifies |
| MANIFEST-FILE-0269 | manifest | PASS | manifest row corpus/theorem_cards/T06.md verifies |
| MANIFEST-FILE-0270 | manifest | PASS | manifest row corpus/theorem_cards/T07.md verifies |
| MANIFEST-FILE-0271 | manifest | PASS | manifest row corpus/theorem_cards/T08.md verifies |
| MANIFEST-FILE-0272 | manifest | PASS | manifest row corpus/theorem_cards/T09.md verifies |
| MANIFEST-FILE-0273 | manifest | PASS | manifest row corpus/theorem_cards/T10.md verifies |
| MANIFEST-FILE-0274 | manifest | PASS | manifest row corpus/theorem_cards/T11.md verifies |
| MANIFEST-FILE-0275 | manifest | PASS | manifest row corpus/theorem_cards/T12.md verifies |
| MANIFEST-FILE-0276 | manifest | PASS | manifest row corpus/theorem_cards/T13.md verifies |
| MANIFEST-FILE-0277 | manifest | PASS | manifest row corpus/theorem_cards/T14.md verifies |
| MANIFEST-FILE-0278 | manifest | PASS | manifest row corpus/theorem_cards/T15.md verifies |
| MANIFEST-FILE-0279 | manifest | PASS | manifest row corpus/theorem_cards/T16.md verifies |
| MANIFEST-FILE-0280 | manifest | PASS | manifest row corpus/theorem_cards/T17.md verifies |
| MANIFEST-FILE-0281 | manifest | PASS | manifest row corpus/theorem_cards/T18.md verifies |
| MANIFEST-FILE-0282 | manifest | PASS | manifest row docs/ACYCLIC_GLUING_THEOREM.md verifies |
| MANIFEST-FILE-0283 | manifest | PASS | manifest row docs/ASSUMPTION_AND_CLAIM_CEILING.md verifies |
| MANIFEST-FILE-0284 | manifest | PASS | manifest row docs/AUTONOMY_CONTROL_SUITE.md verifies |
| MANIFEST-FILE-0285 | manifest | PASS | manifest row docs/C6_TEMPORAL_SUBSTANCE.md verifies |
| MANIFEST-FILE-0286 | manifest | PASS | manifest row docs/CIRCULARITY_AND_TYPING_POLICY.md verifies |
| MANIFEST-FILE-0287 | manifest | PASS | manifest row docs/CORRIDOR_COMPOSITION_THEOREM.md verifies |
| MANIFEST-FILE-0288 | manifest | PASS | manifest row docs/CORRIDOR_CONTROL_SUITE.md verifies |
| MANIFEST-FILE-0289 | manifest | PASS | manifest row docs/COUNTERMODEL_MINIMALITY.md verifies |
| MANIFEST-FILE-0290 | manifest | PASS | manifest row docs/CST-TT-04_DECISION_GATE.md verifies |
| MANIFEST-FILE-0291 | manifest | PASS | manifest row docs/CST-TT-05_DECISION_GATE.md verifies |
| MANIFEST-FILE-0292 | manifest | PASS | manifest row docs/DIRECT_SUCCESSOR_RESULT.md verifies |
| MANIFEST-FILE-0293 | manifest | PASS | manifest row docs/FINITE_HORIZON_LIVENESS_BOUNDARY.md verifies |
| MANIFEST-FILE-0294 | manifest | PASS | manifest row docs/FORMALIZATION_CONTRACT.md verifies |
| MANIFEST-FILE-0295 | manifest | PASS | manifest row docs/HANDOFF_ALIGNED_PACKAGE.md verifies |
| MANIFEST-FILE-0296 | manifest | PASS | manifest row docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md verifies |
| MANIFEST-FILE-0297 | manifest | PASS | manifest row docs/INTEGRATED_PACKAGE_SEMANTICS.md verifies |
| MANIFEST-FILE-0298 | manifest | PASS | manifest row docs/INTEGRATED_TEMPORAL_FIACH_THEOREM.md verifies |
| MANIFEST-FILE-0299 | manifest | PASS | manifest row docs/LANE_INDEPENDENCE_AUDIT.md verifies |
| MANIFEST-FILE-0300 | manifest | PASS | manifest row docs/MEMORY_OR_FLATNESS_THEOREM.md verifies |
| MANIFEST-FILE-0301 | manifest | PASS | manifest row docs/NEGATIVE_KERNEL.md verifies |
| MANIFEST-FILE-0302 | manifest | PASS | manifest row docs/NONREDUNDANCY_INTERVENTION_AUDIT.md verifies |
| MANIFEST-FILE-0303 | manifest | PASS | manifest row docs/OVERLAP_DIRECT_SUCCESSOR_COMPARISON.md verifies |
| MANIFEST-FILE-0304 | manifest | PASS | manifest row docs/PACKAGE_CONTROL_SUITE.md verifies |
| MANIFEST-FILE-0305 | manifest | PASS | manifest row docs/PHASE_BOUNDARY.md verifies |
| MANIFEST-FILE-0306 | manifest | PASS | manifest row docs/POST_WITHDRAWAL_AUTONOMY.md verifies |
| MANIFEST-FILE-0307 | manifest | PASS | manifest row docs/RECORD_ARROW_TRANSPORT.md verifies |
| MANIFEST-FILE-0308 | manifest | PASS | manifest row docs/RESTORE_AND_BUILD.md verifies |
| MANIFEST-FILE-0309 | manifest | PASS | manifest row docs/ROUTE_DISCIPLINE_AND_CONFLUENCE.md verifies |
| MANIFEST-FILE-0310 | manifest | PASS | manifest row docs/STAGED_PACKAGE_ASSEMBLY.md verifies |
| MANIFEST-FILE-0311 | manifest | PASS | manifest row docs/TARGET_FREEZE.md verifies |
| MANIFEST-FILE-0312 | manifest | PASS | manifest row docs/TEMPORAL_AMENDMENT_MAP.md verifies |
| MANIFEST-FILE-0313 | manifest | PASS | manifest row docs/TEMPORAL_CORRIDOR_SEMANTICS.md verifies |
| MANIFEST-FILE-0314 | manifest | PASS | manifest row docs/THEOREM_AND_TOY_REGISTRY.md verifies |
| MANIFEST-FILE-0315 | manifest | PASS | manifest row docs/TRANSPORT_CONTROL_SUITE.md verifies |
| MANIFEST-FILE-0316 | manifest | PASS | manifest row examples/scaffold/aligned_package_certificate.scaffold.json verifies |
| MANIFEST-FILE-0317 | manifest | PASS | manifest row examples/scaffold/aligned_staged_package_certificate.scaffold.json verifies |
| MANIFEST-FILE-0318 | manifest | PASS | manifest row examples/scaffold/ancestry_certificate.scaffold.json verifies |
| MANIFEST-FILE-0319 | manifest | PASS | manifest row examples/scaffold/autonomy_certificate.scaffold.json verifies |
| MANIFEST-FILE-0320 | manifest | PASS | manifest row examples/scaffold/autonomy_control_certificate.scaffold.json verifies |
| MANIFEST-FILE-0321 | manifest | PASS | manifest row examples/scaffold/corridor_composition_certificate.scaffold.json verifies |
| MANIFEST-FILE-0322 | manifest | PASS | manifest row examples/scaffold/corridor_control_certificate.scaffold.json verifies |
| MANIFEST-FILE-0323 | manifest | PASS | manifest row examples/scaffold/countermodel_certificate.scaffold.json verifies |
| MANIFEST-FILE-0324 | manifest | PASS | manifest row examples/scaffold/direct_successor.scaffold.json verifies |
| MANIFEST-FILE-0325 | manifest | PASS | manifest row examples/scaffold/direct_successor_landed.scaffold.json verifies |
| MANIFEST-FILE-0326 | manifest | PASS | manifest row examples/scaffold/direct_successor_path_certificate.scaffold.json verifies |
| MANIFEST-FILE-0327 | manifest | PASS | manifest row examples/scaffold/fiach_lane_control_certificate.scaffold.json verifies |
| MANIFEST-FILE-0328 | manifest | PASS | manifest row examples/scaffold/memory_repair_certificate.scaffold.json verifies |
| MANIFEST-FILE-0329 | manifest | PASS | manifest row examples/scaffold/package_certificate.scaffold.json verifies |
| MANIFEST-FILE-0330 | manifest | PASS | manifest row examples/scaffold/package_control_certificate.scaffold.json verifies |
| MANIFEST-FILE-0331 | manifest | PASS | manifest row examples/scaffold/post_withdrawal_autonomy_certificate.scaffold.json verifies |
| MANIFEST-FILE-0332 | manifest | PASS | manifest row examples/scaffold/record_arrow_certificate.scaffold.json verifies |
| MANIFEST-FILE-0333 | manifest | PASS | manifest row examples/scaffold/route_discipline_certificate.scaffold.json verifies |
| MANIFEST-FILE-0334 | manifest | PASS | manifest row examples/scaffold/staged_package_certificate.scaffold.json verifies |
| MANIFEST-FILE-0335 | manifest | PASS | manifest row examples/scaffold/strict_temporal_corridor_certificate.scaffold.json verifies |
| MANIFEST-FILE-0336 | manifest | PASS | manifest row examples/scaffold/temporal_corridor.scaffold.json verifies |
| MANIFEST-FILE-0337 | manifest | PASS | manifest row examples/scaffold/temporal_fiach_certificate.scaffold.json verifies |
| MANIFEST-FILE-0338 | manifest | PASS | manifest row examples/scaffold/temporal_fiach_landed_certificate.scaffold.json verifies |
| MANIFEST-FILE-0339 | manifest | PASS | manifest row examples/scaffold/temporal_signature.scaffold.json verifies |
| MANIFEST-FILE-0340 | manifest | PASS | manifest row examples/scaffold/temporal_transport_certificate.scaffold.json verifies |
| MANIFEST-FILE-0341 | manifest | PASS | manifest row examples/scaffold/transport_control_certificate.scaffold.json verifies |
| MANIFEST-FILE-0342 | manifest | PASS | manifest row feasibility/ASSUMPTION_LADDER.md verifies |
| MANIFEST-FILE-0343 | manifest | PASS | manifest row feasibility/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-FILE-0344 | manifest | PASS | manifest row feasibility/FINITE_CORE_SEMANTICS.md verifies |
| MANIFEST-FILE-0345 | manifest | PASS | manifest row feasibility/FORMALIZATION_TRACTABILITY.md verifies |
| MANIFEST-FILE-0346 | manifest | PASS | manifest row feasibility/LANDING_BUNDLES.md verifies |
| MANIFEST-FILE-0347 | manifest | PASS | manifest row feasibility/MODEL_SUITE.md verifies |
| MANIFEST-FILE-0348 | manifest | PASS | manifest row feasibility/README.md verifies |
| MANIFEST-FILE-0349 | manifest | PASS | manifest row feasibility/RECONNAISSANCE_SYNTHESIS.md verifies |
| MANIFEST-FILE-0350 | manifest | PASS | manifest row feasibility/landing_architecture.dot verifies |
| MANIFEST-FILE-0351 | manifest | PASS | manifest row feasibility/landing_architecture.png verifies |
| MANIFEST-FILE-0352 | manifest | PASS | manifest row feasibility/landing_architecture.svg verifies |
| MANIFEST-FILE-0353 | manifest | PASS | manifest row feasibility/model_cards/MF-01.md verifies |
| MANIFEST-FILE-0354 | manifest | PASS | manifest row feasibility/model_cards/MF-02.md verifies |
| MANIFEST-FILE-0355 | manifest | PASS | manifest row feasibility/model_cards/MF-03.md verifies |
| MANIFEST-FILE-0356 | manifest | PASS | manifest row feasibility/model_cards/MF-04.md verifies |
| MANIFEST-FILE-0357 | manifest | PASS | manifest row feasibility/model_cards/MF-05.md verifies |
| MANIFEST-FILE-0358 | manifest | PASS | manifest row feasibility/model_cards/MF-06.md verifies |
| MANIFEST-FILE-0359 | manifest | PASS | manifest row feasibility/model_cards/MF-07.md verifies |
| MANIFEST-FILE-0360 | manifest | PASS | manifest row feasibility/model_cards/MF-08.md verifies |
| MANIFEST-FILE-0361 | manifest | PASS | manifest row feasibility/model_cards/MF-09.md verifies |
| MANIFEST-FILE-0362 | manifest | PASS | manifest row feasibility/model_cards/MF-10.md verifies |
| MANIFEST-FILE-0363 | manifest | PASS | manifest row feasibility/theorem_prospectus/.gitkeep verifies |
| MANIFEST-FILE-0364 | manifest | PASS | manifest row feasibility/theorem_prospectus/INDEX.md verifies |
| MANIFEST-FILE-0365 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-01.md verifies |
| MANIFEST-FILE-0366 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-02.md verifies |
| MANIFEST-FILE-0367 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-03.md verifies |
| MANIFEST-FILE-0368 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-04.md verifies |
| MANIFEST-FILE-0369 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-05.md verifies |
| MANIFEST-FILE-0370 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-06.md verifies |
| MANIFEST-FILE-0371 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-07.md verifies |
| MANIFEST-FILE-0372 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-08.md verifies |
| MANIFEST-FILE-0373 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-09.md verifies |
| MANIFEST-FILE-0374 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-10.md verifies |
| MANIFEST-FILE-0375 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-11.md verifies |
| MANIFEST-FILE-0376 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-12.md verifies |
| MANIFEST-FILE-0377 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-13.md verifies |
| MANIFEST-FILE-0378 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-14.md verifies |
| MANIFEST-FILE-0379 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-15.md verifies |
| MANIFEST-FILE-0380 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-16.md verifies |
| MANIFEST-FILE-0381 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-17.md verifies |
| MANIFEST-FILE-0382 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-18.md verifies |
| MANIFEST-FILE-0383 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-19.md verifies |
| MANIFEST-FILE-0384 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-20.md verifies |
| MANIFEST-FILE-0385 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-21.md verifies |
| MANIFEST-FILE-0386 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-22.md verifies |
| MANIFEST-FILE-0387 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-23.md verifies |
| MANIFEST-FILE-0388 | manifest | PASS | manifest row feasibility/theorem_prospectus/TH-24.md verifies |
| MANIFEST-FILE-0389 | manifest | PASS | manifest row feasibility/toy_program_prospectus/.gitkeep verifies |
| MANIFEST-FILE-0390 | manifest | PASS | manifest row feasibility/toy_program_prospectus/INDEX.md verifies |
| MANIFEST-FILE-0391 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-01.md verifies |
| MANIFEST-FILE-0392 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-02.md verifies |
| MANIFEST-FILE-0393 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-03.md verifies |
| MANIFEST-FILE-0394 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-04.md verifies |
| MANIFEST-FILE-0395 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-05.md verifies |
| MANIFEST-FILE-0396 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-06.md verifies |
| MANIFEST-FILE-0397 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-07.md verifies |
| MANIFEST-FILE-0398 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-08.md verifies |
| MANIFEST-FILE-0399 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-09.md verifies |
| MANIFEST-FILE-0400 | manifest | PASS | manifest row feasibility/toy_program_prospectus/TP-10.md verifies |
| MANIFEST-FILE-0401 | manifest | PASS | manifest row formal/README.md verifies |
| MANIFEST-FILE-0402 | manifest | PASS | manifest row formal/TOOLCHAIN_STATUS.json verifies |
| MANIFEST-FILE-0403 | manifest | PASS | manifest row formal/certificates/README.md verifies |
| MANIFEST-FILE-0404 | manifest | PASS | manifest row formal/certificates/arrow/ARROW-POS-01.certificate.json verifies |
| MANIFEST-FILE-0405 | manifest | PASS | manifest row formal/certificates/autonomy/AUT-POS-01.certificate.json verifies |
| MANIFEST-FILE-0406 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C01.certificate.json verifies |
| MANIFEST-FILE-0407 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C02.certificate.json verifies |
| MANIFEST-FILE-0408 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C03.certificate.json verifies |
| MANIFEST-FILE-0409 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C04.certificate.json verifies |
| MANIFEST-FILE-0410 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C05.certificate.json verifies |
| MANIFEST-FILE-0411 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C06.certificate.json verifies |
| MANIFEST-FILE-0412 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C07.certificate.json verifies |
| MANIFEST-FILE-0413 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C08.certificate.json verifies |
| MANIFEST-FILE-0414 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C09.certificate.json verifies |
| MANIFEST-FILE-0415 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C10.certificate.json verifies |
| MANIFEST-FILE-0416 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C11.certificate.json verifies |
| MANIFEST-FILE-0417 | manifest | PASS | manifest row formal/certificates/autonomy/controls/AUT-C12.certificate.json verifies |
| MANIFEST-FILE-0418 | manifest | PASS | manifest row formal/certificates/corridors/COR-COMP-01.certificate.json verifies |
| MANIFEST-FILE-0419 | manifest | PASS | manifest row formal/certificates/corridors/COR-POS-01.certificate.json verifies |
| MANIFEST-FILE-0420 | manifest | PASS | manifest row formal/certificates/corridors/COR-POS-02-COMPOSED.certificate.json verifies |
| MANIFEST-FILE-0421 | manifest | PASS | manifest row formal/certificates/corridors/COR-POS-02A.certificate.json verifies |
| MANIFEST-FILE-0422 | manifest | PASS | manifest row formal/certificates/corridors/COR-POS-02B.certificate.json verifies |
| MANIFEST-FILE-0423 | manifest | PASS | manifest row formal/certificates/corridors/controls/COMP-C01.certificate.json verifies |
| MANIFEST-FILE-0424 | manifest | PASS | manifest row formal/certificates/corridors/controls/COMP-C02.certificate.json verifies |
| MANIFEST-FILE-0425 | manifest | PASS | manifest row formal/certificates/corridors/controls/COMP-C03.certificate.json verifies |
| MANIFEST-FILE-0426 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C01.certificate.json verifies |
| MANIFEST-FILE-0427 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C02.certificate.json verifies |
| MANIFEST-FILE-0428 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C03.certificate.json verifies |
| MANIFEST-FILE-0429 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C04.certificate.json verifies |
| MANIFEST-FILE-0430 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C05.certificate.json verifies |
| MANIFEST-FILE-0431 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C06.certificate.json verifies |
| MANIFEST-FILE-0432 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C07.certificate.json verifies |
| MANIFEST-FILE-0433 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C08.certificate.json verifies |
| MANIFEST-FILE-0434 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C09.certificate.json verifies |
| MANIFEST-FILE-0435 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C10.certificate.json verifies |
| MANIFEST-FILE-0436 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C11.certificate.json verifies |
| MANIFEST-FILE-0437 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C12.certificate.json verifies |
| MANIFEST-FILE-0438 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C13.certificate.json verifies |
| MANIFEST-FILE-0439 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C14.certificate.json verifies |
| MANIFEST-FILE-0440 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C15.certificate.json verifies |
| MANIFEST-FILE-0441 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C16.certificate.json verifies |
| MANIFEST-FILE-0442 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C17.certificate.json verifies |
| MANIFEST-FILE-0443 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C18.certificate.json verifies |
| MANIFEST-FILE-0444 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C19.certificate.json verifies |
| MANIFEST-FILE-0445 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C20.certificate.json verifies |
| MANIFEST-FILE-0446 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C21.certificate.json verifies |
| MANIFEST-FILE-0447 | manifest | PASS | manifest row formal/certificates/corridors/controls/COR-C22.certificate.json verifies |
| MANIFEST-FILE-0448 | manifest | PASS | manifest row formal/certificates/countermodels/CM-01.certificate.json verifies |
| MANIFEST-FILE-0449 | manifest | PASS | manifest row formal/certificates/countermodels/CM-02.certificate.json verifies |
| MANIFEST-FILE-0450 | manifest | PASS | manifest row formal/certificates/countermodels/CM-03.certificate.json verifies |
| MANIFEST-FILE-0451 | manifest | PASS | manifest row formal/certificates/countermodels/CM-04.certificate.json verifies |
| MANIFEST-FILE-0452 | manifest | PASS | manifest row formal/certificates/countermodels/CM-05.certificate.json verifies |
| MANIFEST-FILE-0453 | manifest | PASS | manifest row formal/certificates/countermodels/CM-06.certificate.json verifies |
| MANIFEST-FILE-0454 | manifest | PASS | manifest row formal/certificates/countermodels/CM-07.certificate.json verifies |
| MANIFEST-FILE-0455 | manifest | PASS | manifest row formal/certificates/countermodels/CM-08.certificate.json verifies |
| MANIFEST-FILE-0456 | manifest | PASS | manifest row formal/certificates/countermodels/CM-09.certificate.json verifies |
| MANIFEST-FILE-0457 | manifest | PASS | manifest row formal/certificates/countermodels/CM-10.certificate.json verifies |
| MANIFEST-FILE-0458 | manifest | PASS | manifest row formal/certificates/countermodels/CM-11.certificate.json verifies |
| MANIFEST-FILE-0459 | manifest | PASS | manifest row formal/certificates/countermodels/CM-12.certificate.json verifies |
| MANIFEST-FILE-0460 | manifest | PASS | manifest row formal/certificates/countermodels/CM-13.certificate.json verifies |
| MANIFEST-FILE-0461 | manifest | PASS | manifest row formal/certificates/countermodels/CM-14.certificate.json verifies |
| MANIFEST-FILE-0462 | manifest | PASS | manifest row formal/certificates/countermodels/CM-15.certificate.json verifies |
| MANIFEST-FILE-0463 | manifest | PASS | manifest row formal/certificates/countermodels/INDEX.md verifies |
| MANIFEST-FILE-0464 | manifest | PASS | manifest row formal/certificates/direct_successor/DS-PATH-POS-01.certificate.json verifies |
| MANIFEST-FILE-0465 | manifest | PASS | manifest row formal/certificates/direct_successor/DS-POS-01.certificate.json verifies |
| MANIFEST-FILE-0466 | manifest | PASS | manifest row formal/certificates/direct_successor/DS-POS-02A.certificate.json verifies |
| MANIFEST-FILE-0467 | manifest | PASS | manifest row formal/certificates/direct_successor/DS-POS-02B.certificate.json verifies |
| MANIFEST-FILE-0468 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C01.certificate.json verifies |
| MANIFEST-FILE-0469 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C02.certificate.json verifies |
| MANIFEST-FILE-0470 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C03.certificate.json verifies |
| MANIFEST-FILE-0471 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C04.certificate.json verifies |
| MANIFEST-FILE-0472 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C05.certificate.json verifies |
| MANIFEST-FILE-0473 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C06.certificate.json verifies |
| MANIFEST-FILE-0474 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C07.certificate.json verifies |
| MANIFEST-FILE-0475 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C08.certificate.json verifies |
| MANIFEST-FILE-0476 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C09.certificate.json verifies |
| MANIFEST-FILE-0477 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C10.certificate.json verifies |
| MANIFEST-FILE-0478 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C11.certificate.json verifies |
| MANIFEST-FILE-0479 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C12.certificate.json verifies |
| MANIFEST-FILE-0480 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C13.certificate.json verifies |
| MANIFEST-FILE-0481 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C14.certificate.json verifies |
| MANIFEST-FILE-0482 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C15.certificate.json verifies |
| MANIFEST-FILE-0483 | manifest | PASS | manifest row formal/certificates/direct_successor/controls/DS-C16.certificate.json verifies |
| MANIFEST-FILE-0484 | manifest | PASS | manifest row formal/certificates/fiach/FIACH-POS-01.certificate.json verifies |
| MANIFEST-FILE-0485 | manifest | PASS | manifest row formal/certificates/fiach/controls/FIACH-C01.certificate.json verifies |
| MANIFEST-FILE-0486 | manifest | PASS | manifest row formal/certificates/fiach/controls/FIACH-C02.certificate.json verifies |
| MANIFEST-FILE-0487 | manifest | PASS | manifest row formal/certificates/fiach/controls/FIACH-C03.certificate.json verifies |
| MANIFEST-FILE-0488 | manifest | PASS | manifest row formal/certificates/fiach/controls/FIACH-C04.certificate.json verifies |
| MANIFEST-FILE-0489 | manifest | PASS | manifest row formal/certificates/fiach/controls/FIACH-C05.certificate.json verifies |
| MANIFEST-FILE-0490 | manifest | PASS | manifest row formal/certificates/fiach/controls/FIACH-C06.certificate.json verifies |
| MANIFEST-FILE-0491 | manifest | PASS | manifest row formal/certificates/memory/BOUNDED_MEMORY_OR_FLATNESS_EXHAUSTION.json verifies |
| MANIFEST-FILE-0492 | manifest | PASS | manifest row formal/certificates/memory/MEM-FLAT-01.certificate.json verifies |
| MANIFEST-FILE-0493 | manifest | PASS | manifest row formal/certificates/memory/MEM-POS-01.certificate.json verifies |
| MANIFEST-FILE-0494 | manifest | PASS | manifest row formal/certificates/packages/BOUNDED_GLUING_EXHAUSTION.json verifies |
| MANIFEST-FILE-0495 | manifest | PASS | manifest row formal/certificates/packages/PKG-POS-01-TARGET.certificate.json verifies |
| MANIFEST-FILE-0496 | manifest | PASS | manifest row formal/certificates/packages/PKG-POS-02-SOURCE.certificate.json verifies |
| MANIFEST-FILE-0497 | manifest | PASS | manifest row formal/certificates/packages/PKG-POS-03-FIACH-SOURCE.certificate.json verifies |
| MANIFEST-FILE-0498 | manifest | PASS | manifest row formal/certificates/packages/PKG-POS-04-FIACH-TARGET.certificate.json verifies |
| MANIFEST-FILE-0499 | manifest | PASS | manifest row formal/certificates/packages/STG-POS-01.certificate.json verifies |
| MANIFEST-FILE-0500 | manifest | PASS | manifest row formal/certificates/packages/STG-POS-02-FIACH.certificate.json verifies |
| MANIFEST-FILE-0501 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-01.certificate.json verifies |
| MANIFEST-FILE-0502 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-02.certificate.json verifies |
| MANIFEST-FILE-0503 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-03.certificate.json verifies |
| MANIFEST-FILE-0504 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-04.certificate.json verifies |
| MANIFEST-FILE-0505 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-05.certificate.json verifies |
| MANIFEST-FILE-0506 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-06.certificate.json verifies |
| MANIFEST-FILE-0507 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-07.certificate.json verifies |
| MANIFEST-FILE-0508 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-08.certificate.json verifies |
| MANIFEST-FILE-0509 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-09.certificate.json verifies |
| MANIFEST-FILE-0510 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-10.certificate.json verifies |
| MANIFEST-FILE-0511 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-11.certificate.json verifies |
| MANIFEST-FILE-0512 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-12.certificate.json verifies |
| MANIFEST-FILE-0513 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-13.certificate.json verifies |
| MANIFEST-FILE-0514 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-14.certificate.json verifies |
| MANIFEST-FILE-0515 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-15.certificate.json verifies |
| MANIFEST-FILE-0516 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-16.certificate.json verifies |
| MANIFEST-FILE-0517 | manifest | PASS | manifest row formal/certificates/packages/controls/PC-17.certificate.json verifies |
| MANIFEST-FILE-0518 | manifest | PASS | manifest row formal/certificates/packages/controls/SC-01.certificate.json verifies |
| MANIFEST-FILE-0519 | manifest | PASS | manifest row formal/certificates/routes/BOUNDED_CONFLUENCE_SHAPE_SEARCH.json verifies |
| MANIFEST-FILE-0520 | manifest | PASS | manifest row formal/certificates/routes/BOUNDED_GLOBAL_NOW_OBSTRUCTION_SEARCH.json verifies |
| MANIFEST-FILE-0521 | manifest | PASS | manifest row formal/certificates/routes/ROUTE-NEG-01.certificate.json verifies |
| MANIFEST-FILE-0522 | manifest | PASS | manifest row formal/certificates/routes/ROUTE-POS-01.certificate.json verifies |
| MANIFEST-FILE-0523 | manifest | PASS | manifest row formal/certificates/search/AUTONOMY_FINITE_HORIZON_EXHAUSTION.json verifies |
| MANIFEST-FILE-0524 | manifest | PASS | manifest row formal/certificates/search/AUTONOMY_INVARIANT_EXHAUSTION.json verifies |
| MANIFEST-FILE-0525 | manifest | PASS | manifest row formal/certificates/search/CORRIDOR_COMPOSITION_SEARCH.json verifies |
| MANIFEST-FILE-0526 | manifest | PASS | manifest row formal/certificates/search/CORRIDOR_SUPPORT_SEARCH.json verifies |
| MANIFEST-FILE-0527 | manifest | PASS | manifest row formal/certificates/search/DIRECT_PATH_COMPOSITION_SEARCH.json verifies |
| MANIFEST-FILE-0528 | manifest | PASS | manifest row formal/certificates/search/DIRECT_SUCCESSOR_SEARCH.json verifies |
| MANIFEST-FILE-0529 | manifest | PASS | manifest row formal/certificates/search/FIACH_LANE_TRUTH_TABLE.json verifies |
| MANIFEST-FILE-0530 | manifest | PASS | manifest row formal/certificates/search/NONREDUNDANCY_TRUTH_TABLE_SEARCH.json verifies |
| MANIFEST-FILE-0531 | manifest | PASS | manifest row formal/certificates/transport/BOUNDED_TRANSPORT_SHAPE_SEARCH.json verifies |
| MANIFEST-FILE-0532 | manifest | PASS | manifest row formal/certificates/transport/TR-POS-01.certificate.json verifies |
| MANIFEST-FILE-0533 | manifest | PASS | manifest row formal/certificates/transport/TR-POS-02-FLAT.certificate.json verifies |
| MANIFEST-FILE-0534 | manifest | PASS | manifest row formal/certificates/transport/controls/ARROW-C01.certificate.json verifies |
| MANIFEST-FILE-0535 | manifest | PASS | manifest row formal/certificates/transport/controls/ARROW-C02.certificate.json verifies |
| MANIFEST-FILE-0536 | manifest | PASS | manifest row formal/certificates/transport/controls/ARROW-C03.certificate.json verifies |
| MANIFEST-FILE-0537 | manifest | PASS | manifest row formal/certificates/transport/controls/ARROW-C04.certificate.json verifies |
| MANIFEST-FILE-0538 | manifest | PASS | manifest row formal/certificates/transport/controls/MEM-C01.certificate.json verifies |
| MANIFEST-FILE-0539 | manifest | PASS | manifest row formal/certificates/transport/controls/ROUTE-C01.certificate.json verifies |
| MANIFEST-FILE-0540 | manifest | PASS | manifest row formal/certificates/transport/controls/ROUTE-C02.certificate.json verifies |
| MANIFEST-FILE-0541 | manifest | PASS | manifest row formal/certificates/transport/controls/ROUTE-C03.certificate.json verifies |
| MANIFEST-FILE-0542 | manifest | PASS | manifest row formal/certificates/transport/controls/ROUTE-C04.certificate.json verifies |
| MANIFEST-FILE-0543 | manifest | PASS | manifest row formal/certificates/transport/controls/ROUTE-C05.certificate.json verifies |
| MANIFEST-FILE-0544 | manifest | PASS | manifest row formal/certificates/transport/controls/ROUTE-C06.certificate.json verifies |
| MANIFEST-FILE-0545 | manifest | PASS | manifest row formal/certificates/transport/controls/ROUTE-C07.certificate.json verifies |
| MANIFEST-FILE-0546 | manifest | PASS | manifest row formal/certificates/transport/controls/ROUTE-C08.certificate.json verifies |
| MANIFEST-FILE-0547 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C01.certificate.json verifies |
| MANIFEST-FILE-0548 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C02.certificate.json verifies |
| MANIFEST-FILE-0549 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C03.certificate.json verifies |
| MANIFEST-FILE-0550 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C04.certificate.json verifies |
| MANIFEST-FILE-0551 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C05.certificate.json verifies |
| MANIFEST-FILE-0552 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C06.certificate.json verifies |
| MANIFEST-FILE-0553 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C07.certificate.json verifies |
| MANIFEST-FILE-0554 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C08.certificate.json verifies |
| MANIFEST-FILE-0555 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C09.certificate.json verifies |
| MANIFEST-FILE-0556 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C10.certificate.json verifies |
| MANIFEST-FILE-0557 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C11.certificate.json verifies |
| MANIFEST-FILE-0558 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C12.certificate.json verifies |
| MANIFEST-FILE-0559 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C13.certificate.json verifies |
| MANIFEST-FILE-0560 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C14.certificate.json verifies |
| MANIFEST-FILE-0561 | manifest | PASS | manifest row formal/certificates/transport/controls/TR-C15.certificate.json verifies |
| MANIFEST-FILE-0562 | manifest | PASS | manifest row inputs/INPUTS.sha256 verifies |
| MANIFEST-FILE-0563 | manifest | PASS | manifest row inputs/INPUT_PROVENANCE.md verifies |
| MANIFEST-FILE-0564 | manifest | PASS | manifest row inputs/SOURCE_INPUTS.md verifies |
| MANIFEST-FILE-0565 | manifest | PASS | manifest row inputs/normative/PAPER_TRIAGE.md verifies |
| MANIFEST-FILE-0566 | manifest | PASS | manifest row inputs/normative/PREPARATORY_EXPLORATION_PLAN.md verifies |
| MANIFEST-FILE-0567 | manifest | PASS | manifest row inputs/normative/cst-tt-00/EXECUTION_PLAN.md verifies |
| MANIFEST-FILE-0568 | manifest | PASS | manifest row inputs/normative/cst-tt-00/FIACH_BASELINE_SPECIFICATION.md verifies |
| MANIFEST-FILE-0569 | manifest | PASS | manifest row inputs/normative/cst-tt-00/IAPS_BASELINE_SPECIFICATION.md verifies |
| MANIFEST-FILE-0570 | manifest | PASS | manifest row inputs/normative/cst-tt-00/IMPORTED_SHA256SUMS.txt verifies |
| MANIFEST-FILE-0571 | manifest | PASS | manifest row inputs/normative/cst-tt-00/TEMPORAL_AUDIT_ORIGINAL_SHA256SUMS.txt verifies |
| MANIFEST-FILE-0572 | manifest | PASS | manifest row inputs/normative/cst-tt-00/TEMPORAL_AUDIT_README.md verifies |
| MANIFEST-FILE-0573 | manifest | PASS | manifest row inputs/normative/cst-tt-00/TEMPORAL_SOURCE_MAP.md verifies |
| MANIFEST-FILE-0574 | manifest | PASS | manifest row inputs/normative/cst-tt-00/TEMPORAL_TRANSCENDENCE_AUDIT.md verifies |
| MANIFEST-FILE-0575 | manifest | PASS | manifest row inputs/reference_surfaces/A1_A2_provenance_excerpt.md verifies |
| MANIFEST-FILE-0576 | manifest | PASS | manifest row inputs/reference_surfaces/F19_Object_Persistence_excerpt.tex verifies |
| MANIFEST-FILE-0577 | manifest | PASS | manifest row inputs/reference_surfaces/notation_and_terminology.md verifies |
| MANIFEST-FILE-0578 | manifest | PASS | manifest row inputs/reference_surfaces/open_issues.md verifies |
| MANIFEST-FILE-0579 | manifest | PASS | manifest row inputs/reference_surfaces/sec_02_claim_types.tex verifies |
| MANIFEST-FILE-0580 | manifest | PASS | manifest row inputs/reference_surfaces/sec_03_closure_architecture.tex verifies |
| MANIFEST-FILE-0581 | manifest | PASS | manifest row inputs/reference_surfaces/sec_05_consequence_clusters.tex verifies |
| MANIFEST-FILE-0582 | manifest | PASS | manifest row inputs/reference_surfaces/sec_06_conditional_realization.tex verifies |
| MANIFEST-FILE-0583 | manifest | PASS | manifest row inputs/reference_surfaces/sec_07_empirical_status.tex verifies |
| MANIFEST-FILE-0584 | manifest | PASS | manifest row inputs/reference_surfaces/sec_09_limitations_conclusion.tex verifies |
| MANIFEST-FILE-0585 | manifest | PASS | manifest row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_An_Audited_Closure_Architecture_for_Consciousness_Exact_Finite_Models_Structural_Theorems_and_Conditional_Realization.tex verifies |
| MANIFEST-FILE-0586 | manifest | PASS | manifest row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Glass_Is_an_Unclosed_Layer_Kovacs_Memory_as_Predictive_Quotient_Residue.tex verifies |
| MANIFEST-FILE-0587 | manifest | PASS | manifest row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex verifies |
| MANIFEST-FILE-0588 | manifest | PASS | manifest row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex verifies |
| MANIFEST-FILE-0589 | manifest | PASS | manifest row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_VI_A_Catalog_of_Dynamical_Structural_Laws.tex verifies |
| MANIFEST-FILE-0590 | manifest | PASS | manifest row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Protocol_Trap_Holonomy_Without_Entropy_Production.tex verifies |
| MANIFEST-FILE-0591 | manifest | PASS | manifest row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Flatten_a_Stone_with_Six_Birds_Critical_Pairs_Holonomy_and_Confluence_in_Rewriting_Systems.tex verifies |
| MANIFEST-FILE-0592 | manifest | PASS | manifest row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Lay_a_Stone_with_Six_Birds_Finite_State_Semantics_for_Packaging_Directionality_and_Coarse_Graining.tex verifies |
| MANIFEST-FILE-0593 | manifest | PASS | manifest row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex verifies |
| MANIFEST-FILE-0594 | manifest | PASS | manifest row inputs/source_archives/CST_temporal_transcendence_audit.zip verifies |
| MANIFEST-FILE-0595 | manifest | PASS | manifest row inputs/source_archives/six-birds-consciousness_v41.zip verifies |
| MANIFEST-FILE-0596 | manifest | PASS | manifest row inputs/source_archives/six_birds_papers_tex.zip verifies |
| MANIFEST-FILE-0597 | manifest | PASS | manifest row lakefile.toml verifies |
| MANIFEST-FILE-0598 | manifest | PASS | manifest row lean-toolchain verifies |
| MANIFEST-FILE-0599 | manifest | PASS | manifest row ledgers/.gitkeep verifies |
| MANIFEST-FILE-0600 | manifest | PASS | manifest row ledgers/DECISION_LOG.md verifies |
| MANIFEST-FILE-0601 | manifest | PASS | manifest row ledgers/REJECTED_DEFAULTS.md verifies |
| MANIFEST-FILE-0602 | manifest | PASS | manifest row ledgers/UNRESOLVED_QUESTIONS.md verifies |
| MANIFEST-FILE-0603 | manifest | PASS | manifest row ledgers/anti_conflation_checklist.csv verifies |
| MANIFEST-FILE-0604 | manifest | PASS | manifest row ledgers/asset_provenance.csv verifies |
| MANIFEST-FILE-0605 | manifest | PASS | manifest row ledgers/assumption_exposure.csv verifies |
| MANIFEST-FILE-0606 | manifest | PASS | manifest row ledgers/assumption_register.csv verifies |
| MANIFEST-FILE-0607 | manifest | PASS | manifest row ledgers/assumption_register.yml verifies |
| MANIFEST-FILE-0608 | manifest | PASS | manifest row ledgers/candidate_anti_conflation_audit.csv verifies |
| MANIFEST-FILE-0609 | manifest | PASS | manifest row ledgers/candidate_asset_crosswalk.csv verifies |
| MANIFEST-FILE-0610 | manifest | PASS | manifest row ledgers/candidate_assumption_matrix.csv verifies |
| MANIFEST-FILE-0611 | manifest | PASS | manifest row ledgers/candidate_discriminator_crosswalk.csv verifies |
| MANIFEST-FILE-0612 | manifest | PASS | manifest row ledgers/candidate_divergence_matrix.csv verifies |
| MANIFEST-FILE-0613 | manifest | PASS | manifest row ledgers/candidate_feature_matrix.csv verifies |
| MANIFEST-FILE-0614 | manifest | PASS | manifest row ledgers/candidate_hard_case_stress.csv verifies |
| MANIFEST-FILE-0615 | manifest | PASS | manifest row ledgers/candidate_internal_lens_audit.csv verifies |
| MANIFEST-FILE-0616 | manifest | PASS | manifest row ledgers/candidate_question_responses.csv verifies |
| MANIFEST-FILE-0617 | manifest | PASS | manifest row ledgers/candidate_scenario_verdicts.csv verifies |
| MANIFEST-FILE-0618 | manifest | PASS | manifest row ledgers/candidate_verdicts_by_scenario.csv verifies |
| MANIFEST-FILE-0619 | manifest | PASS | manifest row ledgers/claim_register_template.csv verifies |
| MANIFEST-FILE-0620 | manifest | PASS | manifest row ledgers/claim_tag_registry.yml verifies |
| MANIFEST-FILE-0621 | manifest | PASS | manifest row ledgers/corpus_duplicate_map.csv verifies |
| MANIFEST-FILE-0622 | manifest | PASS | manifest row ledgers/decision_log.csv verifies |
| MANIFEST-FILE-0623 | manifest | PASS | manifest row ledgers/dependency_read_wave_log.csv verifies |
| MANIFEST-FILE-0624 | manifest | PASS | manifest row ledgers/exploration_question_bank.yml verifies |
| MANIFEST-FILE-0625 | manifest | PASS | manifest row ledgers/external_literature_crosswalk.csv verifies |
| MANIFEST-FILE-0626 | manifest | PASS | manifest row ledgers/family_assumption_ladder.csv verifies |
| MANIFEST-FILE-0627 | manifest | PASS | manifest row ledgers/family_feasibility_registry.csv verifies |
| MANIFEST-FILE-0628 | manifest | PASS | manifest row ledgers/formalization_surface.csv verifies |
| MANIFEST-FILE-0629 | manifest | PASS | manifest row ledgers/gap_to_asset_matrix.csv verifies |
| MANIFEST-FILE-0630 | manifest | PASS | manifest row ledgers/glossary_terms.csv verifies |
| MANIFEST-FILE-0631 | manifest | PASS | manifest row ledgers/landing_bundle_registry.csv verifies |
| MANIFEST-FILE-0632 | manifest | PASS | manifest row ledgers/lexical_dependency_index.csv verifies |
| MANIFEST-FILE-0633 | manifest | PASS | manifest row ledgers/map_type_ledger.csv verifies |
| MANIFEST-FILE-0634 | manifest | PASS | manifest row ledgers/model_candidate_discrimination.csv verifies |
| MANIFEST-FILE-0635 | manifest | PASS | manifest row ledgers/model_registry.csv verifies |
| MANIFEST-FILE-0636 | manifest | PASS | manifest row ledgers/model_theorem_program_crosswalk.csv verifies |
| MANIFEST-FILE-0637 | manifest | PASS | manifest row ledgers/new_primitive_register.csv verifies |
| MANIFEST-FILE-0638 | manifest | PASS | manifest row ledgers/no_go_refinement_map.csv verifies |
| MANIFEST-FILE-0639 | manifest | PASS | manifest row ledgers/no_go_register.csv verifies |
| MANIFEST-FILE-0640 | manifest | PASS | manifest row ledgers/paper_coverage_audit.csv verifies |
| MANIFEST-FILE-0641 | manifest | PASS | manifest row ledgers/rejection_and_salvage_log.csv verifies |
| MANIFEST-FILE-0642 | manifest | PASS | manifest row ledgers/scenario_asset_crosswalk.csv verifies |
| MANIFEST-FILE-0643 | manifest | PASS | manifest row ledgers/scenario_discriminator_matrix.csv verifies |
| MANIFEST-FILE-0644 | manifest | PASS | manifest row ledgers/scenario_question_crosswalk.csv verifies |
| MANIFEST-FILE-0645 | manifest | PASS | manifest row ledgers/scenario_verdict_template.csv verifies |
| MANIFEST-FILE-0646 | manifest | PASS | manifest row ledgers/source_label_index.csv verifies |
| MANIFEST-FILE-0647 | manifest | PASS | manifest row ledgers/statement_provenance.csv verifies |
| MANIFEST-FILE-0648 | manifest | PASS | manifest row ledgers/support_and_carrier_assumptions.csv verifies |
| MANIFEST-FILE-0649 | manifest | PASS | manifest row ledgers/survivor_composition_matrix.csv verifies |
| MANIFEST-FILE-0650 | manifest | PASS | manifest row ledgers/survivor_family_registry.csv verifies |
| MANIFEST-FILE-0651 | manifest | PASS | manifest row ledgers/term_dependency_and_circularity_audit.csv verifies |
| MANIFEST-FILE-0652 | manifest | PASS | manifest row ledgers/theorem_dependency_and_risk.csv verifies |
| MANIFEST-FILE-0653 | manifest | PASS | manifest row ledgers/toy_program_registry.csv verifies |
| MANIFEST-FILE-0654 | manifest | PASS | manifest row ledgers/version_and_exclusion_log.md verifies |
| MANIFEST-FILE-0655 | manifest | PASS | manifest row manifests/.gitkeep verifies |
| MANIFEST-FILE-0656 | manifest | PASS | manifest row manifests/COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0657 | manifest | PASS | manifest row manifests/CST-EXP-00_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0658 | manifest | PASS | manifest row manifests/CST-EXP-00_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0659 | manifest | PASS | manifest row manifests/CST-EXP-01_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0660 | manifest | PASS | manifest row manifests/CST-EXP-01_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0661 | manifest | PASS | manifest row manifests/CST-EXP-01_VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0662 | manifest | PASS | manifest row manifests/CST-EXP-02_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0663 | manifest | PASS | manifest row manifests/CST-EXP-02_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0664 | manifest | PASS | manifest row manifests/CST-EXP-02_VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0665 | manifest | PASS | manifest row manifests/CST-EXP-03_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0666 | manifest | PASS | manifest row manifests/CST-EXP-03_MANIFEST.json verifies |
| MANIFEST-FILE-0667 | manifest | PASS | manifest row manifests/CST-EXP-03_REBUILD_VERIFICATION.json verifies |
| MANIFEST-FILE-0668 | manifest | PASS | manifest row manifests/CST-EXP-03_REBUILD_VERIFICATION.md verifies |
| MANIFEST-FILE-0669 | manifest | PASS | manifest row manifests/CST-EXP-04_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0670 | manifest | PASS | manifest row manifests/CST-EXP-04_MANIFEST.json verifies |
| MANIFEST-FILE-0671 | manifest | PASS | manifest row manifests/CST-EXP-04_PREVALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0672 | manifest | PASS | manifest row manifests/CST-EXP-04_PREVALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0673 | manifest | PASS | manifest row manifests/CST-EXP-04_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0674 | manifest | PASS | manifest row manifests/CST-EXP-04_VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0675 | manifest | PASS | manifest row manifests/CST-EXP-05_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0676 | manifest | PASS | manifest row manifests/CST-EXP-05_MANIFEST.json verifies |
| MANIFEST-FILE-0677 | manifest | PASS | manifest row manifests/CST-EXP-06_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0678 | manifest | PASS | manifest row manifests/CST-EXP-06_MANIFEST.json verifies |
| MANIFEST-FILE-0679 | manifest | PASS | manifest row manifests/CST-EXP-06_PREVALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0680 | manifest | PASS | manifest row manifests/CST-EXP-06_PREVALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0681 | manifest | PASS | manifest row manifests/CST-EXP-06_SHA256SUMS verifies |
| MANIFEST-FILE-0682 | manifest | PASS | manifest row manifests/CST-EXP-06_VALIDATION_REPORT_FINAL.md verifies |
| MANIFEST-FILE-0683 | manifest | PASS | manifest row manifests/CST-EXP-06_VALIDATION_RESULTS_FINAL.json verifies |
| MANIFEST-FILE-0684 | manifest | PASS | manifest row manifests/CST-TT-00_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0685 | manifest | PASS | manifest row manifests/CST-TT-00_MANIFEST.json verifies |
| MANIFEST-FILE-0686 | manifest | PASS | manifest row manifests/CST-TT-00_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-FILE-0687 | manifest | PASS | manifest row manifests/CST-TT-00_PHASE_SUMMARY.json verifies |
| MANIFEST-FILE-0688 | manifest | PASS | manifest row manifests/CST-TT-00_REBUILD_VERIFICATION.json verifies |
| MANIFEST-FILE-0689 | manifest | PASS | manifest row manifests/CST-TT-00_REBUILD_VERIFICATION.md verifies |
| MANIFEST-FILE-0690 | manifest | PASS | manifest row manifests/CST-TT-00_SHA256SUMS verifies |
| MANIFEST-FILE-0691 | manifest | PASS | manifest row manifests/CST-TT-00_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-FILE-0692 | manifest | PASS | manifest row manifests/CST-TT-00_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0693 | manifest | PASS | manifest row manifests/CST-TT-00_VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0694 | manifest | PASS | manifest row manifests/CST-TT-01_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0695 | manifest | PASS | manifest row manifests/CST-TT-01_MANIFEST.json verifies |
| MANIFEST-FILE-0696 | manifest | PASS | manifest row manifests/CST-TT-01_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-FILE-0697 | manifest | PASS | manifest row manifests/CST-TT-01_PHASE_SUMMARY.json verifies |
| MANIFEST-FILE-0698 | manifest | PASS | manifest row manifests/CST-TT-01_REBUILD_VERIFICATION.json verifies |
| MANIFEST-FILE-0699 | manifest | PASS | manifest row manifests/CST-TT-01_REBUILD_VERIFICATION.md verifies |
| MANIFEST-FILE-0700 | manifest | PASS | manifest row manifests/CST-TT-01_SEARCH_SUMMARY.json verifies |
| MANIFEST-FILE-0701 | manifest | PASS | manifest row manifests/CST-TT-01_SHA256SUMS verifies |
| MANIFEST-FILE-0702 | manifest | PASS | manifest row manifests/CST-TT-01_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-FILE-0703 | manifest | PASS | manifest row manifests/CST-TT-01_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0704 | manifest | PASS | manifest row manifests/CST-TT-01_VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0705 | manifest | PASS | manifest row manifests/CST-TT-02_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0706 | manifest | PASS | manifest row manifests/CST-TT-02_MANIFEST.json verifies |
| MANIFEST-FILE-0707 | manifest | PASS | manifest row manifests/CST-TT-02_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-FILE-0708 | manifest | PASS | manifest row manifests/CST-TT-02_PHASE_SUMMARY.json verifies |
| MANIFEST-FILE-0709 | manifest | PASS | manifest row manifests/CST-TT-02_REBUILD_VERIFICATION.json verifies |
| MANIFEST-FILE-0710 | manifest | PASS | manifest row manifests/CST-TT-02_REBUILD_VERIFICATION.md verifies |
| MANIFEST-FILE-0711 | manifest | PASS | manifest row manifests/CST-TT-02_SHA256SUMS verifies |
| MANIFEST-FILE-0712 | manifest | PASS | manifest row manifests/CST-TT-02_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-FILE-0713 | manifest | PASS | manifest row manifests/CST-TT-02_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0714 | manifest | PASS | manifest row manifests/CST-TT-02_VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0715 | manifest | PASS | manifest row manifests/CST-TT-03_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0716 | manifest | PASS | manifest row manifests/CST-TT-03_MANIFEST.json verifies |
| MANIFEST-FILE-0717 | manifest | PASS | manifest row manifests/CST-TT-03_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-FILE-0718 | manifest | PASS | manifest row manifests/CST-TT-03_PHASE_SUMMARY.json verifies |
| MANIFEST-FILE-0719 | manifest | PASS | manifest row manifests/CST-TT-03_REBUILD_VERIFICATION.json verifies |
| MANIFEST-FILE-0720 | manifest | PASS | manifest row manifests/CST-TT-03_REBUILD_VERIFICATION.md verifies |
| MANIFEST-FILE-0721 | manifest | PASS | manifest row manifests/CST-TT-03_SHA256SUMS verifies |
| MANIFEST-FILE-0722 | manifest | PASS | manifest row manifests/CST-TT-03_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-FILE-0723 | manifest | PASS | manifest row manifests/CST-TT-03_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0724 | manifest | PASS | manifest row manifests/CST-TT-03_VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0725 | manifest | PASS | manifest row manifests/CST-TT-04_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0726 | manifest | PASS | manifest row manifests/CST-TT-04_MANIFEST.json verifies |
| MANIFEST-FILE-0727 | manifest | PASS | manifest row manifests/CST-TT-04_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-FILE-0728 | manifest | PASS | manifest row manifests/CST-TT-04_PHASE_SUMMARY.json verifies |
| MANIFEST-FILE-0729 | manifest | PASS | manifest row manifests/CST-TT-04_REBUILD_VERIFICATION.json verifies |
| MANIFEST-FILE-0730 | manifest | PASS | manifest row manifests/CST-TT-04_REBUILD_VERIFICATION.md verifies |
| MANIFEST-FILE-0731 | manifest | PASS | manifest row manifests/CST-TT-04_SHA256SUMS verifies |
| MANIFEST-FILE-0732 | manifest | PASS | manifest row manifests/CST-TT-04_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-FILE-0733 | manifest | PASS | manifest row manifests/CST-TT-04_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0734 | manifest | PASS | manifest row manifests/CST-TT-04_VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0735 | manifest | PASS | manifest row manifests/CST-TT-05_COMPLETION_REPORT.md verifies |
| MANIFEST-FILE-0736 | manifest | PASS | manifest row manifests/CST-TT-05_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-FILE-0737 | manifest | PASS | manifest row manifests/CST-TT-05_PHASE_SUMMARY.json verifies |
| MANIFEST-FILE-0738 | manifest | PASS | manifest row manifests/CST-TT-05_REBUILD_VERIFICATION.json verifies |
| MANIFEST-FILE-0739 | manifest | PASS | manifest row manifests/CST-TT-05_REBUILD_VERIFICATION.md verifies |
| MANIFEST-FILE-0740 | manifest | PASS | manifest row manifests/CST-TT-05_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-FILE-0741 | manifest | PASS | manifest row manifests/CST-TT-05_VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0742 | manifest | PASS | manifest row manifests/CST-TT-05_VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0743 | manifest | PASS | manifest row manifests/EXP02_ASSET_SUMMARY.json verifies |
| MANIFEST-FILE-0744 | manifest | PASS | manifest row manifests/EXP03_ASSET_SUMMARY.json verifies |
| MANIFEST-FILE-0745 | manifest | PASS | manifest row manifests/EXP04_ASSET_SUMMARY.json verifies |
| MANIFEST-FILE-0746 | manifest | PASS | manifest row manifests/EXP05_ASSET_SUMMARY.json verifies |
| MANIFEST-FILE-0747 | manifest | PASS | manifest row manifests/EXP06_ASSET_SUMMARY.json verifies |
| MANIFEST-FILE-0748 | manifest | PASS | manifest row manifests/PHASE_SUMMARY.json verifies |
| MANIFEST-FILE-0749 | manifest | PASS | manifest row manifests/REBUILD_VERIFICATION.json verifies |
| MANIFEST-FILE-0750 | manifest | PASS | manifest row manifests/REBUILD_VERIFICATION.md verifies |
| MANIFEST-FILE-0751 | manifest | PASS | manifest row manifests/RESTORE_AND_VERIFY.md verifies |
| MANIFEST-FILE-0752 | manifest | PASS | manifest row manifests/SOURCE_SHA256SUMS verifies |
| MANIFEST-FILE-0753 | manifest | PASS | manifest row manifests/TT00_ASSET_SUMMARY.json verifies |
| MANIFEST-FILE-0754 | manifest | PASS | manifest row manifests/VALIDATION_REPORT.md verifies |
| MANIFEST-FILE-0755 | manifest | PASS | manifest row manifests/VALIDATION_RESULTS.json verifies |
| MANIFEST-FILE-0756 | manifest | PASS | manifest row models/arrow/ARROW-POS-01.model.json verifies |
| MANIFEST-FILE-0757 | manifest | PASS | manifest row models/autonomy/AUT-POS-01.model.json verifies |
| MANIFEST-FILE-0758 | manifest | PASS | manifest row models/autonomy/controls/AUT-C01.model.json verifies |
| MANIFEST-FILE-0759 | manifest | PASS | manifest row models/autonomy/controls/AUT-C02.model.json verifies |
| MANIFEST-FILE-0760 | manifest | PASS | manifest row models/autonomy/controls/AUT-C03.model.json verifies |
| MANIFEST-FILE-0761 | manifest | PASS | manifest row models/autonomy/controls/AUT-C04.model.json verifies |
| MANIFEST-FILE-0762 | manifest | PASS | manifest row models/autonomy/controls/AUT-C05.model.json verifies |
| MANIFEST-FILE-0763 | manifest | PASS | manifest row models/autonomy/controls/AUT-C06.model.json verifies |
| MANIFEST-FILE-0764 | manifest | PASS | manifest row models/autonomy/controls/AUT-C07.model.json verifies |
| MANIFEST-FILE-0765 | manifest | PASS | manifest row models/autonomy/controls/AUT-C08.model.json verifies |
| MANIFEST-FILE-0766 | manifest | PASS | manifest row models/autonomy/controls/AUT-C09.model.json verifies |
| MANIFEST-FILE-0767 | manifest | PASS | manifest row models/autonomy/controls/AUT-C10.model.json verifies |
| MANIFEST-FILE-0768 | manifest | PASS | manifest row models/autonomy/controls/AUT-C11.model.json verifies |
| MANIFEST-FILE-0769 | manifest | PASS | manifest row models/autonomy/controls/AUT-C12.model.json verifies |
| MANIFEST-FILE-0770 | manifest | PASS | manifest row models/corridors/COR-POS-01.model.json verifies |
| MANIFEST-FILE-0771 | manifest | PASS | manifest row models/corridors/COR-POS-02-COMPOSED.model.json verifies |
| MANIFEST-FILE-0772 | manifest | PASS | manifest row models/corridors/COR-POS-02A.model.json verifies |
| MANIFEST-FILE-0773 | manifest | PASS | manifest row models/corridors/COR-POS-02B.model.json verifies |
| MANIFEST-FILE-0774 | manifest | PASS | manifest row models/corridors/controls/COMP-C01.model.json verifies |
| MANIFEST-FILE-0775 | manifest | PASS | manifest row models/corridors/controls/COMP-C02.model.json verifies |
| MANIFEST-FILE-0776 | manifest | PASS | manifest row models/corridors/controls/COMP-C03.model.json verifies |
| MANIFEST-FILE-0777 | manifest | PASS | manifest row models/corridors/controls/COR-C01.model.json verifies |
| MANIFEST-FILE-0778 | manifest | PASS | manifest row models/corridors/controls/COR-C02.model.json verifies |
| MANIFEST-FILE-0779 | manifest | PASS | manifest row models/corridors/controls/COR-C03.model.json verifies |
| MANIFEST-FILE-0780 | manifest | PASS | manifest row models/corridors/controls/COR-C04.model.json verifies |
| MANIFEST-FILE-0781 | manifest | PASS | manifest row models/corridors/controls/COR-C05.model.json verifies |
| MANIFEST-FILE-0782 | manifest | PASS | manifest row models/corridors/controls/COR-C06.model.json verifies |
| MANIFEST-FILE-0783 | manifest | PASS | manifest row models/corridors/controls/COR-C07.model.json verifies |
| MANIFEST-FILE-0784 | manifest | PASS | manifest row models/corridors/controls/COR-C08.model.json verifies |
| MANIFEST-FILE-0785 | manifest | PASS | manifest row models/corridors/controls/COR-C09.model.json verifies |
| MANIFEST-FILE-0786 | manifest | PASS | manifest row models/corridors/controls/COR-C10.model.json verifies |
| MANIFEST-FILE-0787 | manifest | PASS | manifest row models/corridors/controls/COR-C11.model.json verifies |
| MANIFEST-FILE-0788 | manifest | PASS | manifest row models/corridors/controls/COR-C12.model.json verifies |
| MANIFEST-FILE-0789 | manifest | PASS | manifest row models/corridors/controls/COR-C13.model.json verifies |
| MANIFEST-FILE-0790 | manifest | PASS | manifest row models/corridors/controls/COR-C14.model.json verifies |
| MANIFEST-FILE-0791 | manifest | PASS | manifest row models/corridors/controls/COR-C15.model.json verifies |
| MANIFEST-FILE-0792 | manifest | PASS | manifest row models/corridors/controls/COR-C16.model.json verifies |
| MANIFEST-FILE-0793 | manifest | PASS | manifest row models/corridors/controls/COR-C17.model.json verifies |
| MANIFEST-FILE-0794 | manifest | PASS | manifest row models/corridors/controls/COR-C18.model.json verifies |
| MANIFEST-FILE-0795 | manifest | PASS | manifest row models/corridors/controls/COR-C19.model.json verifies |
| MANIFEST-FILE-0796 | manifest | PASS | manifest row models/corridors/controls/COR-C20.model.json verifies |
| MANIFEST-FILE-0797 | manifest | PASS | manifest row models/corridors/controls/COR-C21.model.json verifies |
| MANIFEST-FILE-0798 | manifest | PASS | manifest row models/corridors/controls/COR-C22.model.json verifies |
| MANIFEST-FILE-0799 | manifest | PASS | manifest row models/countermodels/CM-01.md verifies |
| MANIFEST-FILE-0800 | manifest | PASS | manifest row models/countermodels/CM-01.model.json verifies |
| MANIFEST-FILE-0801 | manifest | PASS | manifest row models/countermodels/CM-02.md verifies |
| MANIFEST-FILE-0802 | manifest | PASS | manifest row models/countermodels/CM-02.model.json verifies |
| MANIFEST-FILE-0803 | manifest | PASS | manifest row models/countermodels/CM-03.md verifies |
| MANIFEST-FILE-0804 | manifest | PASS | manifest row models/countermodels/CM-03.model.json verifies |
| MANIFEST-FILE-0805 | manifest | PASS | manifest row models/countermodels/CM-04.md verifies |
| MANIFEST-FILE-0806 | manifest | PASS | manifest row models/countermodels/CM-04.model.json verifies |
| MANIFEST-FILE-0807 | manifest | PASS | manifest row models/countermodels/CM-05.md verifies |
| MANIFEST-FILE-0808 | manifest | PASS | manifest row models/countermodels/CM-05.model.json verifies |
| MANIFEST-FILE-0809 | manifest | PASS | manifest row models/countermodels/CM-06.md verifies |
| MANIFEST-FILE-0810 | manifest | PASS | manifest row models/countermodels/CM-06.model.json verifies |
| MANIFEST-FILE-0811 | manifest | PASS | manifest row models/countermodels/CM-07.md verifies |
| MANIFEST-FILE-0812 | manifest | PASS | manifest row models/countermodels/CM-07.model.json verifies |
| MANIFEST-FILE-0813 | manifest | PASS | manifest row models/countermodels/CM-08.md verifies |
| MANIFEST-FILE-0814 | manifest | PASS | manifest row models/countermodels/CM-08.model.json verifies |
| MANIFEST-FILE-0815 | manifest | PASS | manifest row models/countermodels/CM-09.md verifies |
| MANIFEST-FILE-0816 | manifest | PASS | manifest row models/countermodels/CM-09.model.json verifies |
| MANIFEST-FILE-0817 | manifest | PASS | manifest row models/countermodels/CM-10.md verifies |
| MANIFEST-FILE-0818 | manifest | PASS | manifest row models/countermodels/CM-10.model.json verifies |
| MANIFEST-FILE-0819 | manifest | PASS | manifest row models/countermodels/CM-11.md verifies |
| MANIFEST-FILE-0820 | manifest | PASS | manifest row models/countermodels/CM-11.model.json verifies |
| MANIFEST-FILE-0821 | manifest | PASS | manifest row models/countermodels/CM-12.md verifies |
| MANIFEST-FILE-0822 | manifest | PASS | manifest row models/countermodels/CM-12.model.json verifies |
| MANIFEST-FILE-0823 | manifest | PASS | manifest row models/countermodels/CM-13.md verifies |
| MANIFEST-FILE-0824 | manifest | PASS | manifest row models/countermodels/CM-13.model.json verifies |
| MANIFEST-FILE-0825 | manifest | PASS | manifest row models/countermodels/CM-14.md verifies |
| MANIFEST-FILE-0826 | manifest | PASS | manifest row models/countermodels/CM-14.model.json verifies |
| MANIFEST-FILE-0827 | manifest | PASS | manifest row models/countermodels/CM-15.md verifies |
| MANIFEST-FILE-0828 | manifest | PASS | manifest row models/countermodels/CM-15.model.json verifies |
| MANIFEST-FILE-0829 | manifest | PASS | manifest row models/countermodels/INDEX.md verifies |
| MANIFEST-FILE-0830 | manifest | PASS | manifest row models/direct_successor/DS-POS-01.model.json verifies |
| MANIFEST-FILE-0831 | manifest | PASS | manifest row models/direct_successor/DS-POS-02A.model.json verifies |
| MANIFEST-FILE-0832 | manifest | PASS | manifest row models/direct_successor/DS-POS-02B.model.json verifies |
| MANIFEST-FILE-0833 | manifest | PASS | manifest row models/direct_successor/controls/DS-C01.model.json verifies |
| MANIFEST-FILE-0834 | manifest | PASS | manifest row models/direct_successor/controls/DS-C02.model.json verifies |
| MANIFEST-FILE-0835 | manifest | PASS | manifest row models/direct_successor/controls/DS-C03.model.json verifies |
| MANIFEST-FILE-0836 | manifest | PASS | manifest row models/direct_successor/controls/DS-C04.model.json verifies |
| MANIFEST-FILE-0837 | manifest | PASS | manifest row models/direct_successor/controls/DS-C05.model.json verifies |
| MANIFEST-FILE-0838 | manifest | PASS | manifest row models/direct_successor/controls/DS-C06.model.json verifies |
| MANIFEST-FILE-0839 | manifest | PASS | manifest row models/direct_successor/controls/DS-C07.model.json verifies |
| MANIFEST-FILE-0840 | manifest | PASS | manifest row models/direct_successor/controls/DS-C08.model.json verifies |
| MANIFEST-FILE-0841 | manifest | PASS | manifest row models/direct_successor/controls/DS-C09.model.json verifies |
| MANIFEST-FILE-0842 | manifest | PASS | manifest row models/direct_successor/controls/DS-C10.model.json verifies |
| MANIFEST-FILE-0843 | manifest | PASS | manifest row models/direct_successor/controls/DS-C11.model.json verifies |
| MANIFEST-FILE-0844 | manifest | PASS | manifest row models/direct_successor/controls/DS-C12.model.json verifies |
| MANIFEST-FILE-0845 | manifest | PASS | manifest row models/direct_successor/controls/DS-C13.model.json verifies |
| MANIFEST-FILE-0846 | manifest | PASS | manifest row models/direct_successor/controls/DS-C14.model.json verifies |
| MANIFEST-FILE-0847 | manifest | PASS | manifest row models/direct_successor/controls/DS-C15.model.json verifies |
| MANIFEST-FILE-0848 | manifest | PASS | manifest row models/direct_successor/controls/DS-C16.model.json verifies |
| MANIFEST-FILE-0849 | manifest | PASS | manifest row models/fiach/FIACH-POS-01.model.json verifies |
| MANIFEST-FILE-0850 | manifest | PASS | manifest row models/fiach/controls/FIACH-C01.model.json verifies |
| MANIFEST-FILE-0851 | manifest | PASS | manifest row models/fiach/controls/FIACH-C02.model.json verifies |
| MANIFEST-FILE-0852 | manifest | PASS | manifest row models/fiach/controls/FIACH-C03.model.json verifies |
| MANIFEST-FILE-0853 | manifest | PASS | manifest row models/fiach/controls/FIACH-C04.model.json verifies |
| MANIFEST-FILE-0854 | manifest | PASS | manifest row models/fiach/controls/FIACH-C05.model.json verifies |
| MANIFEST-FILE-0855 | manifest | PASS | manifest row models/fiach/controls/FIACH-C06.model.json verifies |
| MANIFEST-FILE-0856 | manifest | PASS | manifest row models/memory/MEM-FLAT-01.model.json verifies |
| MANIFEST-FILE-0857 | manifest | PASS | manifest row models/memory/MEM-POS-01.model.json verifies |
| MANIFEST-FILE-0858 | manifest | PASS | manifest row models/packages/PKG-POS-01-TARGET.model.json verifies |
| MANIFEST-FILE-0859 | manifest | PASS | manifest row models/packages/PKG-POS-02-SOURCE.model.json verifies |
| MANIFEST-FILE-0860 | manifest | PASS | manifest row models/packages/PKG-POS-03-FIACH-SOURCE.model.json verifies |
| MANIFEST-FILE-0861 | manifest | PASS | manifest row models/packages/PKG-POS-04-FIACH-TARGET.model.json verifies |
| MANIFEST-FILE-0862 | manifest | PASS | manifest row models/packages/STG-POS-01.assembly.json verifies |
| MANIFEST-FILE-0863 | manifest | PASS | manifest row models/packages/STG-POS-02-FIACH.assembly.json verifies |
| MANIFEST-FILE-0864 | manifest | PASS | manifest row models/packages/controls/PC-01.model.json verifies |
| MANIFEST-FILE-0865 | manifest | PASS | manifest row models/packages/controls/PC-02.model.json verifies |
| MANIFEST-FILE-0866 | manifest | PASS | manifest row models/packages/controls/PC-03.model.json verifies |
| MANIFEST-FILE-0867 | manifest | PASS | manifest row models/packages/controls/PC-04.model.json verifies |
| MANIFEST-FILE-0868 | manifest | PASS | manifest row models/packages/controls/PC-05.model.json verifies |
| MANIFEST-FILE-0869 | manifest | PASS | manifest row models/packages/controls/PC-06.model.json verifies |
| MANIFEST-FILE-0870 | manifest | PASS | manifest row models/packages/controls/PC-07.model.json verifies |
| MANIFEST-FILE-0871 | manifest | PASS | manifest row models/packages/controls/PC-08.model.json verifies |
| MANIFEST-FILE-0872 | manifest | PASS | manifest row models/packages/controls/PC-09.model.json verifies |
| MANIFEST-FILE-0873 | manifest | PASS | manifest row models/packages/controls/PC-10.model.json verifies |
| MANIFEST-FILE-0874 | manifest | PASS | manifest row models/packages/controls/PC-11.model.json verifies |
| MANIFEST-FILE-0875 | manifest | PASS | manifest row models/packages/controls/PC-12.model.json verifies |
| MANIFEST-FILE-0876 | manifest | PASS | manifest row models/packages/controls/PC-13.model.json verifies |
| MANIFEST-FILE-0877 | manifest | PASS | manifest row models/packages/controls/PC-14.model.json verifies |
| MANIFEST-FILE-0878 | manifest | PASS | manifest row models/packages/controls/PC-15.model.json verifies |
| MANIFEST-FILE-0879 | manifest | PASS | manifest row models/packages/controls/PC-16.model.json verifies |
| MANIFEST-FILE-0880 | manifest | PASS | manifest row models/packages/controls/PC-17.model.json verifies |
| MANIFEST-FILE-0881 | manifest | PASS | manifest row models/packages/controls/SC-01.assembly.json verifies |
| MANIFEST-FILE-0882 | manifest | PASS | manifest row models/routes/ROUTE-NEG-01.model.json verifies |
| MANIFEST-FILE-0883 | manifest | PASS | manifest row models/routes/ROUTE-POS-01.model.json verifies |
| MANIFEST-FILE-0884 | manifest | PASS | manifest row models/transport/TR-POS-01.model.json verifies |
| MANIFEST-FILE-0885 | manifest | PASS | manifest row models/transport/TR-POS-02-FLAT.model.json verifies |
| MANIFEST-FILE-0886 | manifest | PASS | manifest row models/transport/controls/ARROW-C01.model.json verifies |
| MANIFEST-FILE-0887 | manifest | PASS | manifest row models/transport/controls/ARROW-C02.model.json verifies |
| MANIFEST-FILE-0888 | manifest | PASS | manifest row models/transport/controls/ARROW-C03.model.json verifies |
| MANIFEST-FILE-0889 | manifest | PASS | manifest row models/transport/controls/ARROW-C04.model.json verifies |
| MANIFEST-FILE-0890 | manifest | PASS | manifest row models/transport/controls/MEM-C01.model.json verifies |
| MANIFEST-FILE-0891 | manifest | PASS | manifest row models/transport/controls/ROUTE-C01.model.json verifies |
| MANIFEST-FILE-0892 | manifest | PASS | manifest row models/transport/controls/ROUTE-C02.model.json verifies |
| MANIFEST-FILE-0893 | manifest | PASS | manifest row models/transport/controls/ROUTE-C03.model.json verifies |
| MANIFEST-FILE-0894 | manifest | PASS | manifest row models/transport/controls/ROUTE-C04.model.json verifies |
| MANIFEST-FILE-0895 | manifest | PASS | manifest row models/transport/controls/ROUTE-C05.model.json verifies |
| MANIFEST-FILE-0896 | manifest | PASS | manifest row models/transport/controls/ROUTE-C06.model.json verifies |
| MANIFEST-FILE-0897 | manifest | PASS | manifest row models/transport/controls/ROUTE-C07.model.json verifies |
| MANIFEST-FILE-0898 | manifest | PASS | manifest row models/transport/controls/ROUTE-C08.model.json verifies |
| MANIFEST-FILE-0899 | manifest | PASS | manifest row models/transport/controls/TR-C01.model.json verifies |
| MANIFEST-FILE-0900 | manifest | PASS | manifest row models/transport/controls/TR-C02.model.json verifies |
| MANIFEST-FILE-0901 | manifest | PASS | manifest row models/transport/controls/TR-C03.model.json verifies |
| MANIFEST-FILE-0902 | manifest | PASS | manifest row models/transport/controls/TR-C04.model.json verifies |
| MANIFEST-FILE-0903 | manifest | PASS | manifest row models/transport/controls/TR-C05.model.json verifies |
| MANIFEST-FILE-0904 | manifest | PASS | manifest row models/transport/controls/TR-C06.model.json verifies |
| MANIFEST-FILE-0905 | manifest | PASS | manifest row models/transport/controls/TR-C07.model.json verifies |
| MANIFEST-FILE-0906 | manifest | PASS | manifest row models/transport/controls/TR-C08.model.json verifies |
| MANIFEST-FILE-0907 | manifest | PASS | manifest row models/transport/controls/TR-C09.model.json verifies |
| MANIFEST-FILE-0908 | manifest | PASS | manifest row models/transport/controls/TR-C10.model.json verifies |
| MANIFEST-FILE-0909 | manifest | PASS | manifest row models/transport/controls/TR-C11.model.json verifies |
| MANIFEST-FILE-0910 | manifest | PASS | manifest row models/transport/controls/TR-C12.model.json verifies |
| MANIFEST-FILE-0911 | manifest | PASS | manifest row models/transport/controls/TR-C13.model.json verifies |
| MANIFEST-FILE-0912 | manifest | PASS | manifest row models/transport/controls/TR-C14.model.json verifies |
| MANIFEST-FILE-0913 | manifest | PASS | manifest row models/transport/controls/TR-C15.model.json verifies |
| MANIFEST-FILE-0914 | manifest | PASS | manifest row pyproject.toml verifies |
| MANIFEST-FILE-0915 | manifest | PASS | manifest row registries/ASSUMPTION_LEDGER.csv verifies |
| MANIFEST-FILE-0916 | manifest | PASS | manifest row registries/AUTONOMY_CONTROL_REGISTRY.csv verifies |
| MANIFEST-FILE-0917 | manifest | PASS | manifest row registries/AUTONOMY_SEARCH_REGISTRY.csv verifies |
| MANIFEST-FILE-0918 | manifest | PASS | manifest row registries/AUTONOMY_WITNESS_REGISTRY.csv verifies |
| MANIFEST-FILE-0919 | manifest | PASS | manifest row registries/CERTIFICATE_SCHEMA_REGISTRY.csv verifies |
| MANIFEST-FILE-0920 | manifest | PASS | manifest row registries/CLAIM_LANE_REGISTRY.csv verifies |
| MANIFEST-FILE-0921 | manifest | PASS | manifest row registries/CORRIDOR_COMPOSITION_REGISTRY.csv verifies |
| MANIFEST-FILE-0922 | manifest | PASS | manifest row registries/CORRIDOR_CONTROL_REGISTRY.csv verifies |
| MANIFEST-FILE-0923 | manifest | PASS | manifest row registries/CORRIDOR_SEARCH_REGISTRY.csv verifies |
| MANIFEST-FILE-0924 | manifest | PASS | manifest row registries/COUNTERMODEL_REGISTRY.csv verifies |
| MANIFEST-FILE-0925 | manifest | PASS | manifest row registries/DEFINITION_REGISTRY.csv verifies |
| MANIFEST-FILE-0926 | manifest | PASS | manifest row registries/DEPENDENCY_EDGES.csv verifies |
| MANIFEST-FILE-0927 | manifest | PASS | manifest row registries/DIRECT_SUCCESSOR_CONTROL_REGISTRY.csv verifies |
| MANIFEST-FILE-0928 | manifest | PASS | manifest row registries/DIRECT_SUCCESSOR_PATH_REGISTRY.csv verifies |
| MANIFEST-FILE-0929 | manifest | PASS | manifest row registries/DIRECT_SUCCESSOR_REGISTRY.csv verifies |
| MANIFEST-FILE-0930 | manifest | PASS | manifest row registries/FIACH_LANE_CONTROL_REGISTRY.csv verifies |
| MANIFEST-FILE-0931 | manifest | PASS | manifest row registries/FIACH_WITNESS_REGISTRY.csv verifies |
| MANIFEST-FILE-0932 | manifest | PASS | manifest row registries/HANDOFF_ALIGNED_PACKAGE_REGISTRY.csv verifies |
| MANIFEST-FILE-0933 | manifest | PASS | manifest row registries/KILL_CRITERIA.csv verifies |
| MANIFEST-FILE-0934 | manifest | PASS | manifest row registries/MEMORY_REPAIR_REGISTRY.csv verifies |
| MANIFEST-FILE-0935 | manifest | PASS | manifest row registries/MINIMALITY_LEDGER.csv verifies |
| MANIFEST-FILE-0936 | manifest | PASS | manifest row registries/OVERLAP_DIRECT_COMPARISON.csv verifies |
| MANIFEST-FILE-0937 | manifest | PASS | manifest row registries/PACKAGE_CONTROL_REGISTRY.csv verifies |
| MANIFEST-FILE-0938 | manifest | PASS | manifest row registries/PACKAGE_OBLIGATION_REGISTRY.csv verifies |
| MANIFEST-FILE-0939 | manifest | PASS | manifest row registries/PACKAGE_WITNESS_REGISTRY.csv verifies |
| MANIFEST-FILE-0940 | manifest | PASS | manifest row registries/PROJECT_REGISTRY.json verifies |
| MANIFEST-FILE-0941 | manifest | PASS | manifest row registries/RECORD_ARROW_REGISTRY.csv verifies |
| MANIFEST-FILE-0942 | manifest | PASS | manifest row registries/ROUTE_DISCIPLINE_REGISTRY.csv verifies |
| MANIFEST-FILE-0943 | manifest | PASS | manifest row registries/STAGED_ASSEMBLY_OBLIGATION_REGISTRY.csv verifies |
| MANIFEST-FILE-0944 | manifest | PASS | manifest row registries/TEMPORAL_AMENDMENT_MAP.csv verifies |
| MANIFEST-FILE-0945 | manifest | PASS | manifest row registries/TEMPORAL_CORRIDOR_WITNESS_REGISTRY.csv verifies |
| MANIFEST-FILE-0946 | manifest | PASS | manifest row registries/TEMPORAL_TRANSPORT_WITNESS_REGISTRY.csv verifies |
| MANIFEST-FILE-0947 | manifest | PASS | manifest row registries/THEOREM_REGISTRY.csv verifies |
| MANIFEST-FILE-0948 | manifest | PASS | manifest row registries/TOY_MODEL_REGISTRY.csv verifies |
| MANIFEST-FILE-0949 | manifest | PASS | manifest row registries/TRANSPORT_CONTROL_REGISTRY.csv verifies |
| MANIFEST-FILE-0950 | manifest | PASS | manifest row requirements-lock.txt verifies |
| MANIFEST-FILE-0951 | manifest | PASS | manifest row scenarios/.gitkeep verifies |
| MANIFEST-FILE-0952 | manifest | PASS | manifest row scenarios/CANONICAL_BATTERY.md verifies |
| MANIFEST-FILE-0953 | manifest | PASS | manifest row scenarios/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-FILE-0954 | manifest | PASS | manifest row scenarios/NEUTRAL_TRANSFER_SCHEMA.md verifies |
| MANIFEST-FILE-0955 | manifest | PASS | manifest row scenarios/OUTCOME_LABEL_REGISTRY.csv verifies |
| MANIFEST-FILE-0956 | manifest | PASS | manifest row scenarios/OUTCOME_TAXONOMY.md verifies |
| MANIFEST-FILE-0957 | manifest | PASS | manifest row scenarios/PROTOCOL_AXIS_DICTIONARY.md verifies |
| MANIFEST-FILE-0958 | manifest | PASS | manifest row scenarios/PROTOCOL_AXIS_MATRIX.csv verifies |
| MANIFEST-FILE-0959 | manifest | PASS | manifest row scenarios/PROTOCOL_AXIS_REGISTRY.csv verifies |
| MANIFEST-FILE-0960 | manifest | PASS | manifest row scenarios/SCENARIO_REGISTRY.json verifies |
| MANIFEST-FILE-0961 | manifest | PASS | manifest row scenarios/cards/INDEX.md verifies |
| MANIFEST-FILE-0962 | manifest | PASS | manifest row scenarios/cards/S01.md verifies |
| MANIFEST-FILE-0963 | manifest | PASS | manifest row scenarios/cards/S02.md verifies |
| MANIFEST-FILE-0964 | manifest | PASS | manifest row scenarios/cards/S03.md verifies |
| MANIFEST-FILE-0965 | manifest | PASS | manifest row scenarios/cards/S04.md verifies |
| MANIFEST-FILE-0966 | manifest | PASS | manifest row scenarios/cards/S05.md verifies |
| MANIFEST-FILE-0967 | manifest | PASS | manifest row scenarios/cards/S06.md verifies |
| MANIFEST-FILE-0968 | manifest | PASS | manifest row scenarios/cards/S07.md verifies |
| MANIFEST-FILE-0969 | manifest | PASS | manifest row scenarios/cards/S08.md verifies |
| MANIFEST-FILE-0970 | manifest | PASS | manifest row scenarios/cards/S09.md verifies |
| MANIFEST-FILE-0971 | manifest | PASS | manifest row scenarios/cards/S10.md verifies |
| MANIFEST-FILE-0972 | manifest | PASS | manifest row scenarios/cards/S11.md verifies |
| MANIFEST-FILE-0973 | manifest | PASS | manifest row scenarios/cards/S12.md verifies |
| MANIFEST-FILE-0974 | manifest | PASS | manifest row scenarios/cards/S13.md verifies |
| MANIFEST-FILE-0975 | manifest | PASS | manifest row scenarios/cards/S14.md verifies |
| MANIFEST-FILE-0976 | manifest | PASS | manifest row scenarios/cards/S15.md verifies |
| MANIFEST-FILE-0977 | manifest | PASS | manifest row scenarios/cards/S16.md verifies |
| MANIFEST-FILE-0978 | manifest | PASS | manifest row scenarios/cards/S17.md verifies |
| MANIFEST-FILE-0979 | manifest | PASS | manifest row scenarios/cards/S18.md verifies |
| MANIFEST-FILE-0980 | manifest | PASS | manifest row scenarios/cards/S19.md verifies |
| MANIFEST-FILE-0981 | manifest | PASS | manifest row scenarios/cards/S20.md verifies |
| MANIFEST-FILE-0982 | manifest | PASS | manifest row scenarios/cards/S21.md verifies |
| MANIFEST-FILE-0983 | manifest | PASS | manifest row scenarios/cards/S22.md verifies |
| MANIFEST-FILE-0984 | manifest | PASS | manifest row scenarios/cards/S23.md verifies |
| MANIFEST-FILE-0985 | manifest | PASS | manifest row scenarios/cards/S24.md verifies |
| MANIFEST-FILE-0986 | manifest | PASS | manifest row scenarios/cards/S25.md verifies |
| MANIFEST-FILE-0987 | manifest | PASS | manifest row scenarios/cards/S26.md verifies |
| MANIFEST-FILE-0988 | manifest | PASS | manifest row scenarios/cards/S27.md verifies |
| MANIFEST-FILE-0989 | manifest | PASS | manifest row scenarios/cards/S28.md verifies |
| MANIFEST-FILE-0990 | manifest | PASS | manifest row scenarios/cards/S29.md verifies |
| MANIFEST-FILE-0991 | manifest | PASS | manifest row scenarios/cards/S30.md verifies |
| MANIFEST-FILE-0992 | manifest | PASS | manifest row scenarios/cards/S31.md verifies |
| MANIFEST-FILE-0993 | manifest | PASS | manifest row scenarios/cards/S32.md verifies |
| MANIFEST-FILE-0994 | manifest | PASS | manifest row scenarios/cards/S33.md verifies |
| MANIFEST-FILE-0995 | manifest | PASS | manifest row scenarios/cards/S34.md verifies |
| MANIFEST-FILE-0996 | manifest | PASS | manifest row scenarios/cards/S35.md verifies |
| MANIFEST-FILE-0997 | manifest | PASS | manifest row scenarios/neutral_transfer_frame.dot verifies |
| MANIFEST-FILE-0998 | manifest | PASS | manifest row scenarios/neutral_transfer_frame.png verifies |
| MANIFEST-FILE-0999 | manifest | PASS | manifest row scenarios/neutral_transfer_frame.svg verifies |
| MANIFEST-FILE-1000 | manifest | PASS | manifest row schemas/certificates/aligned_package_certificate.schema.json verifies |
| MANIFEST-FILE-1001 | manifest | PASS | manifest row schemas/certificates/aligned_staged_package_certificate.schema.json verifies |
| MANIFEST-FILE-1002 | manifest | PASS | manifest row schemas/certificates/ancestry_certificate.schema.json verifies |
| MANIFEST-FILE-1003 | manifest | PASS | manifest row schemas/certificates/autonomy_certificate.schema.json verifies |
| MANIFEST-FILE-1004 | manifest | PASS | manifest row schemas/certificates/autonomy_control_certificate.schema.json verifies |
| MANIFEST-FILE-1005 | manifest | PASS | manifest row schemas/certificates/corridor_composition_certificate.schema.json verifies |
| MANIFEST-FILE-1006 | manifest | PASS | manifest row schemas/certificates/corridor_control_certificate.schema.json verifies |
| MANIFEST-FILE-1007 | manifest | PASS | manifest row schemas/certificates/countermodel_certificate.schema.json verifies |
| MANIFEST-FILE-1008 | manifest | PASS | manifest row schemas/certificates/direct_successor.schema.json verifies |
| MANIFEST-FILE-1009 | manifest | PASS | manifest row schemas/certificates/direct_successor_landed.schema.json verifies |
| MANIFEST-FILE-1010 | manifest | PASS | manifest row schemas/certificates/direct_successor_path_certificate.schema.json verifies |
| MANIFEST-FILE-1011 | manifest | PASS | manifest row schemas/certificates/fiach_lane_control_certificate.schema.json verifies |
| MANIFEST-FILE-1012 | manifest | PASS | manifest row schemas/certificates/memory_repair_certificate.schema.json verifies |
| MANIFEST-FILE-1013 | manifest | PASS | manifest row schemas/certificates/package_certificate.schema.json verifies |
| MANIFEST-FILE-1014 | manifest | PASS | manifest row schemas/certificates/package_control_certificate.schema.json verifies |
| MANIFEST-FILE-1015 | manifest | PASS | manifest row schemas/certificates/post_withdrawal_autonomy_certificate.schema.json verifies |
| MANIFEST-FILE-1016 | manifest | PASS | manifest row schemas/certificates/record_arrow_certificate.schema.json verifies |
| MANIFEST-FILE-1017 | manifest | PASS | manifest row schemas/certificates/route_discipline_certificate.schema.json verifies |
| MANIFEST-FILE-1018 | manifest | PASS | manifest row schemas/certificates/staged_package_certificate.schema.json verifies |
| MANIFEST-FILE-1019 | manifest | PASS | manifest row schemas/certificates/strict_temporal_corridor_certificate.schema.json verifies |
| MANIFEST-FILE-1020 | manifest | PASS | manifest row schemas/certificates/temporal_corridor.schema.json verifies |
| MANIFEST-FILE-1021 | manifest | PASS | manifest row schemas/certificates/temporal_fiach_certificate.schema.json verifies |
| MANIFEST-FILE-1022 | manifest | PASS | manifest row schemas/certificates/temporal_fiach_landed_certificate.schema.json verifies |
| MANIFEST-FILE-1023 | manifest | PASS | manifest row schemas/certificates/temporal_signature.schema.json verifies |
| MANIFEST-FILE-1024 | manifest | PASS | manifest row schemas/certificates/temporal_transport_certificate.schema.json verifies |
| MANIFEST-FILE-1025 | manifest | PASS | manifest row schemas/certificates/transport_control_certificate.schema.json verifies |
| MANIFEST-FILE-1026 | manifest | PASS | manifest row schemas/registries/theorem_registry_row.schema.json verifies |
| MANIFEST-FILE-1027 | manifest | PASS | manifest row scripts/build_exp01_assets.py verifies |
| MANIFEST-FILE-1028 | manifest | PASS | manifest row scripts/build_exp02_assets.py verifies |
| MANIFEST-FILE-1029 | manifest | PASS | manifest row scripts/build_exp03_assets.py verifies |
| MANIFEST-FILE-1030 | manifest | PASS | manifest row scripts/build_exp04_assets.py verifies |
| MANIFEST-FILE-1031 | manifest | PASS | manifest row scripts/build_exp05_assets.py verifies |
| MANIFEST-FILE-1032 | manifest | PASS | manifest row scripts/build_exp06_assets.py verifies |
| MANIFEST-FILE-1033 | manifest | PASS | manifest row scripts/build_tt00_assets.py verifies |
| MANIFEST-FILE-1034 | manifest | PASS | manifest row scripts/build_tt01_assets.py verifies |
| MANIFEST-FILE-1035 | manifest | PASS | manifest row scripts/build_tt02_assets.py verifies |
| MANIFEST-FILE-1036 | manifest | PASS | manifest row scripts/build_tt03_assets.py verifies |
| MANIFEST-FILE-1037 | manifest | PASS | manifest row scripts/build_tt04_assets.py verifies |
| MANIFEST-FILE-1038 | manifest | PASS | manifest row scripts/build_tt05_assets.py verifies |
| MANIFEST-FILE-1039 | manifest | PASS | manifest row scripts/enrich_exp01_assets.py verifies |
| MANIFEST-FILE-1040 | manifest | PASS | manifest row scripts/exp02_supplemental.py verifies |
| MANIFEST-FILE-1041 | manifest | PASS | manifest row scripts/exp03_data.py verifies |
| MANIFEST-FILE-1042 | manifest | PASS | manifest row scripts/exp04_data.py verifies |
| MANIFEST-FILE-1043 | manifest | PASS | manifest row scripts/exp05_data.py verifies |
| MANIFEST-FILE-1044 | manifest | PASS | manifest row scripts/exp06_data.py verifies |
| MANIFEST-FILE-1045 | manifest | PASS | manifest row scripts/extract_corpus.py verifies |
| MANIFEST-FILE-1046 | manifest | PASS | manifest row scripts/finalize_exp02_manifest.py verifies |
| MANIFEST-FILE-1047 | manifest | PASS | manifest row scripts/finalize_exp03_manifest.py verifies |
| MANIFEST-FILE-1048 | manifest | PASS | manifest row scripts/finalize_exp04_manifest.py verifies |
| MANIFEST-FILE-1049 | manifest | PASS | manifest row scripts/finalize_exp05_manifest.py verifies |
| MANIFEST-FILE-1050 | manifest | PASS | manifest row scripts/finalize_exp06_manifest.py verifies |
| MANIFEST-FILE-1051 | manifest | PASS | manifest row scripts/finalize_tt00_manifest.py verifies |
| MANIFEST-FILE-1052 | manifest | PASS | manifest row scripts/finalize_tt01_manifest.py verifies |
| MANIFEST-FILE-1053 | manifest | PASS | manifest row scripts/finalize_tt02_manifest.py verifies |
| MANIFEST-FILE-1054 | manifest | PASS | manifest row scripts/finalize_tt03_manifest.py verifies |
| MANIFEST-FILE-1055 | manifest | PASS | manifest row scripts/finalize_tt04_manifest.py verifies |
| MANIFEST-FILE-1056 | manifest | PASS | manifest row scripts/finalize_tt05_manifest.py verifies |
| MANIFEST-FILE-1057 | manifest | PASS | manifest row scripts/rebuild_exp01.sh verifies |
| MANIFEST-FILE-1058 | manifest | PASS | manifest row scripts/rebuild_exp02.sh verifies |
| MANIFEST-FILE-1059 | manifest | PASS | manifest row scripts/rebuild_exp03.sh verifies |
| MANIFEST-FILE-1060 | manifest | PASS | manifest row scripts/rebuild_exp04.sh verifies |
| MANIFEST-FILE-1061 | manifest | PASS | manifest row scripts/rebuild_exp05.sh verifies |
| MANIFEST-FILE-1062 | manifest | PASS | manifest row scripts/rebuild_exp06.sh verifies |
| MANIFEST-FILE-1063 | manifest | PASS | manifest row scripts/rebuild_tt00.sh verifies |
| MANIFEST-FILE-1064 | manifest | PASS | manifest row scripts/rebuild_tt01.sh verifies |
| MANIFEST-FILE-1065 | manifest | PASS | manifest row scripts/rebuild_tt02.sh verifies |
| MANIFEST-FILE-1066 | manifest | PASS | manifest row scripts/rebuild_tt03.sh verifies |
| MANIFEST-FILE-1067 | manifest | PASS | manifest row scripts/rebuild_tt04.sh verifies |
| MANIFEST-FILE-1068 | manifest | PASS | manifest row scripts/rebuild_tt05.sh verifies |
| MANIFEST-FILE-1069 | manifest | PASS | manifest row scripts/run_tt00_checks.sh verifies |
| MANIFEST-FILE-1070 | manifest | PASS | manifest row scripts/run_tt01_checks.sh verifies |
| MANIFEST-FILE-1071 | manifest | PASS | manifest row scripts/run_tt02_checks.sh verifies |
| MANIFEST-FILE-1072 | manifest | PASS | manifest row scripts/run_tt03_checks.sh verifies |
| MANIFEST-FILE-1073 | manifest | PASS | manifest row scripts/run_tt04_checks.sh verifies |
| MANIFEST-FILE-1074 | manifest | PASS | manifest row scripts/run_tt05_checks.sh verifies |
| MANIFEST-FILE-1075 | manifest | PASS | manifest row scripts/tt00_data.py verifies |
| MANIFEST-FILE-1076 | manifest | PASS | manifest row scripts/tt02_data.py verifies |
| MANIFEST-FILE-1077 | manifest | PASS | manifest row scripts/tt03_data.py verifies |
| MANIFEST-FILE-1078 | manifest | PASS | manifest row scripts/tt04_data.py verifies |
| MANIFEST-FILE-1079 | manifest | PASS | manifest row scripts/tt05_data.py verifies |
| MANIFEST-FILE-1080 | manifest | PASS | manifest row scripts/validate_exp01.py verifies |
| MANIFEST-FILE-1081 | manifest | PASS | manifest row scripts/validate_exp02.py verifies |
| MANIFEST-FILE-1082 | manifest | PASS | manifest row scripts/validate_exp03.py verifies |
| MANIFEST-FILE-1083 | manifest | PASS | manifest row scripts/validate_exp04.py verifies |
| MANIFEST-FILE-1084 | manifest | PASS | manifest row scripts/validate_exp05.py verifies |
| MANIFEST-FILE-1085 | manifest | PASS | manifest row scripts/validate_exp06.py verifies |
| MANIFEST-FILE-1086 | manifest | PASS | manifest row scripts/validate_tt00.py verifies |
| MANIFEST-FILE-1087 | manifest | PASS | manifest row scripts/validate_tt01.py verifies |
| MANIFEST-FILE-1088 | manifest | PASS | manifest row scripts/validate_tt02.py verifies |
| MANIFEST-FILE-1089 | manifest | PASS | manifest row scripts/validate_tt03.py verifies |
| MANIFEST-FILE-1090 | manifest | PASS | manifest row scripts/validate_tt04.py verifies |
| MANIFEST-FILE-1091 | manifest | PASS | manifest row scripts/validate_tt05.py verifies |
| MANIFEST-FILE-1092 | manifest | PASS | manifest row scripts/verify_exp03_rebuild.py verifies |
| MANIFEST-FILE-1093 | manifest | PASS | manifest row scripts/verify_exp04_rebuild.py verifies |
| MANIFEST-FILE-1094 | manifest | PASS | manifest row scripts/verify_exp05_rebuild.py verifies |
| MANIFEST-FILE-1095 | manifest | PASS | manifest row scripts/verify_exp06_rebuild.py verifies |
| MANIFEST-FILE-1096 | manifest | PASS | manifest row scripts/verify_tt00_rebuild.py verifies |
| MANIFEST-FILE-1097 | manifest | PASS | manifest row scripts/verify_tt01_rebuild.py verifies |
| MANIFEST-FILE-1098 | manifest | PASS | manifest row scripts/verify_tt02_rebuild.py verifies |
| MANIFEST-FILE-1099 | manifest | PASS | manifest row scripts/verify_tt03_rebuild.py verifies |
| MANIFEST-FILE-1100 | manifest | PASS | manifest row scripts/verify_tt04_rebuild.py verifies |
| MANIFEST-FILE-1101 | manifest | PASS | manifest row scripts/verify_tt05_rebuild.py verifies |
| MANIFEST-FILE-1102 | manifest | PASS | manifest row src/cst_tt/__init__.py verifies |
| MANIFEST-FILE-1103 | manifest | PASS | manifest row src/cst_tt/ancestry.py verifies |
| MANIFEST-FILE-1104 | manifest | PASS | manifest row src/cst_tt/autonomy.py verifies |
| MANIFEST-FILE-1105 | manifest | PASS | manifest row src/cst_tt/bridge_composition_checker.py verifies |
| MANIFEST-FILE-1106 | manifest | PASS | manifest row src/cst_tt/circularity.py verifies |
| MANIFEST-FILE-1107 | manifest | PASS | manifest row src/cst_tt/contracts.py verifies |
| MANIFEST-FILE-1108 | manifest | PASS | manifest row src/cst_tt/corridor.py verifies |
| MANIFEST-FILE-1109 | manifest | PASS | manifest row src/cst_tt/corridor_and_branch_checker.py verifies |
| MANIFEST-FILE-1110 | manifest | PASS | manifest row src/cst_tt/countermodels.py verifies |
| MANIFEST-FILE-1111 | manifest | PASS | manifest row src/cst_tt/fiach.py verifies |
| MANIFEST-FILE-1112 | manifest | PASS | manifest row src/cst_tt/hashing.py verifies |
| MANIFEST-FILE-1113 | manifest | PASS | manifest row src/cst_tt/package.py verifies |
| MANIFEST-FILE-1114 | manifest | PASS | manifest row src/cst_tt/package_auditor.py verifies |
| MANIFEST-FILE-1115 | manifest | PASS | manifest row src/cst_tt/package_gluing.py verifies |
| MANIFEST-FILE-1116 | manifest | PASS | manifest row src/cst_tt/predicates.py verifies |
| MANIFEST-FILE-1117 | manifest | PASS | manifest row src/cst_tt/registry.py verifies |
| MANIFEST-FILE-1118 | manifest | PASS | manifest row src/cst_tt/targets.py verifies |
| MANIFEST-FILE-1119 | manifest | PASS | manifest row src/cst_tt/temporal.py verifies |
| MANIFEST-FILE-1120 | manifest | PASS | manifest row src/cst_tt/transport.py verifies |
| MANIFEST-FILE-1121 | manifest | PASS | manifest row src/cst_tt/transport_auditor.py verifies |
| MANIFEST-FILE-1122 | manifest | PASS | manifest row src/cst_tt/types.py verifies |
| MANIFEST-FILE-1123 | manifest | PASS | manifest row src/cst_tt/withdrawal_autonomy_checker.py verifies |
| MANIFEST-FILE-1124 | manifest | PASS | manifest row synthesis/.gitkeep verifies |
| MANIFEST-FILE-1125 | manifest | PASS | manifest row synthesis/COPY_VS_CONTINUATION_AUDIT.md verifies |
| MANIFEST-FILE-1126 | manifest | PASS | manifest row synthesis/CST-EXP-03_CANDIDATE_GENERATION_SYNTHESIS.md verifies |
| MANIFEST-FILE-1127 | manifest | PASS | manifest row synthesis/EXPLORATION_DOSSIER.md verifies |
| MANIFEST-FILE-1128 | manifest | PASS | manifest row synthesis/FALLBACK_TARGET_SPECIFICATION.md verifies |
| MANIFEST-FILE-1129 | manifest | PASS | manifest row synthesis/FINALIST_COMPARISON.md verifies |
| MANIFEST-FILE-1130 | manifest | PASS | manifest row synthesis/FROZEN_THEOREM_FAMILY.csv verifies |
| MANIFEST-FILE-1131 | manifest | PASS | manifest row synthesis/FROZEN_WITNESS_SUITE.csv verifies |
| MANIFEST-FILE-1132 | manifest | PASS | manifest row synthesis/LATER_LANDING_HANDOFF.md verifies |
| MANIFEST-FILE-1133 | manifest | PASS | manifest row synthesis/PRIMARY_TARGET_SPECIFICATION.md verifies |
| MANIFEST-FILE-1134 | manifest | PASS | manifest row synthesis/README.md verifies |
| MANIFEST-FILE-1135 | manifest | PASS | manifest row synthesis/TARGET_REGISTRY.json verifies |
| MANIFEST-FILE-1136 | manifest | PASS | manifest row synthesis/TARGET_SCENARIO_VERDICTS.csv verifies |
| MANIFEST-FILE-1137 | manifest | PASS | manifest row synthesis/TARGET_SELECTION_SCORECARD.csv verifies |
| MANIFEST-FILE-1138 | manifest | PASS | manifest row synthesis/frozen_target_architecture.dot verifies |
| MANIFEST-FILE-1139 | manifest | PASS | manifest row synthesis/frozen_target_architecture.png verifies |
| MANIFEST-FILE-1140 | manifest | PASS | manifest row synthesis/frozen_target_architecture.svg verifies |
| MANIFEST-FILE-1141 | manifest | PASS | manifest row templates/.gitkeep verifies |
| MANIFEST-FILE-1142 | manifest | PASS | manifest row templates/CANDIDATE_CARD.yml verifies |
| MANIFEST-FILE-1143 | manifest | PASS | manifest row templates/CLAIM_RECORD.yml verifies |
| MANIFEST-FILE-1144 | manifest | PASS | manifest row templates/QUESTION_BANK_RESPONSE.yml verifies |
| MANIFEST-FILE-1145 | manifest | PASS | manifest row templates/SCENARIO_VERDICT_RECORD.yml verifies |
| MANIFEST-FILE-1146 | manifest | PASS | manifest row tests/test_autonomy_certificates.py verifies |
| MANIFEST-FILE-1147 | manifest | PASS | manifest row tests/test_circularity_and_lean_surface.py verifies |
| MANIFEST-FILE-1148 | manifest | PASS | manifest row tests/test_corridor_certificates.py verifies |
| MANIFEST-FILE-1149 | manifest | PASS | manifest row tests/test_corridor_composition.py verifies |
| MANIFEST-FILE-1150 | manifest | PASS | manifest row tests/test_corridor_searches.py verifies |
| MANIFEST-FILE-1151 | manifest | PASS | manifest row tests/test_countermodel_certificates.py verifies |
| MANIFEST-FILE-1152 | manifest | PASS | manifest row tests/test_countermodel_enumeration.py verifies |
| MANIFEST-FILE-1153 | manifest | PASS | manifest row tests/test_direct_successor.py verifies |
| MANIFEST-FILE-1154 | manifest | PASS | manifest row tests/test_fiach_certificate.py verifies |
| MANIFEST-FILE-1155 | manifest | PASS | manifest row tests/test_generated_assets.py verifies |
| MANIFEST-FILE-1156 | manifest | PASS | manifest row tests/test_package_certificates.py verifies |
| MANIFEST-FILE-1157 | manifest | PASS | manifest row tests/test_package_gluing.py verifies |
| MANIFEST-FILE-1158 | manifest | PASS | manifest row tests/test_phase01_boundaries.py verifies |
| MANIFEST-FILE-1159 | manifest | PASS | manifest row tests/test_provenance_and_boundaries.py verifies |
| MANIFEST-FILE-1160 | manifest | PASS | manifest row tests/test_python_types.py verifies |
| MANIFEST-FILE-1161 | manifest | PASS | manifest row tests/test_registries.py verifies |
| MANIFEST-FILE-1162 | manifest | PASS | manifest row tests/test_registry_schema.py verifies |
| MANIFEST-FILE-1163 | manifest | PASS | manifest row tests/test_reproducibility_policy.py verifies |
| MANIFEST-FILE-1164 | manifest | PASS | manifest row tests/test_route_memory_arrow.py verifies |
| MANIFEST-FILE-1165 | manifest | PASS | manifest row tests/test_scaffold_boundaries.py verifies |
| MANIFEST-FILE-1166 | manifest | PASS | manifest row tests/test_schema_examples.py verifies |
| MANIFEST-FILE-1167 | manifest | PASS | manifest row tests/test_temporal_transport_certificates.py verifies |
| MANIFEST-FILE-1168 | manifest | PASS | manifest row tests/test_transport_controls_and_search.py verifies |
| MANIFEST-FILE-1169 | manifest | PASS | manifest row tests/test_tt03_formal_surfaces.py verifies |
| MANIFEST-FILE-1170 | manifest | PASS | manifest row tests/test_tt04_formal_surfaces.py verifies |
| MANIFEST-FILE-1171 | manifest | PASS | manifest row tests/test_tt05_formal_surfaces.py verifies |
| MANIFEST-FILE-1172 | manifest | PASS | manifest row vocabulary/.gitkeep verifies |
| MANIFEST-FILE-1173 | manifest | PASS | manifest row vocabulary/CANONICAL_GLOSSARY.md verifies |
| MANIFEST-FILE-1174 | manifest | PASS | manifest row vocabulary/CLAIM_TYPE_SYSTEM.md verifies |
| MANIFEST-FILE-1175 | manifest | PASS | manifest row vocabulary/TERM_DEPENDENCY_AUDIT.md verifies |
| MANIFEST-FILE-1176 | manifest | PASS | manifest row vocabulary/TYPE_AND_NOTATION_SCAFFOLD.md verifies |
| MANIFEST-SUM-COUNT | manifest | PASS | checksum ledger includes files and both manifests |
| MANIFEST-SUM-0001 | manifest | PASS | checksum row .gitignore verifies |
| MANIFEST-SUM-0002 | manifest | PASS | checksum row CHANGELOG.md verifies |
| MANIFEST-SUM-0003 | manifest | PASS | checksum row CSTTT.lean verifies |
| MANIFEST-SUM-0004 | manifest | PASS | checksum row CSTTT/Autonomy/FiniteAutonomy.lean verifies |
| MANIFEST-SUM-0005 | manifest | PASS | checksum row CSTTT/Autonomy/System.lean verifies |
| MANIFEST-SUM-0006 | manifest | PASS | checksum row CSTTT/Core/Carrier.lean verifies |
| MANIFEST-SUM-0007 | manifest | PASS | checksum row CSTTT/Core/Episode.lean verifies |
| MANIFEST-SUM-0008 | manifest | PASS | checksum row CSTTT/Core/Finite.lean verifies |
| MANIFEST-SUM-0009 | manifest | PASS | checksum row CSTTT/Corridor/Composition.lean verifies |
| MANIFEST-SUM-0010 | manifest | PASS | checksum row CSTTT/Corridor/DirectSuccessor.lean verifies |
| MANIFEST-SUM-0011 | manifest | PASS | checksum row CSTTT/Corridor/FiniteDirectSuccessor.lean verifies |
| MANIFEST-SUM-0012 | manifest | PASS | checksum row CSTTT/Corridor/FiniteTemporalCorridor.lean verifies |
| MANIFEST-SUM-0013 | manifest | PASS | checksum row CSTTT/Corridor/TemporalCorridor.lean verifies |
| MANIFEST-SUM-0014 | manifest | PASS | checksum row CSTTT/Countermodels/Kernel.lean verifies |
| MANIFEST-SUM-0015 | manifest | PASS | checksum row CSTTT/Fallback/Ancestry.lean verifies |
| MANIFEST-SUM-0016 | manifest | PASS | checksum row CSTTT/Package/Clauses.lean verifies |
| MANIFEST-SUM-0017 | manifest | PASS | checksum row CSTTT/Package/FiniteGluing.lean verifies |
| MANIFEST-SUM-0018 | manifest | PASS | checksum row CSTTT/Package/Gluing.lean verifies |
| MANIFEST-SUM-0019 | manifest | PASS | checksum row CSTTT/Package/TemporalPackage.lean verifies |
| MANIFEST-SUM-0020 | manifest | PASS | checksum row CSTTT/Prospects/Statements.lean verifies |
| MANIFEST-SUM-0021 | manifest | PASS | checksum row CSTTT/Targets/FiniteTemporalFIACH.lean verifies |
| MANIFEST-SUM-0022 | manifest | PASS | checksum row CSTTT/Targets/TemporalFIACH.lean verifies |
| MANIFEST-SUM-0023 | manifest | PASS | checksum row CSTTT/Temporal/Clock.lean verifies |
| MANIFEST-SUM-0024 | manifest | PASS | checksum row CSTTT/Temporal/Closure.lean verifies |
| MANIFEST-SUM-0025 | manifest | PASS | checksum row CSTTT/Temporal/Signature.lean verifies |
| MANIFEST-SUM-0026 | manifest | PASS | checksum row CSTTT/Transport/FiniteExamples.lean verifies |
| MANIFEST-SUM-0027 | manifest | PASS | checksum row CSTTT/Transport/FiniteTemporalTransport.lean verifies |
| MANIFEST-SUM-0028 | manifest | PASS | checksum row CSTTT/Transport/RecordArrow.lean verifies |
| MANIFEST-SUM-0029 | manifest | PASS | checksum row CSTTT/Transport/RouteDiscipline.lean verifies |
| MANIFEST-SUM-0030 | manifest | PASS | checksum row CSTTT/Transport/TemporalBridge.lean verifies |
| MANIFEST-SUM-0031 | manifest | PASS | checksum row README.md verifies |
| MANIFEST-SUM-0032 | manifest | PASS | checksum row RESTORE_AND_VERIFY.md verifies |
| MANIFEST-SUM-0033 | manifest | PASS | checksum row STATE.md verifies |
| MANIFEST-SUM-0034 | manifest | PASS | checksum row STATUS.md verifies |
| MANIFEST-SUM-0035 | manifest | PASS | checksum row candidates/BRIDGE_DESIGN_SPACE.md verifies |
| MANIFEST-SUM-0036 | manifest | PASS | checksum row candidates/CANDIDATE_COMPARISON_GUIDE.md verifies |
| MANIFEST-SUM-0037 | manifest | PASS | checksum row candidates/CANDIDATE_REGISTRY.json verifies |
| MANIFEST-SUM-0038 | manifest | PASS | checksum row candidates/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-SUM-0039 | manifest | PASS | checksum row candidates/INVARIANT_ATLAS.md verifies |
| MANIFEST-SUM-0040 | manifest | PASS | checksum row candidates/TRANSPORTED_OBJECT_ATLAS.md verifies |
| MANIFEST-SUM-0041 | manifest | PASS | checksum row candidates/brainstorms/01_quotient_algebraic.md verifies |
| MANIFEST-SUM-0042 | manifest | PASS | checksum row candidates/brainstorms/02_dynamical_process.md verifies |
| MANIFEST-SUM-0043 | manifest | PASS | checksum row candidates/brainstorms/03_error_correcting_logical_object.md verifies |
| MANIFEST-SUM-0044 | manifest | PASS | checksum row candidates/brainstorms/04_closure_realization.md verifies |
| MANIFEST-SUM-0045 | manifest | PASS | checksum row candidates/brainstorms/05_viability_agent.md verifies |
| MANIFEST-SUM-0046 | manifest | PASS | checksum row candidates/brainstorms/06_branching_philosophical.md verifies |
| MANIFEST-SUM-0047 | manifest | PASS | checksum row candidates/brainstorms/07_wild_hybrid.md verifies |
| MANIFEST-SUM-0048 | manifest | PASS | checksum row candidates/brainstorms/BRAINSTORM_FREEZE.sha256 verifies |
| MANIFEST-SUM-0049 | manifest | PASS | checksum row candidates/brainstorms/INDEX.md verifies |
| MANIFEST-SUM-0050 | manifest | PASS | checksum row candidates/bridge_registry.csv verifies |
| MANIFEST-SUM-0051 | manifest | PASS | checksum row candidates/bridges/.gitkeep verifies |
| MANIFEST-SUM-0052 | manifest | PASS | checksum row candidates/candidate_design_space.dot verifies |
| MANIFEST-SUM-0053 | manifest | PASS | checksum row candidates/candidate_design_space.png verifies |
| MANIFEST-SUM-0054 | manifest | PASS | checksum row candidates/candidate_design_space.svg verifies |
| MANIFEST-SUM-0055 | manifest | PASS | checksum row candidates/invariant_registry.csv verifies |
| MANIFEST-SUM-0056 | manifest | PASS | checksum row candidates/invariants/.gitkeep verifies |
| MANIFEST-SUM-0057 | manifest | PASS | checksum row candidates/target_schemas/.gitkeep verifies |
| MANIFEST-SUM-0058 | manifest | PASS | checksum row candidates/target_schemas/INDEX.md verifies |
| MANIFEST-SUM-0059 | manifest | PASS | checksum row candidates/target_schemas/TS-01.md verifies |
| MANIFEST-SUM-0060 | manifest | PASS | checksum row candidates/target_schemas/TS-02.md verifies |
| MANIFEST-SUM-0061 | manifest | PASS | checksum row candidates/target_schemas/TS-03.md verifies |
| MANIFEST-SUM-0062 | manifest | PASS | checksum row candidates/target_schemas/TS-04.md verifies |
| MANIFEST-SUM-0063 | manifest | PASS | checksum row candidates/target_schemas/TS-05.md verifies |
| MANIFEST-SUM-0064 | manifest | PASS | checksum row candidates/target_schemas/TS-06.md verifies |
| MANIFEST-SUM-0065 | manifest | PASS | checksum row candidates/target_schemas/TS-07.md verifies |
| MANIFEST-SUM-0066 | manifest | PASS | checksum row candidates/target_schemas/TS-08.md verifies |
| MANIFEST-SUM-0067 | manifest | PASS | checksum row candidates/target_schemas/TS-09.md verifies |
| MANIFEST-SUM-0068 | manifest | PASS | checksum row candidates/target_schemas/TS-10.md verifies |
| MANIFEST-SUM-0069 | manifest | PASS | checksum row candidates/transported_object_registry.csv verifies |
| MANIFEST-SUM-0070 | manifest | PASS | checksum row challenges/COUNTEREXAMPLE_CATALOG.md verifies |
| MANIFEST-SUM-0071 | manifest | PASS | checksum row challenges/CST-EXP-04_ADVERSARIAL_SYNTHESIS.md verifies |
| MANIFEST-SUM-0072 | manifest | PASS | checksum row challenges/INTERNAL_STRESS_SYNTHESIS.md verifies |
| MANIFEST-SUM-0073 | manifest | PASS | checksum row challenges/README.md verifies |
| MANIFEST-SUM-0074 | manifest | PASS | checksum row challenges/SURVIVOR_SHORTLIST.md verifies |
| MANIFEST-SUM-0075 | manifest | PASS | checksum row challenges/candidate_stress/INDEX.md verifies |
| MANIFEST-SUM-0076 | manifest | PASS | checksum row challenges/candidate_stress/TS-01.md verifies |
| MANIFEST-SUM-0077 | manifest | PASS | checksum row challenges/candidate_stress/TS-02.md verifies |
| MANIFEST-SUM-0078 | manifest | PASS | checksum row challenges/candidate_stress/TS-03.md verifies |
| MANIFEST-SUM-0079 | manifest | PASS | checksum row challenges/candidate_stress/TS-04.md verifies |
| MANIFEST-SUM-0080 | manifest | PASS | checksum row challenges/candidate_stress/TS-05.md verifies |
| MANIFEST-SUM-0081 | manifest | PASS | checksum row challenges/candidate_stress/TS-06.md verifies |
| MANIFEST-SUM-0082 | manifest | PASS | checksum row challenges/candidate_stress/TS-07.md verifies |
| MANIFEST-SUM-0083 | manifest | PASS | checksum row challenges/candidate_stress/TS-08.md verifies |
| MANIFEST-SUM-0084 | manifest | PASS | checksum row challenges/candidate_stress/TS-09.md verifies |
| MANIFEST-SUM-0085 | manifest | PASS | checksum row challenges/candidate_stress/TS-10.md verifies |
| MANIFEST-SUM-0086 | manifest | PASS | checksum row challenges/counterexamples/.gitkeep verifies |
| MANIFEST-SUM-0087 | manifest | PASS | checksum row challenges/counterexamples/HC-01.md verifies |
| MANIFEST-SUM-0088 | manifest | PASS | checksum row challenges/counterexamples/HC-02.md verifies |
| MANIFEST-SUM-0089 | manifest | PASS | checksum row challenges/counterexamples/HC-03.md verifies |
| MANIFEST-SUM-0090 | manifest | PASS | checksum row challenges/counterexamples/HC-04.md verifies |
| MANIFEST-SUM-0091 | manifest | PASS | checksum row challenges/counterexamples/HC-05.md verifies |
| MANIFEST-SUM-0092 | manifest | PASS | checksum row challenges/counterexamples/HC-06.md verifies |
| MANIFEST-SUM-0093 | manifest | PASS | checksum row challenges/counterexamples/HC-07.md verifies |
| MANIFEST-SUM-0094 | manifest | PASS | checksum row challenges/counterexamples/HC-08.md verifies |
| MANIFEST-SUM-0095 | manifest | PASS | checksum row challenges/counterexamples/HC-09.md verifies |
| MANIFEST-SUM-0096 | manifest | PASS | checksum row challenges/counterexamples/HC-10.md verifies |
| MANIFEST-SUM-0097 | manifest | PASS | checksum row challenges/counterexamples/HC-11.md verifies |
| MANIFEST-SUM-0098 | manifest | PASS | checksum row challenges/counterexamples/HC-12.md verifies |
| MANIFEST-SUM-0099 | manifest | PASS | checksum row challenges/counterexamples/HC-13.md verifies |
| MANIFEST-SUM-0100 | manifest | PASS | checksum row challenges/counterexamples/HC-14.md verifies |
| MANIFEST-SUM-0101 | manifest | PASS | checksum row challenges/counterexamples/HC-15.md verifies |
| MANIFEST-SUM-0102 | manifest | PASS | checksum row challenges/counterexamples/HC-16.md verifies |
| MANIFEST-SUM-0103 | manifest | PASS | checksum row challenges/counterexamples/HC-17.md verifies |
| MANIFEST-SUM-0104 | manifest | PASS | checksum row challenges/counterexamples/HC-18.md verifies |
| MANIFEST-SUM-0105 | manifest | PASS | checksum row challenges/external_literature/.gitkeep verifies |
| MANIFEST-SUM-0106 | manifest | PASS | checksum row challenges/external_literature/LITERATURE_CHALLENGE_MAP.md verifies |
| MANIFEST-SUM-0107 | manifest | PASS | checksum row challenges/external_literature/SEARCH_AND_SCOPE_LOG.md verifies |
| MANIFEST-SUM-0108 | manifest | PASS | checksum row challenges/external_literature/SOURCE_REGISTRY.csv verifies |
| MANIFEST-SUM-0109 | manifest | PASS | checksum row challenges/no_go_conjectures/.gitkeep verifies |
| MANIFEST-SUM-0110 | manifest | PASS | checksum row challenges/no_go_conjectures/INDEX.md verifies |
| MANIFEST-SUM-0111 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-01.md verifies |
| MANIFEST-SUM-0112 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-02.md verifies |
| MANIFEST-SUM-0113 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-03.md verifies |
| MANIFEST-SUM-0114 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-04.md verifies |
| MANIFEST-SUM-0115 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-05.md verifies |
| MANIFEST-SUM-0116 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-06.md verifies |
| MANIFEST-SUM-0117 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-07.md verifies |
| MANIFEST-SUM-0118 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-08.md verifies |
| MANIFEST-SUM-0119 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-09.md verifies |
| MANIFEST-SUM-0120 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-10.md verifies |
| MANIFEST-SUM-0121 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-11.md verifies |
| MANIFEST-SUM-0122 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-12.md verifies |
| MANIFEST-SUM-0123 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-13.md verifies |
| MANIFEST-SUM-0124 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-14.md verifies |
| MANIFEST-SUM-0125 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-15.md verifies |
| MANIFEST-SUM-0126 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-16.md verifies |
| MANIFEST-SUM-0127 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-17.md verifies |
| MANIFEST-SUM-0128 | manifest | PASS | checksum row challenges/no_go_conjectures/NG-18.md verifies |
| MANIFEST-SUM-0129 | manifest | PASS | checksum row challenges/red_team/INDEX.md verifies |
| MANIFEST-SUM-0130 | manifest | PASS | checksum row challenges/red_team/RT-01.md verifies |
| MANIFEST-SUM-0131 | manifest | PASS | checksum row challenges/red_team/RT-02.md verifies |
| MANIFEST-SUM-0132 | manifest | PASS | checksum row challenges/red_team/RT-03.md verifies |
| MANIFEST-SUM-0133 | manifest | PASS | checksum row challenges/red_team/RT-04.md verifies |
| MANIFEST-SUM-0134 | manifest | PASS | checksum row challenges/red_team/RT-05.md verifies |
| MANIFEST-SUM-0135 | manifest | PASS | checksum row challenges/red_team/RT-06.md verifies |
| MANIFEST-SUM-0136 | manifest | PASS | checksum row challenges/red_team/RT-07.md verifies |
| MANIFEST-SUM-0137 | manifest | PASS | checksum row challenges/survivor_architecture.dot verifies |
| MANIFEST-SUM-0138 | manifest | PASS | checksum row challenges/survivor_architecture.png verifies |
| MANIFEST-SUM-0139 | manifest | PASS | checksum row challenges/survivor_architecture.svg verifies |
| MANIFEST-SUM-0140 | manifest | PASS | checksum row changelog/.gitkeep verifies |
| MANIFEST-SUM-0141 | manifest | PASS | checksum row changelog/CST-EXP-00.md verifies |
| MANIFEST-SUM-0142 | manifest | PASS | checksum row changelog/CST-EXP-01.md verifies |
| MANIFEST-SUM-0143 | manifest | PASS | checksum row changelog/CST-EXP-02.md verifies |
| MANIFEST-SUM-0144 | manifest | PASS | checksum row changelog/CST-EXP-03.md verifies |
| MANIFEST-SUM-0145 | manifest | PASS | checksum row changelog/CST-EXP-05.md verifies |
| MANIFEST-SUM-0146 | manifest | PASS | checksum row changelog/CST-EXP-06.md verifies |
| MANIFEST-SUM-0147 | manifest | PASS | checksum row changelog/CST-TT-00.md verifies |
| MANIFEST-SUM-0148 | manifest | PASS | checksum row changelog/CST-TT-01.md verifies |
| MANIFEST-SUM-0149 | manifest | PASS | checksum row changelog/CST-TT-02.md verifies |
| MANIFEST-SUM-0150 | manifest | PASS | checksum row changelog/CST-TT-03.md verifies |
| MANIFEST-SUM-0151 | manifest | PASS | checksum row changelog/CST-TT-04.md verifies |
| MANIFEST-SUM-0152 | manifest | PASS | checksum row changelog/CST-TT-05.md verifies |
| MANIFEST-SUM-0153 | manifest | PASS | checksum row charter/.gitkeep verifies |
| MANIFEST-SUM-0154 | manifest | PASS | checksum row charter/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-SUM-0155 | manifest | PASS | checksum row charter/NONGOALS_AND_SCOPE_GUARDS.md verifies |
| MANIFEST-SUM-0156 | manifest | PASS | checksum row charter/PROJECT_CHARTER.md verifies |
| MANIFEST-SUM-0157 | manifest | PASS | checksum row charter/TYPED_PROBLEM_STATEMENT.md verifies |
| MANIFEST-SUM-0158 | manifest | PASS | checksum row config/REPRODUCIBILITY.json verifies |
| MANIFEST-SUM-0159 | manifest | PASS | checksum row corpus/README.md verifies |
| MANIFEST-SUM-0160 | manifest | PASS | checksum row corpus/asset_atlas/.gitkeep verifies |
| MANIFEST-SUM-0161 | manifest | PASS | checksum row corpus/asset_atlas/ASSET_ATLAS.md verifies |
| MANIFEST-SUM-0162 | manifest | PASS | checksum row corpus/asset_atlas/ASSET_PROVENANCE.md verifies |
| MANIFEST-SUM-0163 | manifest | PASS | checksum row corpus/asset_atlas/COMPOSITION_NOTES.md verifies |
| MANIFEST-SUM-0164 | manifest | PASS | checksum row corpus/asset_atlas/DEPENDENCY_GRAPH_GUIDE.md verifies |
| MANIFEST-SUM-0165 | manifest | PASS | checksum row corpus/asset_atlas/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-SUM-0166 | manifest | PASS | checksum row corpus/asset_atlas/LEXICAL_DEPENDENCY_METHOD.md verifies |
| MANIFEST-SUM-0167 | manifest | PASS | checksum row corpus/asset_atlas/PAPER_COVERAGE_AUDIT.md verifies |
| MANIFEST-SUM-0168 | manifest | PASS | checksum row corpus/asset_atlas/STATEMENT_SELECTION_METHOD.md verifies |
| MANIFEST-SUM-0169 | manifest | PASS | checksum row corpus/asset_atlas/dependency_graph.dot verifies |
| MANIFEST-SUM-0170 | manifest | PASS | checksum row corpus/asset_atlas/dependency_graph.mmd verifies |
| MANIFEST-SUM-0171 | manifest | PASS | checksum row corpus/asset_atlas/dependency_graph.png verifies |
| MANIFEST-SUM-0172 | manifest | PASS | checksum row corpus/asset_atlas/dependency_graph.svg verifies |
| MANIFEST-SUM-0173 | manifest | PASS | checksum row corpus/asset_atlas/dependency_graph_edges.csv verifies |
| MANIFEST-SUM-0174 | manifest | PASS | checksum row corpus/asset_atlas/dependency_graph_nodes.csv verifies |
| MANIFEST-SUM-0175 | manifest | PASS | checksum row corpus/clause_cards/C1.md verifies |
| MANIFEST-SUM-0176 | manifest | PASS | checksum row corpus/clause_cards/C2.md verifies |
| MANIFEST-SUM-0177 | manifest | PASS | checksum row corpus/clause_cards/C3.md verifies |
| MANIFEST-SUM-0178 | manifest | PASS | checksum row corpus/clause_cards/C4.md verifies |
| MANIFEST-SUM-0179 | manifest | PASS | checksum row corpus/clause_cards/C5.md verifies |
| MANIFEST-SUM-0180 | manifest | PASS | checksum row corpus/clause_cards/C6.md verifies |
| MANIFEST-SUM-0181 | manifest | PASS | checksum row corpus/clause_cards/C7.md verifies |
| MANIFEST-SUM-0182 | manifest | PASS | checksum row corpus/clause_cards/C8.md verifies |
| MANIFEST-SUM-0183 | manifest | PASS | checksum row corpus/clause_cards/INDEX.md verifies |
| MANIFEST-SUM-0184 | manifest | PASS | checksum row corpus/consciousness_repo/ASSET_MAP.md verifies |
| MANIFEST-SUM-0185 | manifest | PASS | checksum row corpus/consciousness_repo/VERIFICATION.md verifies |
| MANIFEST-SUM-0186 | manifest | PASS | checksum row corpus/consciousness_repo/consciousness_repo_inventory.csv verifies |
| MANIFEST-SUM-0187 | manifest | PASS | checksum row corpus/consciousness_repo/formal_inventory.csv verifies |
| MANIFEST-SUM-0188 | manifest | PASS | checksum row corpus/consciousness_repo/test_inventory.csv verifies |
| MANIFEST-SUM-0189 | manifest | PASS | checksum row corpus/machine_index/README.md verifies |
| MANIFEST-SUM-0190 | manifest | PASS | checksum row corpus/machine_index/all_statement_index.csv verifies |
| MANIFEST-SUM-0191 | manifest | PASS | checksum row corpus/machine_index/paper_inventory.csv verifies |
| MANIFEST-SUM-0192 | manifest | PASS | checksum row corpus/paper_cards/.gitkeep verifies |
| MANIFEST-SUM-0193 | manifest | PASS | checksum row corpus/paper_cards/INDEX.csv verifies |
| MANIFEST-SUM-0194 | manifest | PASS | checksum row corpus/paper_cards/INDEX.md verifies |
| MANIFEST-SUM-0195 | manifest | PASS | checksum row corpus/paper_cards/P01.md verifies |
| MANIFEST-SUM-0196 | manifest | PASS | checksum row corpus/paper_cards/P02.md verifies |
| MANIFEST-SUM-0197 | manifest | PASS | checksum row corpus/paper_cards/P03.md verifies |
| MANIFEST-SUM-0198 | manifest | PASS | checksum row corpus/paper_cards/P04.md verifies |
| MANIFEST-SUM-0199 | manifest | PASS | checksum row corpus/paper_cards/P05.md verifies |
| MANIFEST-SUM-0200 | manifest | PASS | checksum row corpus/paper_cards/P06.md verifies |
| MANIFEST-SUM-0201 | manifest | PASS | checksum row corpus/paper_cards/P07.md verifies |
| MANIFEST-SUM-0202 | manifest | PASS | checksum row corpus/paper_cards/P08.md verifies |
| MANIFEST-SUM-0203 | manifest | PASS | checksum row corpus/paper_cards/P09.md verifies |
| MANIFEST-SUM-0204 | manifest | PASS | checksum row corpus/paper_cards/P10.md verifies |
| MANIFEST-SUM-0205 | manifest | PASS | checksum row corpus/paper_cards/P11.md verifies |
| MANIFEST-SUM-0206 | manifest | PASS | checksum row corpus/paper_cards/P12.md verifies |
| MANIFEST-SUM-0207 | manifest | PASS | checksum row corpus/paper_cards/P13.md verifies |
| MANIFEST-SUM-0208 | manifest | PASS | checksum row corpus/paper_cards/P14.md verifies |
| MANIFEST-SUM-0209 | manifest | PASS | checksum row corpus/paper_cards/P15.md verifies |
| MANIFEST-SUM-0210 | manifest | PASS | checksum row corpus/paper_cards/P16.md verifies |
| MANIFEST-SUM-0211 | manifest | PASS | checksum row corpus/paper_cards/P17.md verifies |
| MANIFEST-SUM-0212 | manifest | PASS | checksum row corpus/paper_cards/P18.md verifies |
| MANIFEST-SUM-0213 | manifest | PASS | checksum row corpus/paper_cards/P19.md verifies |
| MANIFEST-SUM-0214 | manifest | PASS | checksum row corpus/paper_cards/P20.md verifies |
| MANIFEST-SUM-0215 | manifest | PASS | checksum row corpus/paper_cards/P21.md verifies |
| MANIFEST-SUM-0216 | manifest | PASS | checksum row corpus/paper_cards/P22.md verifies |
| MANIFEST-SUM-0217 | manifest | PASS | checksum row corpus/paper_cards/P23.md verifies |
| MANIFEST-SUM-0218 | manifest | PASS | checksum row corpus/paper_cards/P24.md verifies |
| MANIFEST-SUM-0219 | manifest | PASS | checksum row corpus/paper_cards/P25.md verifies |
| MANIFEST-SUM-0220 | manifest | PASS | checksum row corpus/paper_cards/P26.md verifies |
| MANIFEST-SUM-0221 | manifest | PASS | checksum row corpus/paper_cards/P27.md verifies |
| MANIFEST-SUM-0222 | manifest | PASS | checksum row corpus/paper_cards/P28.md verifies |
| MANIFEST-SUM-0223 | manifest | PASS | checksum row corpus/paper_cards/P29.md verifies |
| MANIFEST-SUM-0224 | manifest | PASS | checksum row corpus/paper_cards/P30.md verifies |
| MANIFEST-SUM-0225 | manifest | PASS | checksum row corpus/paper_cards/P31.md verifies |
| MANIFEST-SUM-0226 | manifest | PASS | checksum row corpus/paper_cards/P32.md verifies |
| MANIFEST-SUM-0227 | manifest | PASS | checksum row corpus/paper_cards/P33.md verifies |
| MANIFEST-SUM-0228 | manifest | PASS | checksum row corpus/paper_cards/P34.md verifies |
| MANIFEST-SUM-0229 | manifest | PASS | checksum row corpus/paper_cards/P35.md verifies |
| MANIFEST-SUM-0230 | manifest | PASS | checksum row corpus/paper_cards/P36.md verifies |
| MANIFEST-SUM-0231 | manifest | PASS | checksum row corpus/paper_cards/P37.md verifies |
| MANIFEST-SUM-0232 | manifest | PASS | checksum row corpus/paper_cards/P38.md verifies |
| MANIFEST-SUM-0233 | manifest | PASS | checksum row corpus/paper_cards/P39.md verifies |
| MANIFEST-SUM-0234 | manifest | PASS | checksum row corpus/paper_cards/P40.md verifies |
| MANIFEST-SUM-0235 | manifest | PASS | checksum row corpus/paper_cards/P41.md verifies |
| MANIFEST-SUM-0236 | manifest | PASS | checksum row corpus/paper_cards/P42.md verifies |
| MANIFEST-SUM-0237 | manifest | PASS | checksum row corpus/paper_cards/P43.md verifies |
| MANIFEST-SUM-0238 | manifest | PASS | checksum row corpus/paper_cards/P44.md verifies |
| MANIFEST-SUM-0239 | manifest | PASS | checksum row corpus/paper_cards/P45.md verifies |
| MANIFEST-SUM-0240 | manifest | PASS | checksum row corpus/paper_cards/P46.md verifies |
| MANIFEST-SUM-0241 | manifest | PASS | checksum row corpus/paper_cards/P47.md verifies |
| MANIFEST-SUM-0242 | manifest | PASS | checksum row corpus/paper_cards/P48.md verifies |
| MANIFEST-SUM-0243 | manifest | PASS | checksum row corpus/paper_cards/P49.md verifies |
| MANIFEST-SUM-0244 | manifest | PASS | checksum row corpus/paper_cards/P50.md verifies |
| MANIFEST-SUM-0245 | manifest | PASS | checksum row corpus/paper_cards/P51.md verifies |
| MANIFEST-SUM-0246 | manifest | PASS | checksum row corpus/paper_cards/P52.md verifies |
| MANIFEST-SUM-0247 | manifest | PASS | checksum row corpus/paper_cards/P53.md verifies |
| MANIFEST-SUM-0248 | manifest | PASS | checksum row corpus/paper_cards/P54.md verifies |
| MANIFEST-SUM-0249 | manifest | PASS | checksum row corpus/paper_cards/P55.md verifies |
| MANIFEST-SUM-0250 | manifest | PASS | checksum row corpus/paper_cards/P56.md verifies |
| MANIFEST-SUM-0251 | manifest | PASS | checksum row corpus/paper_cards/P57.md verifies |
| MANIFEST-SUM-0252 | manifest | PASS | checksum row corpus/paper_cards/P58.md verifies |
| MANIFEST-SUM-0253 | manifest | PASS | checksum row corpus/paper_cards/P59.md verifies |
| MANIFEST-SUM-0254 | manifest | PASS | checksum row corpus/paper_cards/P60.md verifies |
| MANIFEST-SUM-0255 | manifest | PASS | checksum row corpus/theorem_cards/.gitkeep verifies |
| MANIFEST-SUM-0256 | manifest | PASS | checksum row corpus/theorem_cards/INDEX.md verifies |
| MANIFEST-SUM-0257 | manifest | PASS | checksum row corpus/theorem_cards/P06-AOR.md verifies |
| MANIFEST-SUM-0258 | manifest | PASS | checksum row corpus/theorem_cards/P14-PT.md verifies |
| MANIFEST-SUM-0259 | manifest | PASS | checksum row corpus/theorem_cards/P18-RE.md verifies |
| MANIFEST-SUM-0260 | manifest | PASS | checksum row corpus/theorem_cards/P30-F19.md verifies |
| MANIFEST-SUM-0261 | manifest | PASS | checksum row corpus/theorem_cards/P44-CD.md verifies |
| MANIFEST-SUM-0262 | manifest | PASS | checksum row corpus/theorem_cards/P50-CF.md verifies |
| MANIFEST-SUM-0263 | manifest | PASS | checksum row corpus/theorem_cards/P52-NS.md verifies |
| MANIFEST-SUM-0264 | manifest | PASS | checksum row corpus/theorem_cards/T01.md verifies |
| MANIFEST-SUM-0265 | manifest | PASS | checksum row corpus/theorem_cards/T02.md verifies |
| MANIFEST-SUM-0266 | manifest | PASS | checksum row corpus/theorem_cards/T03.md verifies |
| MANIFEST-SUM-0267 | manifest | PASS | checksum row corpus/theorem_cards/T04.md verifies |
| MANIFEST-SUM-0268 | manifest | PASS | checksum row corpus/theorem_cards/T05.md verifies |
| MANIFEST-SUM-0269 | manifest | PASS | checksum row corpus/theorem_cards/T06.md verifies |
| MANIFEST-SUM-0270 | manifest | PASS | checksum row corpus/theorem_cards/T07.md verifies |
| MANIFEST-SUM-0271 | manifest | PASS | checksum row corpus/theorem_cards/T08.md verifies |
| MANIFEST-SUM-0272 | manifest | PASS | checksum row corpus/theorem_cards/T09.md verifies |
| MANIFEST-SUM-0273 | manifest | PASS | checksum row corpus/theorem_cards/T10.md verifies |
| MANIFEST-SUM-0274 | manifest | PASS | checksum row corpus/theorem_cards/T11.md verifies |
| MANIFEST-SUM-0275 | manifest | PASS | checksum row corpus/theorem_cards/T12.md verifies |
| MANIFEST-SUM-0276 | manifest | PASS | checksum row corpus/theorem_cards/T13.md verifies |
| MANIFEST-SUM-0277 | manifest | PASS | checksum row corpus/theorem_cards/T14.md verifies |
| MANIFEST-SUM-0278 | manifest | PASS | checksum row corpus/theorem_cards/T15.md verifies |
| MANIFEST-SUM-0279 | manifest | PASS | checksum row corpus/theorem_cards/T16.md verifies |
| MANIFEST-SUM-0280 | manifest | PASS | checksum row corpus/theorem_cards/T17.md verifies |
| MANIFEST-SUM-0281 | manifest | PASS | checksum row corpus/theorem_cards/T18.md verifies |
| MANIFEST-SUM-0282 | manifest | PASS | checksum row docs/ACYCLIC_GLUING_THEOREM.md verifies |
| MANIFEST-SUM-0283 | manifest | PASS | checksum row docs/ASSUMPTION_AND_CLAIM_CEILING.md verifies |
| MANIFEST-SUM-0284 | manifest | PASS | checksum row docs/AUTONOMY_CONTROL_SUITE.md verifies |
| MANIFEST-SUM-0285 | manifest | PASS | checksum row docs/C6_TEMPORAL_SUBSTANCE.md verifies |
| MANIFEST-SUM-0286 | manifest | PASS | checksum row docs/CIRCULARITY_AND_TYPING_POLICY.md verifies |
| MANIFEST-SUM-0287 | manifest | PASS | checksum row docs/CORRIDOR_COMPOSITION_THEOREM.md verifies |
| MANIFEST-SUM-0288 | manifest | PASS | checksum row docs/CORRIDOR_CONTROL_SUITE.md verifies |
| MANIFEST-SUM-0289 | manifest | PASS | checksum row docs/COUNTERMODEL_MINIMALITY.md verifies |
| MANIFEST-SUM-0290 | manifest | PASS | checksum row docs/CST-TT-04_DECISION_GATE.md verifies |
| MANIFEST-SUM-0291 | manifest | PASS | checksum row docs/CST-TT-05_DECISION_GATE.md verifies |
| MANIFEST-SUM-0292 | manifest | PASS | checksum row docs/DIRECT_SUCCESSOR_RESULT.md verifies |
| MANIFEST-SUM-0293 | manifest | PASS | checksum row docs/FINITE_HORIZON_LIVENESS_BOUNDARY.md verifies |
| MANIFEST-SUM-0294 | manifest | PASS | checksum row docs/FORMALIZATION_CONTRACT.md verifies |
| MANIFEST-SUM-0295 | manifest | PASS | checksum row docs/HANDOFF_ALIGNED_PACKAGE.md verifies |
| MANIFEST-SUM-0296 | manifest | PASS | checksum row docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md verifies |
| MANIFEST-SUM-0297 | manifest | PASS | checksum row docs/INTEGRATED_PACKAGE_SEMANTICS.md verifies |
| MANIFEST-SUM-0298 | manifest | PASS | checksum row docs/INTEGRATED_TEMPORAL_FIACH_THEOREM.md verifies |
| MANIFEST-SUM-0299 | manifest | PASS | checksum row docs/LANE_INDEPENDENCE_AUDIT.md verifies |
| MANIFEST-SUM-0300 | manifest | PASS | checksum row docs/MEMORY_OR_FLATNESS_THEOREM.md verifies |
| MANIFEST-SUM-0301 | manifest | PASS | checksum row docs/NEGATIVE_KERNEL.md verifies |
| MANIFEST-SUM-0302 | manifest | PASS | checksum row docs/NONREDUNDANCY_INTERVENTION_AUDIT.md verifies |
| MANIFEST-SUM-0303 | manifest | PASS | checksum row docs/OVERLAP_DIRECT_SUCCESSOR_COMPARISON.md verifies |
| MANIFEST-SUM-0304 | manifest | PASS | checksum row docs/PACKAGE_CONTROL_SUITE.md verifies |
| MANIFEST-SUM-0305 | manifest | PASS | checksum row docs/PHASE_BOUNDARY.md verifies |
| MANIFEST-SUM-0306 | manifest | PASS | checksum row docs/POST_WITHDRAWAL_AUTONOMY.md verifies |
| MANIFEST-SUM-0307 | manifest | PASS | checksum row docs/RECORD_ARROW_TRANSPORT.md verifies |
| MANIFEST-SUM-0308 | manifest | PASS | checksum row docs/RESTORE_AND_BUILD.md verifies |
| MANIFEST-SUM-0309 | manifest | PASS | checksum row docs/ROUTE_DISCIPLINE_AND_CONFLUENCE.md verifies |
| MANIFEST-SUM-0310 | manifest | PASS | checksum row docs/STAGED_PACKAGE_ASSEMBLY.md verifies |
| MANIFEST-SUM-0311 | manifest | PASS | checksum row docs/TARGET_FREEZE.md verifies |
| MANIFEST-SUM-0312 | manifest | PASS | checksum row docs/TEMPORAL_AMENDMENT_MAP.md verifies |
| MANIFEST-SUM-0313 | manifest | PASS | checksum row docs/TEMPORAL_CORRIDOR_SEMANTICS.md verifies |
| MANIFEST-SUM-0314 | manifest | PASS | checksum row docs/THEOREM_AND_TOY_REGISTRY.md verifies |
| MANIFEST-SUM-0315 | manifest | PASS | checksum row docs/TRANSPORT_CONTROL_SUITE.md verifies |
| MANIFEST-SUM-0316 | manifest | PASS | checksum row examples/scaffold/aligned_package_certificate.scaffold.json verifies |
| MANIFEST-SUM-0317 | manifest | PASS | checksum row examples/scaffold/aligned_staged_package_certificate.scaffold.json verifies |
| MANIFEST-SUM-0318 | manifest | PASS | checksum row examples/scaffold/ancestry_certificate.scaffold.json verifies |
| MANIFEST-SUM-0319 | manifest | PASS | checksum row examples/scaffold/autonomy_certificate.scaffold.json verifies |
| MANIFEST-SUM-0320 | manifest | PASS | checksum row examples/scaffold/autonomy_control_certificate.scaffold.json verifies |
| MANIFEST-SUM-0321 | manifest | PASS | checksum row examples/scaffold/corridor_composition_certificate.scaffold.json verifies |
| MANIFEST-SUM-0322 | manifest | PASS | checksum row examples/scaffold/corridor_control_certificate.scaffold.json verifies |
| MANIFEST-SUM-0323 | manifest | PASS | checksum row examples/scaffold/countermodel_certificate.scaffold.json verifies |
| MANIFEST-SUM-0324 | manifest | PASS | checksum row examples/scaffold/direct_successor.scaffold.json verifies |
| MANIFEST-SUM-0325 | manifest | PASS | checksum row examples/scaffold/direct_successor_landed.scaffold.json verifies |
| MANIFEST-SUM-0326 | manifest | PASS | checksum row examples/scaffold/direct_successor_path_certificate.scaffold.json verifies |
| MANIFEST-SUM-0327 | manifest | PASS | checksum row examples/scaffold/fiach_lane_control_certificate.scaffold.json verifies |
| MANIFEST-SUM-0328 | manifest | PASS | checksum row examples/scaffold/memory_repair_certificate.scaffold.json verifies |
| MANIFEST-SUM-0329 | manifest | PASS | checksum row examples/scaffold/package_certificate.scaffold.json verifies |
| MANIFEST-SUM-0330 | manifest | PASS | checksum row examples/scaffold/package_control_certificate.scaffold.json verifies |
| MANIFEST-SUM-0331 | manifest | PASS | checksum row examples/scaffold/post_withdrawal_autonomy_certificate.scaffold.json verifies |
| MANIFEST-SUM-0332 | manifest | PASS | checksum row examples/scaffold/record_arrow_certificate.scaffold.json verifies |
| MANIFEST-SUM-0333 | manifest | PASS | checksum row examples/scaffold/route_discipline_certificate.scaffold.json verifies |
| MANIFEST-SUM-0334 | manifest | PASS | checksum row examples/scaffold/staged_package_certificate.scaffold.json verifies |
| MANIFEST-SUM-0335 | manifest | PASS | checksum row examples/scaffold/strict_temporal_corridor_certificate.scaffold.json verifies |
| MANIFEST-SUM-0336 | manifest | PASS | checksum row examples/scaffold/temporal_corridor.scaffold.json verifies |
| MANIFEST-SUM-0337 | manifest | PASS | checksum row examples/scaffold/temporal_fiach_certificate.scaffold.json verifies |
| MANIFEST-SUM-0338 | manifest | PASS | checksum row examples/scaffold/temporal_fiach_landed_certificate.scaffold.json verifies |
| MANIFEST-SUM-0339 | manifest | PASS | checksum row examples/scaffold/temporal_signature.scaffold.json verifies |
| MANIFEST-SUM-0340 | manifest | PASS | checksum row examples/scaffold/temporal_transport_certificate.scaffold.json verifies |
| MANIFEST-SUM-0341 | manifest | PASS | checksum row examples/scaffold/transport_control_certificate.scaffold.json verifies |
| MANIFEST-SUM-0342 | manifest | PASS | checksum row feasibility/ASSUMPTION_LADDER.md verifies |
| MANIFEST-SUM-0343 | manifest | PASS | checksum row feasibility/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-SUM-0344 | manifest | PASS | checksum row feasibility/FINITE_CORE_SEMANTICS.md verifies |
| MANIFEST-SUM-0345 | manifest | PASS | checksum row feasibility/FORMALIZATION_TRACTABILITY.md verifies |
| MANIFEST-SUM-0346 | manifest | PASS | checksum row feasibility/LANDING_BUNDLES.md verifies |
| MANIFEST-SUM-0347 | manifest | PASS | checksum row feasibility/MODEL_SUITE.md verifies |
| MANIFEST-SUM-0348 | manifest | PASS | checksum row feasibility/README.md verifies |
| MANIFEST-SUM-0349 | manifest | PASS | checksum row feasibility/RECONNAISSANCE_SYNTHESIS.md verifies |
| MANIFEST-SUM-0350 | manifest | PASS | checksum row feasibility/landing_architecture.dot verifies |
| MANIFEST-SUM-0351 | manifest | PASS | checksum row feasibility/landing_architecture.png verifies |
| MANIFEST-SUM-0352 | manifest | PASS | checksum row feasibility/landing_architecture.svg verifies |
| MANIFEST-SUM-0353 | manifest | PASS | checksum row feasibility/model_cards/MF-01.md verifies |
| MANIFEST-SUM-0354 | manifest | PASS | checksum row feasibility/model_cards/MF-02.md verifies |
| MANIFEST-SUM-0355 | manifest | PASS | checksum row feasibility/model_cards/MF-03.md verifies |
| MANIFEST-SUM-0356 | manifest | PASS | checksum row feasibility/model_cards/MF-04.md verifies |
| MANIFEST-SUM-0357 | manifest | PASS | checksum row feasibility/model_cards/MF-05.md verifies |
| MANIFEST-SUM-0358 | manifest | PASS | checksum row feasibility/model_cards/MF-06.md verifies |
| MANIFEST-SUM-0359 | manifest | PASS | checksum row feasibility/model_cards/MF-07.md verifies |
| MANIFEST-SUM-0360 | manifest | PASS | checksum row feasibility/model_cards/MF-08.md verifies |
| MANIFEST-SUM-0361 | manifest | PASS | checksum row feasibility/model_cards/MF-09.md verifies |
| MANIFEST-SUM-0362 | manifest | PASS | checksum row feasibility/model_cards/MF-10.md verifies |
| MANIFEST-SUM-0363 | manifest | PASS | checksum row feasibility/theorem_prospectus/.gitkeep verifies |
| MANIFEST-SUM-0364 | manifest | PASS | checksum row feasibility/theorem_prospectus/INDEX.md verifies |
| MANIFEST-SUM-0365 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-01.md verifies |
| MANIFEST-SUM-0366 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-02.md verifies |
| MANIFEST-SUM-0367 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-03.md verifies |
| MANIFEST-SUM-0368 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-04.md verifies |
| MANIFEST-SUM-0369 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-05.md verifies |
| MANIFEST-SUM-0370 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-06.md verifies |
| MANIFEST-SUM-0371 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-07.md verifies |
| MANIFEST-SUM-0372 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-08.md verifies |
| MANIFEST-SUM-0373 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-09.md verifies |
| MANIFEST-SUM-0374 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-10.md verifies |
| MANIFEST-SUM-0375 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-11.md verifies |
| MANIFEST-SUM-0376 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-12.md verifies |
| MANIFEST-SUM-0377 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-13.md verifies |
| MANIFEST-SUM-0378 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-14.md verifies |
| MANIFEST-SUM-0379 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-15.md verifies |
| MANIFEST-SUM-0380 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-16.md verifies |
| MANIFEST-SUM-0381 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-17.md verifies |
| MANIFEST-SUM-0382 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-18.md verifies |
| MANIFEST-SUM-0383 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-19.md verifies |
| MANIFEST-SUM-0384 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-20.md verifies |
| MANIFEST-SUM-0385 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-21.md verifies |
| MANIFEST-SUM-0386 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-22.md verifies |
| MANIFEST-SUM-0387 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-23.md verifies |
| MANIFEST-SUM-0388 | manifest | PASS | checksum row feasibility/theorem_prospectus/TH-24.md verifies |
| MANIFEST-SUM-0389 | manifest | PASS | checksum row feasibility/toy_program_prospectus/.gitkeep verifies |
| MANIFEST-SUM-0390 | manifest | PASS | checksum row feasibility/toy_program_prospectus/INDEX.md verifies |
| MANIFEST-SUM-0391 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-01.md verifies |
| MANIFEST-SUM-0392 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-02.md verifies |
| MANIFEST-SUM-0393 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-03.md verifies |
| MANIFEST-SUM-0394 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-04.md verifies |
| MANIFEST-SUM-0395 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-05.md verifies |
| MANIFEST-SUM-0396 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-06.md verifies |
| MANIFEST-SUM-0397 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-07.md verifies |
| MANIFEST-SUM-0398 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-08.md verifies |
| MANIFEST-SUM-0399 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-09.md verifies |
| MANIFEST-SUM-0400 | manifest | PASS | checksum row feasibility/toy_program_prospectus/TP-10.md verifies |
| MANIFEST-SUM-0401 | manifest | PASS | checksum row formal/README.md verifies |
| MANIFEST-SUM-0402 | manifest | PASS | checksum row formal/TOOLCHAIN_STATUS.json verifies |
| MANIFEST-SUM-0403 | manifest | PASS | checksum row formal/certificates/README.md verifies |
| MANIFEST-SUM-0404 | manifest | PASS | checksum row formal/certificates/arrow/ARROW-POS-01.certificate.json verifies |
| MANIFEST-SUM-0405 | manifest | PASS | checksum row formal/certificates/autonomy/AUT-POS-01.certificate.json verifies |
| MANIFEST-SUM-0406 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C01.certificate.json verifies |
| MANIFEST-SUM-0407 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C02.certificate.json verifies |
| MANIFEST-SUM-0408 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C03.certificate.json verifies |
| MANIFEST-SUM-0409 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C04.certificate.json verifies |
| MANIFEST-SUM-0410 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C05.certificate.json verifies |
| MANIFEST-SUM-0411 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C06.certificate.json verifies |
| MANIFEST-SUM-0412 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C07.certificate.json verifies |
| MANIFEST-SUM-0413 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C08.certificate.json verifies |
| MANIFEST-SUM-0414 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C09.certificate.json verifies |
| MANIFEST-SUM-0415 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C10.certificate.json verifies |
| MANIFEST-SUM-0416 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C11.certificate.json verifies |
| MANIFEST-SUM-0417 | manifest | PASS | checksum row formal/certificates/autonomy/controls/AUT-C12.certificate.json verifies |
| MANIFEST-SUM-0418 | manifest | PASS | checksum row formal/certificates/corridors/COR-COMP-01.certificate.json verifies |
| MANIFEST-SUM-0419 | manifest | PASS | checksum row formal/certificates/corridors/COR-POS-01.certificate.json verifies |
| MANIFEST-SUM-0420 | manifest | PASS | checksum row formal/certificates/corridors/COR-POS-02-COMPOSED.certificate.json verifies |
| MANIFEST-SUM-0421 | manifest | PASS | checksum row formal/certificates/corridors/COR-POS-02A.certificate.json verifies |
| MANIFEST-SUM-0422 | manifest | PASS | checksum row formal/certificates/corridors/COR-POS-02B.certificate.json verifies |
| MANIFEST-SUM-0423 | manifest | PASS | checksum row formal/certificates/corridors/controls/COMP-C01.certificate.json verifies |
| MANIFEST-SUM-0424 | manifest | PASS | checksum row formal/certificates/corridors/controls/COMP-C02.certificate.json verifies |
| MANIFEST-SUM-0425 | manifest | PASS | checksum row formal/certificates/corridors/controls/COMP-C03.certificate.json verifies |
| MANIFEST-SUM-0426 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C01.certificate.json verifies |
| MANIFEST-SUM-0427 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C02.certificate.json verifies |
| MANIFEST-SUM-0428 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C03.certificate.json verifies |
| MANIFEST-SUM-0429 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C04.certificate.json verifies |
| MANIFEST-SUM-0430 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C05.certificate.json verifies |
| MANIFEST-SUM-0431 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C06.certificate.json verifies |
| MANIFEST-SUM-0432 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C07.certificate.json verifies |
| MANIFEST-SUM-0433 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C08.certificate.json verifies |
| MANIFEST-SUM-0434 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C09.certificate.json verifies |
| MANIFEST-SUM-0435 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C10.certificate.json verifies |
| MANIFEST-SUM-0436 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C11.certificate.json verifies |
| MANIFEST-SUM-0437 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C12.certificate.json verifies |
| MANIFEST-SUM-0438 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C13.certificate.json verifies |
| MANIFEST-SUM-0439 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C14.certificate.json verifies |
| MANIFEST-SUM-0440 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C15.certificate.json verifies |
| MANIFEST-SUM-0441 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C16.certificate.json verifies |
| MANIFEST-SUM-0442 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C17.certificate.json verifies |
| MANIFEST-SUM-0443 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C18.certificate.json verifies |
| MANIFEST-SUM-0444 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C19.certificate.json verifies |
| MANIFEST-SUM-0445 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C20.certificate.json verifies |
| MANIFEST-SUM-0446 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C21.certificate.json verifies |
| MANIFEST-SUM-0447 | manifest | PASS | checksum row formal/certificates/corridors/controls/COR-C22.certificate.json verifies |
| MANIFEST-SUM-0448 | manifest | PASS | checksum row formal/certificates/countermodels/CM-01.certificate.json verifies |
| MANIFEST-SUM-0449 | manifest | PASS | checksum row formal/certificates/countermodels/CM-02.certificate.json verifies |
| MANIFEST-SUM-0450 | manifest | PASS | checksum row formal/certificates/countermodels/CM-03.certificate.json verifies |
| MANIFEST-SUM-0451 | manifest | PASS | checksum row formal/certificates/countermodels/CM-04.certificate.json verifies |
| MANIFEST-SUM-0452 | manifest | PASS | checksum row formal/certificates/countermodels/CM-05.certificate.json verifies |
| MANIFEST-SUM-0453 | manifest | PASS | checksum row formal/certificates/countermodels/CM-06.certificate.json verifies |
| MANIFEST-SUM-0454 | manifest | PASS | checksum row formal/certificates/countermodels/CM-07.certificate.json verifies |
| MANIFEST-SUM-0455 | manifest | PASS | checksum row formal/certificates/countermodels/CM-08.certificate.json verifies |
| MANIFEST-SUM-0456 | manifest | PASS | checksum row formal/certificates/countermodels/CM-09.certificate.json verifies |
| MANIFEST-SUM-0457 | manifest | PASS | checksum row formal/certificates/countermodels/CM-10.certificate.json verifies |
| MANIFEST-SUM-0458 | manifest | PASS | checksum row formal/certificates/countermodels/CM-11.certificate.json verifies |
| MANIFEST-SUM-0459 | manifest | PASS | checksum row formal/certificates/countermodels/CM-12.certificate.json verifies |
| MANIFEST-SUM-0460 | manifest | PASS | checksum row formal/certificates/countermodels/CM-13.certificate.json verifies |
| MANIFEST-SUM-0461 | manifest | PASS | checksum row formal/certificates/countermodels/CM-14.certificate.json verifies |
| MANIFEST-SUM-0462 | manifest | PASS | checksum row formal/certificates/countermodels/CM-15.certificate.json verifies |
| MANIFEST-SUM-0463 | manifest | PASS | checksum row formal/certificates/countermodels/INDEX.md verifies |
| MANIFEST-SUM-0464 | manifest | PASS | checksum row formal/certificates/direct_successor/DS-PATH-POS-01.certificate.json verifies |
| MANIFEST-SUM-0465 | manifest | PASS | checksum row formal/certificates/direct_successor/DS-POS-01.certificate.json verifies |
| MANIFEST-SUM-0466 | manifest | PASS | checksum row formal/certificates/direct_successor/DS-POS-02A.certificate.json verifies |
| MANIFEST-SUM-0467 | manifest | PASS | checksum row formal/certificates/direct_successor/DS-POS-02B.certificate.json verifies |
| MANIFEST-SUM-0468 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C01.certificate.json verifies |
| MANIFEST-SUM-0469 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C02.certificate.json verifies |
| MANIFEST-SUM-0470 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C03.certificate.json verifies |
| MANIFEST-SUM-0471 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C04.certificate.json verifies |
| MANIFEST-SUM-0472 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C05.certificate.json verifies |
| MANIFEST-SUM-0473 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C06.certificate.json verifies |
| MANIFEST-SUM-0474 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C07.certificate.json verifies |
| MANIFEST-SUM-0475 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C08.certificate.json verifies |
| MANIFEST-SUM-0476 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C09.certificate.json verifies |
| MANIFEST-SUM-0477 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C10.certificate.json verifies |
| MANIFEST-SUM-0478 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C11.certificate.json verifies |
| MANIFEST-SUM-0479 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C12.certificate.json verifies |
| MANIFEST-SUM-0480 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C13.certificate.json verifies |
| MANIFEST-SUM-0481 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C14.certificate.json verifies |
| MANIFEST-SUM-0482 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C15.certificate.json verifies |
| MANIFEST-SUM-0483 | manifest | PASS | checksum row formal/certificates/direct_successor/controls/DS-C16.certificate.json verifies |
| MANIFEST-SUM-0484 | manifest | PASS | checksum row formal/certificates/fiach/FIACH-POS-01.certificate.json verifies |
| MANIFEST-SUM-0485 | manifest | PASS | checksum row formal/certificates/fiach/controls/FIACH-C01.certificate.json verifies |
| MANIFEST-SUM-0486 | manifest | PASS | checksum row formal/certificates/fiach/controls/FIACH-C02.certificate.json verifies |
| MANIFEST-SUM-0487 | manifest | PASS | checksum row formal/certificates/fiach/controls/FIACH-C03.certificate.json verifies |
| MANIFEST-SUM-0488 | manifest | PASS | checksum row formal/certificates/fiach/controls/FIACH-C04.certificate.json verifies |
| MANIFEST-SUM-0489 | manifest | PASS | checksum row formal/certificates/fiach/controls/FIACH-C05.certificate.json verifies |
| MANIFEST-SUM-0490 | manifest | PASS | checksum row formal/certificates/fiach/controls/FIACH-C06.certificate.json verifies |
| MANIFEST-SUM-0491 | manifest | PASS | checksum row formal/certificates/memory/BOUNDED_MEMORY_OR_FLATNESS_EXHAUSTION.json verifies |
| MANIFEST-SUM-0492 | manifest | PASS | checksum row formal/certificates/memory/MEM-FLAT-01.certificate.json verifies |
| MANIFEST-SUM-0493 | manifest | PASS | checksum row formal/certificates/memory/MEM-POS-01.certificate.json verifies |
| MANIFEST-SUM-0494 | manifest | PASS | checksum row formal/certificates/packages/BOUNDED_GLUING_EXHAUSTION.json verifies |
| MANIFEST-SUM-0495 | manifest | PASS | checksum row formal/certificates/packages/PKG-POS-01-TARGET.certificate.json verifies |
| MANIFEST-SUM-0496 | manifest | PASS | checksum row formal/certificates/packages/PKG-POS-02-SOURCE.certificate.json verifies |
| MANIFEST-SUM-0497 | manifest | PASS | checksum row formal/certificates/packages/PKG-POS-03-FIACH-SOURCE.certificate.json verifies |
| MANIFEST-SUM-0498 | manifest | PASS | checksum row formal/certificates/packages/PKG-POS-04-FIACH-TARGET.certificate.json verifies |
| MANIFEST-SUM-0499 | manifest | PASS | checksum row formal/certificates/packages/STG-POS-01.certificate.json verifies |
| MANIFEST-SUM-0500 | manifest | PASS | checksum row formal/certificates/packages/STG-POS-02-FIACH.certificate.json verifies |
| MANIFEST-SUM-0501 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-01.certificate.json verifies |
| MANIFEST-SUM-0502 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-02.certificate.json verifies |
| MANIFEST-SUM-0503 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-03.certificate.json verifies |
| MANIFEST-SUM-0504 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-04.certificate.json verifies |
| MANIFEST-SUM-0505 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-05.certificate.json verifies |
| MANIFEST-SUM-0506 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-06.certificate.json verifies |
| MANIFEST-SUM-0507 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-07.certificate.json verifies |
| MANIFEST-SUM-0508 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-08.certificate.json verifies |
| MANIFEST-SUM-0509 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-09.certificate.json verifies |
| MANIFEST-SUM-0510 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-10.certificate.json verifies |
| MANIFEST-SUM-0511 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-11.certificate.json verifies |
| MANIFEST-SUM-0512 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-12.certificate.json verifies |
| MANIFEST-SUM-0513 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-13.certificate.json verifies |
| MANIFEST-SUM-0514 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-14.certificate.json verifies |
| MANIFEST-SUM-0515 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-15.certificate.json verifies |
| MANIFEST-SUM-0516 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-16.certificate.json verifies |
| MANIFEST-SUM-0517 | manifest | PASS | checksum row formal/certificates/packages/controls/PC-17.certificate.json verifies |
| MANIFEST-SUM-0518 | manifest | PASS | checksum row formal/certificates/packages/controls/SC-01.certificate.json verifies |
| MANIFEST-SUM-0519 | manifest | PASS | checksum row formal/certificates/routes/BOUNDED_CONFLUENCE_SHAPE_SEARCH.json verifies |
| MANIFEST-SUM-0520 | manifest | PASS | checksum row formal/certificates/routes/BOUNDED_GLOBAL_NOW_OBSTRUCTION_SEARCH.json verifies |
| MANIFEST-SUM-0521 | manifest | PASS | checksum row formal/certificates/routes/ROUTE-NEG-01.certificate.json verifies |
| MANIFEST-SUM-0522 | manifest | PASS | checksum row formal/certificates/routes/ROUTE-POS-01.certificate.json verifies |
| MANIFEST-SUM-0523 | manifest | PASS | checksum row formal/certificates/search/AUTONOMY_FINITE_HORIZON_EXHAUSTION.json verifies |
| MANIFEST-SUM-0524 | manifest | PASS | checksum row formal/certificates/search/AUTONOMY_INVARIANT_EXHAUSTION.json verifies |
| MANIFEST-SUM-0525 | manifest | PASS | checksum row formal/certificates/search/CORRIDOR_COMPOSITION_SEARCH.json verifies |
| MANIFEST-SUM-0526 | manifest | PASS | checksum row formal/certificates/search/CORRIDOR_SUPPORT_SEARCH.json verifies |
| MANIFEST-SUM-0527 | manifest | PASS | checksum row formal/certificates/search/DIRECT_PATH_COMPOSITION_SEARCH.json verifies |
| MANIFEST-SUM-0528 | manifest | PASS | checksum row formal/certificates/search/DIRECT_SUCCESSOR_SEARCH.json verifies |
| MANIFEST-SUM-0529 | manifest | PASS | checksum row formal/certificates/search/FIACH_LANE_TRUTH_TABLE.json verifies |
| MANIFEST-SUM-0530 | manifest | PASS | checksum row formal/certificates/search/NONREDUNDANCY_TRUTH_TABLE_SEARCH.json verifies |
| MANIFEST-SUM-0531 | manifest | PASS | checksum row formal/certificates/transport/BOUNDED_TRANSPORT_SHAPE_SEARCH.json verifies |
| MANIFEST-SUM-0532 | manifest | PASS | checksum row formal/certificates/transport/TR-POS-01.certificate.json verifies |
| MANIFEST-SUM-0533 | manifest | PASS | checksum row formal/certificates/transport/TR-POS-02-FLAT.certificate.json verifies |
| MANIFEST-SUM-0534 | manifest | PASS | checksum row formal/certificates/transport/controls/ARROW-C01.certificate.json verifies |
| MANIFEST-SUM-0535 | manifest | PASS | checksum row formal/certificates/transport/controls/ARROW-C02.certificate.json verifies |
| MANIFEST-SUM-0536 | manifest | PASS | checksum row formal/certificates/transport/controls/ARROW-C03.certificate.json verifies |
| MANIFEST-SUM-0537 | manifest | PASS | checksum row formal/certificates/transport/controls/ARROW-C04.certificate.json verifies |
| MANIFEST-SUM-0538 | manifest | PASS | checksum row formal/certificates/transport/controls/MEM-C01.certificate.json verifies |
| MANIFEST-SUM-0539 | manifest | PASS | checksum row formal/certificates/transport/controls/ROUTE-C01.certificate.json verifies |
| MANIFEST-SUM-0540 | manifest | PASS | checksum row formal/certificates/transport/controls/ROUTE-C02.certificate.json verifies |
| MANIFEST-SUM-0541 | manifest | PASS | checksum row formal/certificates/transport/controls/ROUTE-C03.certificate.json verifies |
| MANIFEST-SUM-0542 | manifest | PASS | checksum row formal/certificates/transport/controls/ROUTE-C04.certificate.json verifies |
| MANIFEST-SUM-0543 | manifest | PASS | checksum row formal/certificates/transport/controls/ROUTE-C05.certificate.json verifies |
| MANIFEST-SUM-0544 | manifest | PASS | checksum row formal/certificates/transport/controls/ROUTE-C06.certificate.json verifies |
| MANIFEST-SUM-0545 | manifest | PASS | checksum row formal/certificates/transport/controls/ROUTE-C07.certificate.json verifies |
| MANIFEST-SUM-0546 | manifest | PASS | checksum row formal/certificates/transport/controls/ROUTE-C08.certificate.json verifies |
| MANIFEST-SUM-0547 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C01.certificate.json verifies |
| MANIFEST-SUM-0548 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C02.certificate.json verifies |
| MANIFEST-SUM-0549 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C03.certificate.json verifies |
| MANIFEST-SUM-0550 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C04.certificate.json verifies |
| MANIFEST-SUM-0551 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C05.certificate.json verifies |
| MANIFEST-SUM-0552 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C06.certificate.json verifies |
| MANIFEST-SUM-0553 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C07.certificate.json verifies |
| MANIFEST-SUM-0554 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C08.certificate.json verifies |
| MANIFEST-SUM-0555 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C09.certificate.json verifies |
| MANIFEST-SUM-0556 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C10.certificate.json verifies |
| MANIFEST-SUM-0557 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C11.certificate.json verifies |
| MANIFEST-SUM-0558 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C12.certificate.json verifies |
| MANIFEST-SUM-0559 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C13.certificate.json verifies |
| MANIFEST-SUM-0560 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C14.certificate.json verifies |
| MANIFEST-SUM-0561 | manifest | PASS | checksum row formal/certificates/transport/controls/TR-C15.certificate.json verifies |
| MANIFEST-SUM-0562 | manifest | PASS | checksum row inputs/INPUTS.sha256 verifies |
| MANIFEST-SUM-0563 | manifest | PASS | checksum row inputs/INPUT_PROVENANCE.md verifies |
| MANIFEST-SUM-0564 | manifest | PASS | checksum row inputs/SOURCE_INPUTS.md verifies |
| MANIFEST-SUM-0565 | manifest | PASS | checksum row inputs/normative/PAPER_TRIAGE.md verifies |
| MANIFEST-SUM-0566 | manifest | PASS | checksum row inputs/normative/PREPARATORY_EXPLORATION_PLAN.md verifies |
| MANIFEST-SUM-0567 | manifest | PASS | checksum row inputs/normative/cst-tt-00/EXECUTION_PLAN.md verifies |
| MANIFEST-SUM-0568 | manifest | PASS | checksum row inputs/normative/cst-tt-00/FIACH_BASELINE_SPECIFICATION.md verifies |
| MANIFEST-SUM-0569 | manifest | PASS | checksum row inputs/normative/cst-tt-00/IAPS_BASELINE_SPECIFICATION.md verifies |
| MANIFEST-SUM-0570 | manifest | PASS | checksum row inputs/normative/cst-tt-00/IMPORTED_SHA256SUMS.txt verifies |
| MANIFEST-SUM-0571 | manifest | PASS | checksum row inputs/normative/cst-tt-00/TEMPORAL_AUDIT_ORIGINAL_SHA256SUMS.txt verifies |
| MANIFEST-SUM-0572 | manifest | PASS | checksum row inputs/normative/cst-tt-00/TEMPORAL_AUDIT_README.md verifies |
| MANIFEST-SUM-0573 | manifest | PASS | checksum row inputs/normative/cst-tt-00/TEMPORAL_SOURCE_MAP.md verifies |
| MANIFEST-SUM-0574 | manifest | PASS | checksum row inputs/normative/cst-tt-00/TEMPORAL_TRANSCENDENCE_AUDIT.md verifies |
| MANIFEST-SUM-0575 | manifest | PASS | checksum row inputs/reference_surfaces/A1_A2_provenance_excerpt.md verifies |
| MANIFEST-SUM-0576 | manifest | PASS | checksum row inputs/reference_surfaces/F19_Object_Persistence_excerpt.tex verifies |
| MANIFEST-SUM-0577 | manifest | PASS | checksum row inputs/reference_surfaces/notation_and_terminology.md verifies |
| MANIFEST-SUM-0578 | manifest | PASS | checksum row inputs/reference_surfaces/open_issues.md verifies |
| MANIFEST-SUM-0579 | manifest | PASS | checksum row inputs/reference_surfaces/sec_02_claim_types.tex verifies |
| MANIFEST-SUM-0580 | manifest | PASS | checksum row inputs/reference_surfaces/sec_03_closure_architecture.tex verifies |
| MANIFEST-SUM-0581 | manifest | PASS | checksum row inputs/reference_surfaces/sec_05_consequence_clusters.tex verifies |
| MANIFEST-SUM-0582 | manifest | PASS | checksum row inputs/reference_surfaces/sec_06_conditional_realization.tex verifies |
| MANIFEST-SUM-0583 | manifest | PASS | checksum row inputs/reference_surfaces/sec_07_empirical_status.tex verifies |
| MANIFEST-SUM-0584 | manifest | PASS | checksum row inputs/reference_surfaces/sec_09_limitations_conclusion.tex verifies |
| MANIFEST-SUM-0585 | manifest | PASS | checksum row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_An_Audited_Closure_Architecture_for_Consciousness_Exact_Finite_Models_Structural_Theorems_and_Conditional_Realization.tex verifies |
| MANIFEST-SUM-0586 | manifest | PASS | checksum row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Glass_Is_an_Unclosed_Layer_Kovacs_Memory_as_Predictive_Quotient_Residue.tex verifies |
| MANIFEST-SUM-0587 | manifest | PASS | checksum row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex verifies |
| MANIFEST-SUM-0588 | manifest | PASS | checksum row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex verifies |
| MANIFEST-SUM-0589 | manifest | PASS | checksum row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_VI_A_Catalog_of_Dynamical_Structural_Laws.tex verifies |
| MANIFEST-SUM-0590 | manifest | PASS | checksum row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Protocol_Trap_Holonomy_Without_Entropy_Production.tex verifies |
| MANIFEST-SUM-0591 | manifest | PASS | checksum row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Flatten_a_Stone_with_Six_Birds_Critical_Pairs_Holonomy_and_Confluence_in_Rewriting_Systems.tex verifies |
| MANIFEST-SUM-0592 | manifest | PASS | checksum row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Lay_a_Stone_with_Six_Birds_Finite_State_Semantics_for_Packaging_Directionality_and_Coarse_Graining.tex verifies |
| MANIFEST-SUM-0593 | manifest | PASS | checksum row inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex verifies |
| MANIFEST-SUM-0594 | manifest | PASS | checksum row inputs/source_archives/CST_temporal_transcendence_audit.zip verifies |
| MANIFEST-SUM-0595 | manifest | PASS | checksum row inputs/source_archives/six-birds-consciousness_v41.zip verifies |
| MANIFEST-SUM-0596 | manifest | PASS | checksum row inputs/source_archives/six_birds_papers_tex.zip verifies |
| MANIFEST-SUM-0597 | manifest | PASS | checksum row lakefile.toml verifies |
| MANIFEST-SUM-0598 | manifest | PASS | checksum row lean-toolchain verifies |
| MANIFEST-SUM-0599 | manifest | PASS | checksum row ledgers/.gitkeep verifies |
| MANIFEST-SUM-0600 | manifest | PASS | checksum row ledgers/DECISION_LOG.md verifies |
| MANIFEST-SUM-0601 | manifest | PASS | checksum row ledgers/REJECTED_DEFAULTS.md verifies |
| MANIFEST-SUM-0602 | manifest | PASS | checksum row ledgers/UNRESOLVED_QUESTIONS.md verifies |
| MANIFEST-SUM-0603 | manifest | PASS | checksum row ledgers/anti_conflation_checklist.csv verifies |
| MANIFEST-SUM-0604 | manifest | PASS | checksum row ledgers/asset_provenance.csv verifies |
| MANIFEST-SUM-0605 | manifest | PASS | checksum row ledgers/assumption_exposure.csv verifies |
| MANIFEST-SUM-0606 | manifest | PASS | checksum row ledgers/assumption_register.csv verifies |
| MANIFEST-SUM-0607 | manifest | PASS | checksum row ledgers/assumption_register.yml verifies |
| MANIFEST-SUM-0608 | manifest | PASS | checksum row ledgers/candidate_anti_conflation_audit.csv verifies |
| MANIFEST-SUM-0609 | manifest | PASS | checksum row ledgers/candidate_asset_crosswalk.csv verifies |
| MANIFEST-SUM-0610 | manifest | PASS | checksum row ledgers/candidate_assumption_matrix.csv verifies |
| MANIFEST-SUM-0611 | manifest | PASS | checksum row ledgers/candidate_discriminator_crosswalk.csv verifies |
| MANIFEST-SUM-0612 | manifest | PASS | checksum row ledgers/candidate_divergence_matrix.csv verifies |
| MANIFEST-SUM-0613 | manifest | PASS | checksum row ledgers/candidate_feature_matrix.csv verifies |
| MANIFEST-SUM-0614 | manifest | PASS | checksum row ledgers/candidate_hard_case_stress.csv verifies |
| MANIFEST-SUM-0615 | manifest | PASS | checksum row ledgers/candidate_internal_lens_audit.csv verifies |
| MANIFEST-SUM-0616 | manifest | PASS | checksum row ledgers/candidate_question_responses.csv verifies |
| MANIFEST-SUM-0617 | manifest | PASS | checksum row ledgers/candidate_scenario_verdicts.csv verifies |
| MANIFEST-SUM-0618 | manifest | PASS | checksum row ledgers/candidate_verdicts_by_scenario.csv verifies |
| MANIFEST-SUM-0619 | manifest | PASS | checksum row ledgers/claim_register_template.csv verifies |
| MANIFEST-SUM-0620 | manifest | PASS | checksum row ledgers/claim_tag_registry.yml verifies |
| MANIFEST-SUM-0621 | manifest | PASS | checksum row ledgers/corpus_duplicate_map.csv verifies |
| MANIFEST-SUM-0622 | manifest | PASS | checksum row ledgers/decision_log.csv verifies |
| MANIFEST-SUM-0623 | manifest | PASS | checksum row ledgers/dependency_read_wave_log.csv verifies |
| MANIFEST-SUM-0624 | manifest | PASS | checksum row ledgers/exploration_question_bank.yml verifies |
| MANIFEST-SUM-0625 | manifest | PASS | checksum row ledgers/external_literature_crosswalk.csv verifies |
| MANIFEST-SUM-0626 | manifest | PASS | checksum row ledgers/family_assumption_ladder.csv verifies |
| MANIFEST-SUM-0627 | manifest | PASS | checksum row ledgers/family_feasibility_registry.csv verifies |
| MANIFEST-SUM-0628 | manifest | PASS | checksum row ledgers/formalization_surface.csv verifies |
| MANIFEST-SUM-0629 | manifest | PASS | checksum row ledgers/gap_to_asset_matrix.csv verifies |
| MANIFEST-SUM-0630 | manifest | PASS | checksum row ledgers/glossary_terms.csv verifies |
| MANIFEST-SUM-0631 | manifest | PASS | checksum row ledgers/landing_bundle_registry.csv verifies |
| MANIFEST-SUM-0632 | manifest | PASS | checksum row ledgers/lexical_dependency_index.csv verifies |
| MANIFEST-SUM-0633 | manifest | PASS | checksum row ledgers/map_type_ledger.csv verifies |
| MANIFEST-SUM-0634 | manifest | PASS | checksum row ledgers/model_candidate_discrimination.csv verifies |
| MANIFEST-SUM-0635 | manifest | PASS | checksum row ledgers/model_registry.csv verifies |
| MANIFEST-SUM-0636 | manifest | PASS | checksum row ledgers/model_theorem_program_crosswalk.csv verifies |
| MANIFEST-SUM-0637 | manifest | PASS | checksum row ledgers/new_primitive_register.csv verifies |
| MANIFEST-SUM-0638 | manifest | PASS | checksum row ledgers/no_go_refinement_map.csv verifies |
| MANIFEST-SUM-0639 | manifest | PASS | checksum row ledgers/no_go_register.csv verifies |
| MANIFEST-SUM-0640 | manifest | PASS | checksum row ledgers/paper_coverage_audit.csv verifies |
| MANIFEST-SUM-0641 | manifest | PASS | checksum row ledgers/rejection_and_salvage_log.csv verifies |
| MANIFEST-SUM-0642 | manifest | PASS | checksum row ledgers/scenario_asset_crosswalk.csv verifies |
| MANIFEST-SUM-0643 | manifest | PASS | checksum row ledgers/scenario_discriminator_matrix.csv verifies |
| MANIFEST-SUM-0644 | manifest | PASS | checksum row ledgers/scenario_question_crosswalk.csv verifies |
| MANIFEST-SUM-0645 | manifest | PASS | checksum row ledgers/scenario_verdict_template.csv verifies |
| MANIFEST-SUM-0646 | manifest | PASS | checksum row ledgers/source_label_index.csv verifies |
| MANIFEST-SUM-0647 | manifest | PASS | checksum row ledgers/statement_provenance.csv verifies |
| MANIFEST-SUM-0648 | manifest | PASS | checksum row ledgers/support_and_carrier_assumptions.csv verifies |
| MANIFEST-SUM-0649 | manifest | PASS | checksum row ledgers/survivor_composition_matrix.csv verifies |
| MANIFEST-SUM-0650 | manifest | PASS | checksum row ledgers/survivor_family_registry.csv verifies |
| MANIFEST-SUM-0651 | manifest | PASS | checksum row ledgers/term_dependency_and_circularity_audit.csv verifies |
| MANIFEST-SUM-0652 | manifest | PASS | checksum row ledgers/theorem_dependency_and_risk.csv verifies |
| MANIFEST-SUM-0653 | manifest | PASS | checksum row ledgers/toy_program_registry.csv verifies |
| MANIFEST-SUM-0654 | manifest | PASS | checksum row ledgers/version_and_exclusion_log.md verifies |
| MANIFEST-SUM-0655 | manifest | PASS | checksum row manifests/.gitkeep verifies |
| MANIFEST-SUM-0656 | manifest | PASS | checksum row manifests/COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0657 | manifest | PASS | checksum row manifests/CST-EXP-00_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0658 | manifest | PASS | checksum row manifests/CST-EXP-00_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0659 | manifest | PASS | checksum row manifests/CST-EXP-01_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0660 | manifest | PASS | checksum row manifests/CST-EXP-01_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0661 | manifest | PASS | checksum row manifests/CST-EXP-01_VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0662 | manifest | PASS | checksum row manifests/CST-EXP-02_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0663 | manifest | PASS | checksum row manifests/CST-EXP-02_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0664 | manifest | PASS | checksum row manifests/CST-EXP-02_VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0665 | manifest | PASS | checksum row manifests/CST-EXP-03_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0666 | manifest | PASS | checksum row manifests/CST-EXP-03_MANIFEST.json verifies |
| MANIFEST-SUM-0667 | manifest | PASS | checksum row manifests/CST-EXP-03_REBUILD_VERIFICATION.json verifies |
| MANIFEST-SUM-0668 | manifest | PASS | checksum row manifests/CST-EXP-03_REBUILD_VERIFICATION.md verifies |
| MANIFEST-SUM-0669 | manifest | PASS | checksum row manifests/CST-EXP-04_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0670 | manifest | PASS | checksum row manifests/CST-EXP-04_MANIFEST.json verifies |
| MANIFEST-SUM-0671 | manifest | PASS | checksum row manifests/CST-EXP-04_PREVALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0672 | manifest | PASS | checksum row manifests/CST-EXP-04_PREVALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0673 | manifest | PASS | checksum row manifests/CST-EXP-04_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0674 | manifest | PASS | checksum row manifests/CST-EXP-04_VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0675 | manifest | PASS | checksum row manifests/CST-EXP-05_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0676 | manifest | PASS | checksum row manifests/CST-EXP-05_MANIFEST.json verifies |
| MANIFEST-SUM-0677 | manifest | PASS | checksum row manifests/CST-EXP-06_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0678 | manifest | PASS | checksum row manifests/CST-EXP-06_MANIFEST.json verifies |
| MANIFEST-SUM-0679 | manifest | PASS | checksum row manifests/CST-EXP-06_PREVALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0680 | manifest | PASS | checksum row manifests/CST-EXP-06_PREVALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0681 | manifest | PASS | checksum row manifests/CST-EXP-06_SHA256SUMS verifies |
| MANIFEST-SUM-0682 | manifest | PASS | checksum row manifests/CST-EXP-06_VALIDATION_REPORT_FINAL.md verifies |
| MANIFEST-SUM-0683 | manifest | PASS | checksum row manifests/CST-EXP-06_VALIDATION_RESULTS_FINAL.json verifies |
| MANIFEST-SUM-0684 | manifest | PASS | checksum row manifests/CST-TT-00_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0685 | manifest | PASS | checksum row manifests/CST-TT-00_MANIFEST.json verifies |
| MANIFEST-SUM-0686 | manifest | PASS | checksum row manifests/CST-TT-00_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-SUM-0687 | manifest | PASS | checksum row manifests/CST-TT-00_PHASE_SUMMARY.json verifies |
| MANIFEST-SUM-0688 | manifest | PASS | checksum row manifests/CST-TT-00_REBUILD_VERIFICATION.json verifies |
| MANIFEST-SUM-0689 | manifest | PASS | checksum row manifests/CST-TT-00_REBUILD_VERIFICATION.md verifies |
| MANIFEST-SUM-0690 | manifest | PASS | checksum row manifests/CST-TT-00_SHA256SUMS verifies |
| MANIFEST-SUM-0691 | manifest | PASS | checksum row manifests/CST-TT-00_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-SUM-0692 | manifest | PASS | checksum row manifests/CST-TT-00_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0693 | manifest | PASS | checksum row manifests/CST-TT-00_VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0694 | manifest | PASS | checksum row manifests/CST-TT-01_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0695 | manifest | PASS | checksum row manifests/CST-TT-01_MANIFEST.json verifies |
| MANIFEST-SUM-0696 | manifest | PASS | checksum row manifests/CST-TT-01_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-SUM-0697 | manifest | PASS | checksum row manifests/CST-TT-01_PHASE_SUMMARY.json verifies |
| MANIFEST-SUM-0698 | manifest | PASS | checksum row manifests/CST-TT-01_REBUILD_VERIFICATION.json verifies |
| MANIFEST-SUM-0699 | manifest | PASS | checksum row manifests/CST-TT-01_REBUILD_VERIFICATION.md verifies |
| MANIFEST-SUM-0700 | manifest | PASS | checksum row manifests/CST-TT-01_SEARCH_SUMMARY.json verifies |
| MANIFEST-SUM-0701 | manifest | PASS | checksum row manifests/CST-TT-01_SHA256SUMS verifies |
| MANIFEST-SUM-0702 | manifest | PASS | checksum row manifests/CST-TT-01_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-SUM-0703 | manifest | PASS | checksum row manifests/CST-TT-01_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0704 | manifest | PASS | checksum row manifests/CST-TT-01_VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0705 | manifest | PASS | checksum row manifests/CST-TT-02_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0706 | manifest | PASS | checksum row manifests/CST-TT-02_MANIFEST.json verifies |
| MANIFEST-SUM-0707 | manifest | PASS | checksum row manifests/CST-TT-02_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-SUM-0708 | manifest | PASS | checksum row manifests/CST-TT-02_PHASE_SUMMARY.json verifies |
| MANIFEST-SUM-0709 | manifest | PASS | checksum row manifests/CST-TT-02_REBUILD_VERIFICATION.json verifies |
| MANIFEST-SUM-0710 | manifest | PASS | checksum row manifests/CST-TT-02_REBUILD_VERIFICATION.md verifies |
| MANIFEST-SUM-0711 | manifest | PASS | checksum row manifests/CST-TT-02_SHA256SUMS verifies |
| MANIFEST-SUM-0712 | manifest | PASS | checksum row manifests/CST-TT-02_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-SUM-0713 | manifest | PASS | checksum row manifests/CST-TT-02_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0714 | manifest | PASS | checksum row manifests/CST-TT-02_VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0715 | manifest | PASS | checksum row manifests/CST-TT-03_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0716 | manifest | PASS | checksum row manifests/CST-TT-03_MANIFEST.json verifies |
| MANIFEST-SUM-0717 | manifest | PASS | checksum row manifests/CST-TT-03_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-SUM-0718 | manifest | PASS | checksum row manifests/CST-TT-03_PHASE_SUMMARY.json verifies |
| MANIFEST-SUM-0719 | manifest | PASS | checksum row manifests/CST-TT-03_REBUILD_VERIFICATION.json verifies |
| MANIFEST-SUM-0720 | manifest | PASS | checksum row manifests/CST-TT-03_REBUILD_VERIFICATION.md verifies |
| MANIFEST-SUM-0721 | manifest | PASS | checksum row manifests/CST-TT-03_SHA256SUMS verifies |
| MANIFEST-SUM-0722 | manifest | PASS | checksum row manifests/CST-TT-03_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-SUM-0723 | manifest | PASS | checksum row manifests/CST-TT-03_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0724 | manifest | PASS | checksum row manifests/CST-TT-03_VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0725 | manifest | PASS | checksum row manifests/CST-TT-04_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0726 | manifest | PASS | checksum row manifests/CST-TT-04_MANIFEST.json verifies |
| MANIFEST-SUM-0727 | manifest | PASS | checksum row manifests/CST-TT-04_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-SUM-0728 | manifest | PASS | checksum row manifests/CST-TT-04_PHASE_SUMMARY.json verifies |
| MANIFEST-SUM-0729 | manifest | PASS | checksum row manifests/CST-TT-04_REBUILD_VERIFICATION.json verifies |
| MANIFEST-SUM-0730 | manifest | PASS | checksum row manifests/CST-TT-04_REBUILD_VERIFICATION.md verifies |
| MANIFEST-SUM-0731 | manifest | PASS | checksum row manifests/CST-TT-04_SHA256SUMS verifies |
| MANIFEST-SUM-0732 | manifest | PASS | checksum row manifests/CST-TT-04_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-SUM-0733 | manifest | PASS | checksum row manifests/CST-TT-04_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0734 | manifest | PASS | checksum row manifests/CST-TT-04_VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0735 | manifest | PASS | checksum row manifests/CST-TT-05_COMPLETION_REPORT.md verifies |
| MANIFEST-SUM-0736 | manifest | PASS | checksum row manifests/CST-TT-05_MANIFEST.json verifies |
| MANIFEST-SUM-0737 | manifest | PASS | checksum row manifests/CST-TT-05_MODEL_CERTIFICATE_DELTA.csv verifies |
| MANIFEST-SUM-0738 | manifest | PASS | checksum row manifests/CST-TT-05_PHASE_SUMMARY.json verifies |
| MANIFEST-SUM-0739 | manifest | PASS | checksum row manifests/CST-TT-05_REBUILD_VERIFICATION.json verifies |
| MANIFEST-SUM-0740 | manifest | PASS | checksum row manifests/CST-TT-05_REBUILD_VERIFICATION.md verifies |
| MANIFEST-SUM-0741 | manifest | PASS | checksum row manifests/CST-TT-05_THEOREM_STATUS_DELTA.csv verifies |
| MANIFEST-SUM-0742 | manifest | PASS | checksum row manifests/CST-TT-05_VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0743 | manifest | PASS | checksum row manifests/CST-TT-05_VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0744 | manifest | PASS | checksum row manifests/EXP02_ASSET_SUMMARY.json verifies |
| MANIFEST-SUM-0745 | manifest | PASS | checksum row manifests/EXP03_ASSET_SUMMARY.json verifies |
| MANIFEST-SUM-0746 | manifest | PASS | checksum row manifests/EXP04_ASSET_SUMMARY.json verifies |
| MANIFEST-SUM-0747 | manifest | PASS | checksum row manifests/EXP05_ASSET_SUMMARY.json verifies |
| MANIFEST-SUM-0748 | manifest | PASS | checksum row manifests/EXP06_ASSET_SUMMARY.json verifies |
| MANIFEST-SUM-0749 | manifest | PASS | checksum row manifests/MANIFEST.json verifies |
| MANIFEST-SUM-0750 | manifest | PASS | checksum row manifests/PHASE_SUMMARY.json verifies |
| MANIFEST-SUM-0751 | manifest | PASS | checksum row manifests/REBUILD_VERIFICATION.json verifies |
| MANIFEST-SUM-0752 | manifest | PASS | checksum row manifests/REBUILD_VERIFICATION.md verifies |
| MANIFEST-SUM-0753 | manifest | PASS | checksum row manifests/RESTORE_AND_VERIFY.md verifies |
| MANIFEST-SUM-0754 | manifest | PASS | checksum row manifests/SOURCE_SHA256SUMS verifies |
| MANIFEST-SUM-0755 | manifest | PASS | checksum row manifests/TT00_ASSET_SUMMARY.json verifies |
| MANIFEST-SUM-0756 | manifest | PASS | checksum row manifests/VALIDATION_REPORT.md verifies |
| MANIFEST-SUM-0757 | manifest | PASS | checksum row manifests/VALIDATION_RESULTS.json verifies |
| MANIFEST-SUM-0758 | manifest | PASS | checksum row models/arrow/ARROW-POS-01.model.json verifies |
| MANIFEST-SUM-0759 | manifest | PASS | checksum row models/autonomy/AUT-POS-01.model.json verifies |
| MANIFEST-SUM-0760 | manifest | PASS | checksum row models/autonomy/controls/AUT-C01.model.json verifies |
| MANIFEST-SUM-0761 | manifest | PASS | checksum row models/autonomy/controls/AUT-C02.model.json verifies |
| MANIFEST-SUM-0762 | manifest | PASS | checksum row models/autonomy/controls/AUT-C03.model.json verifies |
| MANIFEST-SUM-0763 | manifest | PASS | checksum row models/autonomy/controls/AUT-C04.model.json verifies |
| MANIFEST-SUM-0764 | manifest | PASS | checksum row models/autonomy/controls/AUT-C05.model.json verifies |
| MANIFEST-SUM-0765 | manifest | PASS | checksum row models/autonomy/controls/AUT-C06.model.json verifies |
| MANIFEST-SUM-0766 | manifest | PASS | checksum row models/autonomy/controls/AUT-C07.model.json verifies |
| MANIFEST-SUM-0767 | manifest | PASS | checksum row models/autonomy/controls/AUT-C08.model.json verifies |
| MANIFEST-SUM-0768 | manifest | PASS | checksum row models/autonomy/controls/AUT-C09.model.json verifies |
| MANIFEST-SUM-0769 | manifest | PASS | checksum row models/autonomy/controls/AUT-C10.model.json verifies |
| MANIFEST-SUM-0770 | manifest | PASS | checksum row models/autonomy/controls/AUT-C11.model.json verifies |
| MANIFEST-SUM-0771 | manifest | PASS | checksum row models/autonomy/controls/AUT-C12.model.json verifies |
| MANIFEST-SUM-0772 | manifest | PASS | checksum row models/corridors/COR-POS-01.model.json verifies |
| MANIFEST-SUM-0773 | manifest | PASS | checksum row models/corridors/COR-POS-02-COMPOSED.model.json verifies |
| MANIFEST-SUM-0774 | manifest | PASS | checksum row models/corridors/COR-POS-02A.model.json verifies |
| MANIFEST-SUM-0775 | manifest | PASS | checksum row models/corridors/COR-POS-02B.model.json verifies |
| MANIFEST-SUM-0776 | manifest | PASS | checksum row models/corridors/controls/COMP-C01.model.json verifies |
| MANIFEST-SUM-0777 | manifest | PASS | checksum row models/corridors/controls/COMP-C02.model.json verifies |
| MANIFEST-SUM-0778 | manifest | PASS | checksum row models/corridors/controls/COMP-C03.model.json verifies |
| MANIFEST-SUM-0779 | manifest | PASS | checksum row models/corridors/controls/COR-C01.model.json verifies |
| MANIFEST-SUM-0780 | manifest | PASS | checksum row models/corridors/controls/COR-C02.model.json verifies |
| MANIFEST-SUM-0781 | manifest | PASS | checksum row models/corridors/controls/COR-C03.model.json verifies |
| MANIFEST-SUM-0782 | manifest | PASS | checksum row models/corridors/controls/COR-C04.model.json verifies |
| MANIFEST-SUM-0783 | manifest | PASS | checksum row models/corridors/controls/COR-C05.model.json verifies |
| MANIFEST-SUM-0784 | manifest | PASS | checksum row models/corridors/controls/COR-C06.model.json verifies |
| MANIFEST-SUM-0785 | manifest | PASS | checksum row models/corridors/controls/COR-C07.model.json verifies |
| MANIFEST-SUM-0786 | manifest | PASS | checksum row models/corridors/controls/COR-C08.model.json verifies |
| MANIFEST-SUM-0787 | manifest | PASS | checksum row models/corridors/controls/COR-C09.model.json verifies |
| MANIFEST-SUM-0788 | manifest | PASS | checksum row models/corridors/controls/COR-C10.model.json verifies |
| MANIFEST-SUM-0789 | manifest | PASS | checksum row models/corridors/controls/COR-C11.model.json verifies |
| MANIFEST-SUM-0790 | manifest | PASS | checksum row models/corridors/controls/COR-C12.model.json verifies |
| MANIFEST-SUM-0791 | manifest | PASS | checksum row models/corridors/controls/COR-C13.model.json verifies |
| MANIFEST-SUM-0792 | manifest | PASS | checksum row models/corridors/controls/COR-C14.model.json verifies |
| MANIFEST-SUM-0793 | manifest | PASS | checksum row models/corridors/controls/COR-C15.model.json verifies |
| MANIFEST-SUM-0794 | manifest | PASS | checksum row models/corridors/controls/COR-C16.model.json verifies |
| MANIFEST-SUM-0795 | manifest | PASS | checksum row models/corridors/controls/COR-C17.model.json verifies |
| MANIFEST-SUM-0796 | manifest | PASS | checksum row models/corridors/controls/COR-C18.model.json verifies |
| MANIFEST-SUM-0797 | manifest | PASS | checksum row models/corridors/controls/COR-C19.model.json verifies |
| MANIFEST-SUM-0798 | manifest | PASS | checksum row models/corridors/controls/COR-C20.model.json verifies |
| MANIFEST-SUM-0799 | manifest | PASS | checksum row models/corridors/controls/COR-C21.model.json verifies |
| MANIFEST-SUM-0800 | manifest | PASS | checksum row models/corridors/controls/COR-C22.model.json verifies |
| MANIFEST-SUM-0801 | manifest | PASS | checksum row models/countermodels/CM-01.md verifies |
| MANIFEST-SUM-0802 | manifest | PASS | checksum row models/countermodels/CM-01.model.json verifies |
| MANIFEST-SUM-0803 | manifest | PASS | checksum row models/countermodels/CM-02.md verifies |
| MANIFEST-SUM-0804 | manifest | PASS | checksum row models/countermodels/CM-02.model.json verifies |
| MANIFEST-SUM-0805 | manifest | PASS | checksum row models/countermodels/CM-03.md verifies |
| MANIFEST-SUM-0806 | manifest | PASS | checksum row models/countermodels/CM-03.model.json verifies |
| MANIFEST-SUM-0807 | manifest | PASS | checksum row models/countermodels/CM-04.md verifies |
| MANIFEST-SUM-0808 | manifest | PASS | checksum row models/countermodels/CM-04.model.json verifies |
| MANIFEST-SUM-0809 | manifest | PASS | checksum row models/countermodels/CM-05.md verifies |
| MANIFEST-SUM-0810 | manifest | PASS | checksum row models/countermodels/CM-05.model.json verifies |
| MANIFEST-SUM-0811 | manifest | PASS | checksum row models/countermodels/CM-06.md verifies |
| MANIFEST-SUM-0812 | manifest | PASS | checksum row models/countermodels/CM-06.model.json verifies |
| MANIFEST-SUM-0813 | manifest | PASS | checksum row models/countermodels/CM-07.md verifies |
| MANIFEST-SUM-0814 | manifest | PASS | checksum row models/countermodels/CM-07.model.json verifies |
| MANIFEST-SUM-0815 | manifest | PASS | checksum row models/countermodels/CM-08.md verifies |
| MANIFEST-SUM-0816 | manifest | PASS | checksum row models/countermodels/CM-08.model.json verifies |
| MANIFEST-SUM-0817 | manifest | PASS | checksum row models/countermodels/CM-09.md verifies |
| MANIFEST-SUM-0818 | manifest | PASS | checksum row models/countermodels/CM-09.model.json verifies |
| MANIFEST-SUM-0819 | manifest | PASS | checksum row models/countermodels/CM-10.md verifies |
| MANIFEST-SUM-0820 | manifest | PASS | checksum row models/countermodels/CM-10.model.json verifies |
| MANIFEST-SUM-0821 | manifest | PASS | checksum row models/countermodels/CM-11.md verifies |
| MANIFEST-SUM-0822 | manifest | PASS | checksum row models/countermodels/CM-11.model.json verifies |
| MANIFEST-SUM-0823 | manifest | PASS | checksum row models/countermodels/CM-12.md verifies |
| MANIFEST-SUM-0824 | manifest | PASS | checksum row models/countermodels/CM-12.model.json verifies |
| MANIFEST-SUM-0825 | manifest | PASS | checksum row models/countermodels/CM-13.md verifies |
| MANIFEST-SUM-0826 | manifest | PASS | checksum row models/countermodels/CM-13.model.json verifies |
| MANIFEST-SUM-0827 | manifest | PASS | checksum row models/countermodels/CM-14.md verifies |
| MANIFEST-SUM-0828 | manifest | PASS | checksum row models/countermodels/CM-14.model.json verifies |
| MANIFEST-SUM-0829 | manifest | PASS | checksum row models/countermodels/CM-15.md verifies |
| MANIFEST-SUM-0830 | manifest | PASS | checksum row models/countermodels/CM-15.model.json verifies |
| MANIFEST-SUM-0831 | manifest | PASS | checksum row models/countermodels/INDEX.md verifies |
| MANIFEST-SUM-0832 | manifest | PASS | checksum row models/direct_successor/DS-POS-01.model.json verifies |
| MANIFEST-SUM-0833 | manifest | PASS | checksum row models/direct_successor/DS-POS-02A.model.json verifies |
| MANIFEST-SUM-0834 | manifest | PASS | checksum row models/direct_successor/DS-POS-02B.model.json verifies |
| MANIFEST-SUM-0835 | manifest | PASS | checksum row models/direct_successor/controls/DS-C01.model.json verifies |
| MANIFEST-SUM-0836 | manifest | PASS | checksum row models/direct_successor/controls/DS-C02.model.json verifies |
| MANIFEST-SUM-0837 | manifest | PASS | checksum row models/direct_successor/controls/DS-C03.model.json verifies |
| MANIFEST-SUM-0838 | manifest | PASS | checksum row models/direct_successor/controls/DS-C04.model.json verifies |
| MANIFEST-SUM-0839 | manifest | PASS | checksum row models/direct_successor/controls/DS-C05.model.json verifies |
| MANIFEST-SUM-0840 | manifest | PASS | checksum row models/direct_successor/controls/DS-C06.model.json verifies |
| MANIFEST-SUM-0841 | manifest | PASS | checksum row models/direct_successor/controls/DS-C07.model.json verifies |
| MANIFEST-SUM-0842 | manifest | PASS | checksum row models/direct_successor/controls/DS-C08.model.json verifies |
| MANIFEST-SUM-0843 | manifest | PASS | checksum row models/direct_successor/controls/DS-C09.model.json verifies |
| MANIFEST-SUM-0844 | manifest | PASS | checksum row models/direct_successor/controls/DS-C10.model.json verifies |
| MANIFEST-SUM-0845 | manifest | PASS | checksum row models/direct_successor/controls/DS-C11.model.json verifies |
| MANIFEST-SUM-0846 | manifest | PASS | checksum row models/direct_successor/controls/DS-C12.model.json verifies |
| MANIFEST-SUM-0847 | manifest | PASS | checksum row models/direct_successor/controls/DS-C13.model.json verifies |
| MANIFEST-SUM-0848 | manifest | PASS | checksum row models/direct_successor/controls/DS-C14.model.json verifies |
| MANIFEST-SUM-0849 | manifest | PASS | checksum row models/direct_successor/controls/DS-C15.model.json verifies |
| MANIFEST-SUM-0850 | manifest | PASS | checksum row models/direct_successor/controls/DS-C16.model.json verifies |
| MANIFEST-SUM-0851 | manifest | PASS | checksum row models/fiach/FIACH-POS-01.model.json verifies |
| MANIFEST-SUM-0852 | manifest | PASS | checksum row models/fiach/controls/FIACH-C01.model.json verifies |
| MANIFEST-SUM-0853 | manifest | PASS | checksum row models/fiach/controls/FIACH-C02.model.json verifies |
| MANIFEST-SUM-0854 | manifest | PASS | checksum row models/fiach/controls/FIACH-C03.model.json verifies |
| MANIFEST-SUM-0855 | manifest | PASS | checksum row models/fiach/controls/FIACH-C04.model.json verifies |
| MANIFEST-SUM-0856 | manifest | PASS | checksum row models/fiach/controls/FIACH-C05.model.json verifies |
| MANIFEST-SUM-0857 | manifest | PASS | checksum row models/fiach/controls/FIACH-C06.model.json verifies |
| MANIFEST-SUM-0858 | manifest | PASS | checksum row models/memory/MEM-FLAT-01.model.json verifies |
| MANIFEST-SUM-0859 | manifest | PASS | checksum row models/memory/MEM-POS-01.model.json verifies |
| MANIFEST-SUM-0860 | manifest | PASS | checksum row models/packages/PKG-POS-01-TARGET.model.json verifies |
| MANIFEST-SUM-0861 | manifest | PASS | checksum row models/packages/PKG-POS-02-SOURCE.model.json verifies |
| MANIFEST-SUM-0862 | manifest | PASS | checksum row models/packages/PKG-POS-03-FIACH-SOURCE.model.json verifies |
| MANIFEST-SUM-0863 | manifest | PASS | checksum row models/packages/PKG-POS-04-FIACH-TARGET.model.json verifies |
| MANIFEST-SUM-0864 | manifest | PASS | checksum row models/packages/STG-POS-01.assembly.json verifies |
| MANIFEST-SUM-0865 | manifest | PASS | checksum row models/packages/STG-POS-02-FIACH.assembly.json verifies |
| MANIFEST-SUM-0866 | manifest | PASS | checksum row models/packages/controls/PC-01.model.json verifies |
| MANIFEST-SUM-0867 | manifest | PASS | checksum row models/packages/controls/PC-02.model.json verifies |
| MANIFEST-SUM-0868 | manifest | PASS | checksum row models/packages/controls/PC-03.model.json verifies |
| MANIFEST-SUM-0869 | manifest | PASS | checksum row models/packages/controls/PC-04.model.json verifies |
| MANIFEST-SUM-0870 | manifest | PASS | checksum row models/packages/controls/PC-05.model.json verifies |
| MANIFEST-SUM-0871 | manifest | PASS | checksum row models/packages/controls/PC-06.model.json verifies |
| MANIFEST-SUM-0872 | manifest | PASS | checksum row models/packages/controls/PC-07.model.json verifies |
| MANIFEST-SUM-0873 | manifest | PASS | checksum row models/packages/controls/PC-08.model.json verifies |
| MANIFEST-SUM-0874 | manifest | PASS | checksum row models/packages/controls/PC-09.model.json verifies |
| MANIFEST-SUM-0875 | manifest | PASS | checksum row models/packages/controls/PC-10.model.json verifies |
| MANIFEST-SUM-0876 | manifest | PASS | checksum row models/packages/controls/PC-11.model.json verifies |
| MANIFEST-SUM-0877 | manifest | PASS | checksum row models/packages/controls/PC-12.model.json verifies |
| MANIFEST-SUM-0878 | manifest | PASS | checksum row models/packages/controls/PC-13.model.json verifies |
| MANIFEST-SUM-0879 | manifest | PASS | checksum row models/packages/controls/PC-14.model.json verifies |
| MANIFEST-SUM-0880 | manifest | PASS | checksum row models/packages/controls/PC-15.model.json verifies |
| MANIFEST-SUM-0881 | manifest | PASS | checksum row models/packages/controls/PC-16.model.json verifies |
| MANIFEST-SUM-0882 | manifest | PASS | checksum row models/packages/controls/PC-17.model.json verifies |
| MANIFEST-SUM-0883 | manifest | PASS | checksum row models/packages/controls/SC-01.assembly.json verifies |
| MANIFEST-SUM-0884 | manifest | PASS | checksum row models/routes/ROUTE-NEG-01.model.json verifies |
| MANIFEST-SUM-0885 | manifest | PASS | checksum row models/routes/ROUTE-POS-01.model.json verifies |
| MANIFEST-SUM-0886 | manifest | PASS | checksum row models/transport/TR-POS-01.model.json verifies |
| MANIFEST-SUM-0887 | manifest | PASS | checksum row models/transport/TR-POS-02-FLAT.model.json verifies |
| MANIFEST-SUM-0888 | manifest | PASS | checksum row models/transport/controls/ARROW-C01.model.json verifies |
| MANIFEST-SUM-0889 | manifest | PASS | checksum row models/transport/controls/ARROW-C02.model.json verifies |
| MANIFEST-SUM-0890 | manifest | PASS | checksum row models/transport/controls/ARROW-C03.model.json verifies |
| MANIFEST-SUM-0891 | manifest | PASS | checksum row models/transport/controls/ARROW-C04.model.json verifies |
| MANIFEST-SUM-0892 | manifest | PASS | checksum row models/transport/controls/MEM-C01.model.json verifies |
| MANIFEST-SUM-0893 | manifest | PASS | checksum row models/transport/controls/ROUTE-C01.model.json verifies |
| MANIFEST-SUM-0894 | manifest | PASS | checksum row models/transport/controls/ROUTE-C02.model.json verifies |
| MANIFEST-SUM-0895 | manifest | PASS | checksum row models/transport/controls/ROUTE-C03.model.json verifies |
| MANIFEST-SUM-0896 | manifest | PASS | checksum row models/transport/controls/ROUTE-C04.model.json verifies |
| MANIFEST-SUM-0897 | manifest | PASS | checksum row models/transport/controls/ROUTE-C05.model.json verifies |
| MANIFEST-SUM-0898 | manifest | PASS | checksum row models/transport/controls/ROUTE-C06.model.json verifies |
| MANIFEST-SUM-0899 | manifest | PASS | checksum row models/transport/controls/ROUTE-C07.model.json verifies |
| MANIFEST-SUM-0900 | manifest | PASS | checksum row models/transport/controls/ROUTE-C08.model.json verifies |
| MANIFEST-SUM-0901 | manifest | PASS | checksum row models/transport/controls/TR-C01.model.json verifies |
| MANIFEST-SUM-0902 | manifest | PASS | checksum row models/transport/controls/TR-C02.model.json verifies |
| MANIFEST-SUM-0903 | manifest | PASS | checksum row models/transport/controls/TR-C03.model.json verifies |
| MANIFEST-SUM-0904 | manifest | PASS | checksum row models/transport/controls/TR-C04.model.json verifies |
| MANIFEST-SUM-0905 | manifest | PASS | checksum row models/transport/controls/TR-C05.model.json verifies |
| MANIFEST-SUM-0906 | manifest | PASS | checksum row models/transport/controls/TR-C06.model.json verifies |
| MANIFEST-SUM-0907 | manifest | PASS | checksum row models/transport/controls/TR-C07.model.json verifies |
| MANIFEST-SUM-0908 | manifest | PASS | checksum row models/transport/controls/TR-C08.model.json verifies |
| MANIFEST-SUM-0909 | manifest | PASS | checksum row models/transport/controls/TR-C09.model.json verifies |
| MANIFEST-SUM-0910 | manifest | PASS | checksum row models/transport/controls/TR-C10.model.json verifies |
| MANIFEST-SUM-0911 | manifest | PASS | checksum row models/transport/controls/TR-C11.model.json verifies |
| MANIFEST-SUM-0912 | manifest | PASS | checksum row models/transport/controls/TR-C12.model.json verifies |
| MANIFEST-SUM-0913 | manifest | PASS | checksum row models/transport/controls/TR-C13.model.json verifies |
| MANIFEST-SUM-0914 | manifest | PASS | checksum row models/transport/controls/TR-C14.model.json verifies |
| MANIFEST-SUM-0915 | manifest | PASS | checksum row models/transport/controls/TR-C15.model.json verifies |
| MANIFEST-SUM-0916 | manifest | PASS | checksum row pyproject.toml verifies |
| MANIFEST-SUM-0917 | manifest | PASS | checksum row registries/ASSUMPTION_LEDGER.csv verifies |
| MANIFEST-SUM-0918 | manifest | PASS | checksum row registries/AUTONOMY_CONTROL_REGISTRY.csv verifies |
| MANIFEST-SUM-0919 | manifest | PASS | checksum row registries/AUTONOMY_SEARCH_REGISTRY.csv verifies |
| MANIFEST-SUM-0920 | manifest | PASS | checksum row registries/AUTONOMY_WITNESS_REGISTRY.csv verifies |
| MANIFEST-SUM-0921 | manifest | PASS | checksum row registries/CERTIFICATE_SCHEMA_REGISTRY.csv verifies |
| MANIFEST-SUM-0922 | manifest | PASS | checksum row registries/CLAIM_LANE_REGISTRY.csv verifies |
| MANIFEST-SUM-0923 | manifest | PASS | checksum row registries/CORRIDOR_COMPOSITION_REGISTRY.csv verifies |
| MANIFEST-SUM-0924 | manifest | PASS | checksum row registries/CORRIDOR_CONTROL_REGISTRY.csv verifies |
| MANIFEST-SUM-0925 | manifest | PASS | checksum row registries/CORRIDOR_SEARCH_REGISTRY.csv verifies |
| MANIFEST-SUM-0926 | manifest | PASS | checksum row registries/COUNTERMODEL_REGISTRY.csv verifies |
| MANIFEST-SUM-0927 | manifest | PASS | checksum row registries/DEFINITION_REGISTRY.csv verifies |
| MANIFEST-SUM-0928 | manifest | PASS | checksum row registries/DEPENDENCY_EDGES.csv verifies |
| MANIFEST-SUM-0929 | manifest | PASS | checksum row registries/DIRECT_SUCCESSOR_CONTROL_REGISTRY.csv verifies |
| MANIFEST-SUM-0930 | manifest | PASS | checksum row registries/DIRECT_SUCCESSOR_PATH_REGISTRY.csv verifies |
| MANIFEST-SUM-0931 | manifest | PASS | checksum row registries/DIRECT_SUCCESSOR_REGISTRY.csv verifies |
| MANIFEST-SUM-0932 | manifest | PASS | checksum row registries/FIACH_LANE_CONTROL_REGISTRY.csv verifies |
| MANIFEST-SUM-0933 | manifest | PASS | checksum row registries/FIACH_WITNESS_REGISTRY.csv verifies |
| MANIFEST-SUM-0934 | manifest | PASS | checksum row registries/HANDOFF_ALIGNED_PACKAGE_REGISTRY.csv verifies |
| MANIFEST-SUM-0935 | manifest | PASS | checksum row registries/KILL_CRITERIA.csv verifies |
| MANIFEST-SUM-0936 | manifest | PASS | checksum row registries/MEMORY_REPAIR_REGISTRY.csv verifies |
| MANIFEST-SUM-0937 | manifest | PASS | checksum row registries/MINIMALITY_LEDGER.csv verifies |
| MANIFEST-SUM-0938 | manifest | PASS | checksum row registries/OVERLAP_DIRECT_COMPARISON.csv verifies |
| MANIFEST-SUM-0939 | manifest | PASS | checksum row registries/PACKAGE_CONTROL_REGISTRY.csv verifies |
| MANIFEST-SUM-0940 | manifest | PASS | checksum row registries/PACKAGE_OBLIGATION_REGISTRY.csv verifies |
| MANIFEST-SUM-0941 | manifest | PASS | checksum row registries/PACKAGE_WITNESS_REGISTRY.csv verifies |
| MANIFEST-SUM-0942 | manifest | PASS | checksum row registries/PROJECT_REGISTRY.json verifies |
| MANIFEST-SUM-0943 | manifest | PASS | checksum row registries/RECORD_ARROW_REGISTRY.csv verifies |
| MANIFEST-SUM-0944 | manifest | PASS | checksum row registries/ROUTE_DISCIPLINE_REGISTRY.csv verifies |
| MANIFEST-SUM-0945 | manifest | PASS | checksum row registries/STAGED_ASSEMBLY_OBLIGATION_REGISTRY.csv verifies |
| MANIFEST-SUM-0946 | manifest | PASS | checksum row registries/TEMPORAL_AMENDMENT_MAP.csv verifies |
| MANIFEST-SUM-0947 | manifest | PASS | checksum row registries/TEMPORAL_CORRIDOR_WITNESS_REGISTRY.csv verifies |
| MANIFEST-SUM-0948 | manifest | PASS | checksum row registries/TEMPORAL_TRANSPORT_WITNESS_REGISTRY.csv verifies |
| MANIFEST-SUM-0949 | manifest | PASS | checksum row registries/THEOREM_REGISTRY.csv verifies |
| MANIFEST-SUM-0950 | manifest | PASS | checksum row registries/TOY_MODEL_REGISTRY.csv verifies |
| MANIFEST-SUM-0951 | manifest | PASS | checksum row registries/TRANSPORT_CONTROL_REGISTRY.csv verifies |
| MANIFEST-SUM-0952 | manifest | PASS | checksum row requirements-lock.txt verifies |
| MANIFEST-SUM-0953 | manifest | PASS | checksum row scenarios/.gitkeep verifies |
| MANIFEST-SUM-0954 | manifest | PASS | checksum row scenarios/CANONICAL_BATTERY.md verifies |
| MANIFEST-SUM-0955 | manifest | PASS | checksum row scenarios/EXIT_GATE_AUDIT.md verifies |
| MANIFEST-SUM-0956 | manifest | PASS | checksum row scenarios/NEUTRAL_TRANSFER_SCHEMA.md verifies |
| MANIFEST-SUM-0957 | manifest | PASS | checksum row scenarios/OUTCOME_LABEL_REGISTRY.csv verifies |
| MANIFEST-SUM-0958 | manifest | PASS | checksum row scenarios/OUTCOME_TAXONOMY.md verifies |
| MANIFEST-SUM-0959 | manifest | PASS | checksum row scenarios/PROTOCOL_AXIS_DICTIONARY.md verifies |
| MANIFEST-SUM-0960 | manifest | PASS | checksum row scenarios/PROTOCOL_AXIS_MATRIX.csv verifies |
| MANIFEST-SUM-0961 | manifest | PASS | checksum row scenarios/PROTOCOL_AXIS_REGISTRY.csv verifies |
| MANIFEST-SUM-0962 | manifest | PASS | checksum row scenarios/SCENARIO_REGISTRY.json verifies |
| MANIFEST-SUM-0963 | manifest | PASS | checksum row scenarios/cards/INDEX.md verifies |
| MANIFEST-SUM-0964 | manifest | PASS | checksum row scenarios/cards/S01.md verifies |
| MANIFEST-SUM-0965 | manifest | PASS | checksum row scenarios/cards/S02.md verifies |
| MANIFEST-SUM-0966 | manifest | PASS | checksum row scenarios/cards/S03.md verifies |
| MANIFEST-SUM-0967 | manifest | PASS | checksum row scenarios/cards/S04.md verifies |
| MANIFEST-SUM-0968 | manifest | PASS | checksum row scenarios/cards/S05.md verifies |
| MANIFEST-SUM-0969 | manifest | PASS | checksum row scenarios/cards/S06.md verifies |
| MANIFEST-SUM-0970 | manifest | PASS | checksum row scenarios/cards/S07.md verifies |
| MANIFEST-SUM-0971 | manifest | PASS | checksum row scenarios/cards/S08.md verifies |
| MANIFEST-SUM-0972 | manifest | PASS | checksum row scenarios/cards/S09.md verifies |
| MANIFEST-SUM-0973 | manifest | PASS | checksum row scenarios/cards/S10.md verifies |
| MANIFEST-SUM-0974 | manifest | PASS | checksum row scenarios/cards/S11.md verifies |
| MANIFEST-SUM-0975 | manifest | PASS | checksum row scenarios/cards/S12.md verifies |
| MANIFEST-SUM-0976 | manifest | PASS | checksum row scenarios/cards/S13.md verifies |
| MANIFEST-SUM-0977 | manifest | PASS | checksum row scenarios/cards/S14.md verifies |
| MANIFEST-SUM-0978 | manifest | PASS | checksum row scenarios/cards/S15.md verifies |
| MANIFEST-SUM-0979 | manifest | PASS | checksum row scenarios/cards/S16.md verifies |
| MANIFEST-SUM-0980 | manifest | PASS | checksum row scenarios/cards/S17.md verifies |
| MANIFEST-SUM-0981 | manifest | PASS | checksum row scenarios/cards/S18.md verifies |
| MANIFEST-SUM-0982 | manifest | PASS | checksum row scenarios/cards/S19.md verifies |
| MANIFEST-SUM-0983 | manifest | PASS | checksum row scenarios/cards/S20.md verifies |
| MANIFEST-SUM-0984 | manifest | PASS | checksum row scenarios/cards/S21.md verifies |
| MANIFEST-SUM-0985 | manifest | PASS | checksum row scenarios/cards/S22.md verifies |
| MANIFEST-SUM-0986 | manifest | PASS | checksum row scenarios/cards/S23.md verifies |
| MANIFEST-SUM-0987 | manifest | PASS | checksum row scenarios/cards/S24.md verifies |
| MANIFEST-SUM-0988 | manifest | PASS | checksum row scenarios/cards/S25.md verifies |
| MANIFEST-SUM-0989 | manifest | PASS | checksum row scenarios/cards/S26.md verifies |
| MANIFEST-SUM-0990 | manifest | PASS | checksum row scenarios/cards/S27.md verifies |
| MANIFEST-SUM-0991 | manifest | PASS | checksum row scenarios/cards/S28.md verifies |
| MANIFEST-SUM-0992 | manifest | PASS | checksum row scenarios/cards/S29.md verifies |
| MANIFEST-SUM-0993 | manifest | PASS | checksum row scenarios/cards/S30.md verifies |
| MANIFEST-SUM-0994 | manifest | PASS | checksum row scenarios/cards/S31.md verifies |
| MANIFEST-SUM-0995 | manifest | PASS | checksum row scenarios/cards/S32.md verifies |
| MANIFEST-SUM-0996 | manifest | PASS | checksum row scenarios/cards/S33.md verifies |
| MANIFEST-SUM-0997 | manifest | PASS | checksum row scenarios/cards/S34.md verifies |
| MANIFEST-SUM-0998 | manifest | PASS | checksum row scenarios/cards/S35.md verifies |
| MANIFEST-SUM-0999 | manifest | PASS | checksum row scenarios/neutral_transfer_frame.dot verifies |
| MANIFEST-SUM-1000 | manifest | PASS | checksum row scenarios/neutral_transfer_frame.png verifies |
| MANIFEST-SUM-1001 | manifest | PASS | checksum row scenarios/neutral_transfer_frame.svg verifies |
| MANIFEST-SUM-1002 | manifest | PASS | checksum row schemas/certificates/aligned_package_certificate.schema.json verifies |
| MANIFEST-SUM-1003 | manifest | PASS | checksum row schemas/certificates/aligned_staged_package_certificate.schema.json verifies |
| MANIFEST-SUM-1004 | manifest | PASS | checksum row schemas/certificates/ancestry_certificate.schema.json verifies |
| MANIFEST-SUM-1005 | manifest | PASS | checksum row schemas/certificates/autonomy_certificate.schema.json verifies |
| MANIFEST-SUM-1006 | manifest | PASS | checksum row schemas/certificates/autonomy_control_certificate.schema.json verifies |
| MANIFEST-SUM-1007 | manifest | PASS | checksum row schemas/certificates/corridor_composition_certificate.schema.json verifies |
| MANIFEST-SUM-1008 | manifest | PASS | checksum row schemas/certificates/corridor_control_certificate.schema.json verifies |
| MANIFEST-SUM-1009 | manifest | PASS | checksum row schemas/certificates/countermodel_certificate.schema.json verifies |
| MANIFEST-SUM-1010 | manifest | PASS | checksum row schemas/certificates/direct_successor.schema.json verifies |
| MANIFEST-SUM-1011 | manifest | PASS | checksum row schemas/certificates/direct_successor_landed.schema.json verifies |
| MANIFEST-SUM-1012 | manifest | PASS | checksum row schemas/certificates/direct_successor_path_certificate.schema.json verifies |
| MANIFEST-SUM-1013 | manifest | PASS | checksum row schemas/certificates/fiach_lane_control_certificate.schema.json verifies |
| MANIFEST-SUM-1014 | manifest | PASS | checksum row schemas/certificates/memory_repair_certificate.schema.json verifies |
| MANIFEST-SUM-1015 | manifest | PASS | checksum row schemas/certificates/package_certificate.schema.json verifies |
| MANIFEST-SUM-1016 | manifest | PASS | checksum row schemas/certificates/package_control_certificate.schema.json verifies |
| MANIFEST-SUM-1017 | manifest | PASS | checksum row schemas/certificates/post_withdrawal_autonomy_certificate.schema.json verifies |
| MANIFEST-SUM-1018 | manifest | PASS | checksum row schemas/certificates/record_arrow_certificate.schema.json verifies |
| MANIFEST-SUM-1019 | manifest | PASS | checksum row schemas/certificates/route_discipline_certificate.schema.json verifies |
| MANIFEST-SUM-1020 | manifest | PASS | checksum row schemas/certificates/staged_package_certificate.schema.json verifies |
| MANIFEST-SUM-1021 | manifest | PASS | checksum row schemas/certificates/strict_temporal_corridor_certificate.schema.json verifies |
| MANIFEST-SUM-1022 | manifest | PASS | checksum row schemas/certificates/temporal_corridor.schema.json verifies |
| MANIFEST-SUM-1023 | manifest | PASS | checksum row schemas/certificates/temporal_fiach_certificate.schema.json verifies |
| MANIFEST-SUM-1024 | manifest | PASS | checksum row schemas/certificates/temporal_fiach_landed_certificate.schema.json verifies |
| MANIFEST-SUM-1025 | manifest | PASS | checksum row schemas/certificates/temporal_signature.schema.json verifies |
| MANIFEST-SUM-1026 | manifest | PASS | checksum row schemas/certificates/temporal_transport_certificate.schema.json verifies |
| MANIFEST-SUM-1027 | manifest | PASS | checksum row schemas/certificates/transport_control_certificate.schema.json verifies |
| MANIFEST-SUM-1028 | manifest | PASS | checksum row schemas/registries/theorem_registry_row.schema.json verifies |
| MANIFEST-SUM-1029 | manifest | PASS | checksum row scripts/build_exp01_assets.py verifies |
| MANIFEST-SUM-1030 | manifest | PASS | checksum row scripts/build_exp02_assets.py verifies |
| MANIFEST-SUM-1031 | manifest | PASS | checksum row scripts/build_exp03_assets.py verifies |
| MANIFEST-SUM-1032 | manifest | PASS | checksum row scripts/build_exp04_assets.py verifies |
| MANIFEST-SUM-1033 | manifest | PASS | checksum row scripts/build_exp05_assets.py verifies |
| MANIFEST-SUM-1034 | manifest | PASS | checksum row scripts/build_exp06_assets.py verifies |
| MANIFEST-SUM-1035 | manifest | PASS | checksum row scripts/build_tt00_assets.py verifies |
| MANIFEST-SUM-1036 | manifest | PASS | checksum row scripts/build_tt01_assets.py verifies |
| MANIFEST-SUM-1037 | manifest | PASS | checksum row scripts/build_tt02_assets.py verifies |
| MANIFEST-SUM-1038 | manifest | PASS | checksum row scripts/build_tt03_assets.py verifies |
| MANIFEST-SUM-1039 | manifest | PASS | checksum row scripts/build_tt04_assets.py verifies |
| MANIFEST-SUM-1040 | manifest | PASS | checksum row scripts/build_tt05_assets.py verifies |
| MANIFEST-SUM-1041 | manifest | PASS | checksum row scripts/enrich_exp01_assets.py verifies |
| MANIFEST-SUM-1042 | manifest | PASS | checksum row scripts/exp02_supplemental.py verifies |
| MANIFEST-SUM-1043 | manifest | PASS | checksum row scripts/exp03_data.py verifies |
| MANIFEST-SUM-1044 | manifest | PASS | checksum row scripts/exp04_data.py verifies |
| MANIFEST-SUM-1045 | manifest | PASS | checksum row scripts/exp05_data.py verifies |
| MANIFEST-SUM-1046 | manifest | PASS | checksum row scripts/exp06_data.py verifies |
| MANIFEST-SUM-1047 | manifest | PASS | checksum row scripts/extract_corpus.py verifies |
| MANIFEST-SUM-1048 | manifest | PASS | checksum row scripts/finalize_exp02_manifest.py verifies |
| MANIFEST-SUM-1049 | manifest | PASS | checksum row scripts/finalize_exp03_manifest.py verifies |
| MANIFEST-SUM-1050 | manifest | PASS | checksum row scripts/finalize_exp04_manifest.py verifies |
| MANIFEST-SUM-1051 | manifest | PASS | checksum row scripts/finalize_exp05_manifest.py verifies |
| MANIFEST-SUM-1052 | manifest | PASS | checksum row scripts/finalize_exp06_manifest.py verifies |
| MANIFEST-SUM-1053 | manifest | PASS | checksum row scripts/finalize_tt00_manifest.py verifies |
| MANIFEST-SUM-1054 | manifest | PASS | checksum row scripts/finalize_tt01_manifest.py verifies |
| MANIFEST-SUM-1055 | manifest | PASS | checksum row scripts/finalize_tt02_manifest.py verifies |
| MANIFEST-SUM-1056 | manifest | PASS | checksum row scripts/finalize_tt03_manifest.py verifies |
| MANIFEST-SUM-1057 | manifest | PASS | checksum row scripts/finalize_tt04_manifest.py verifies |
| MANIFEST-SUM-1058 | manifest | PASS | checksum row scripts/finalize_tt05_manifest.py verifies |
| MANIFEST-SUM-1059 | manifest | PASS | checksum row scripts/rebuild_exp01.sh verifies |
| MANIFEST-SUM-1060 | manifest | PASS | checksum row scripts/rebuild_exp02.sh verifies |
| MANIFEST-SUM-1061 | manifest | PASS | checksum row scripts/rebuild_exp03.sh verifies |
| MANIFEST-SUM-1062 | manifest | PASS | checksum row scripts/rebuild_exp04.sh verifies |
| MANIFEST-SUM-1063 | manifest | PASS | checksum row scripts/rebuild_exp05.sh verifies |
| MANIFEST-SUM-1064 | manifest | PASS | checksum row scripts/rebuild_exp06.sh verifies |
| MANIFEST-SUM-1065 | manifest | PASS | checksum row scripts/rebuild_tt00.sh verifies |
| MANIFEST-SUM-1066 | manifest | PASS | checksum row scripts/rebuild_tt01.sh verifies |
| MANIFEST-SUM-1067 | manifest | PASS | checksum row scripts/rebuild_tt02.sh verifies |
| MANIFEST-SUM-1068 | manifest | PASS | checksum row scripts/rebuild_tt03.sh verifies |
| MANIFEST-SUM-1069 | manifest | PASS | checksum row scripts/rebuild_tt04.sh verifies |
| MANIFEST-SUM-1070 | manifest | PASS | checksum row scripts/rebuild_tt05.sh verifies |
| MANIFEST-SUM-1071 | manifest | PASS | checksum row scripts/run_tt00_checks.sh verifies |
| MANIFEST-SUM-1072 | manifest | PASS | checksum row scripts/run_tt01_checks.sh verifies |
| MANIFEST-SUM-1073 | manifest | PASS | checksum row scripts/run_tt02_checks.sh verifies |
| MANIFEST-SUM-1074 | manifest | PASS | checksum row scripts/run_tt03_checks.sh verifies |
| MANIFEST-SUM-1075 | manifest | PASS | checksum row scripts/run_tt04_checks.sh verifies |
| MANIFEST-SUM-1076 | manifest | PASS | checksum row scripts/run_tt05_checks.sh verifies |
| MANIFEST-SUM-1077 | manifest | PASS | checksum row scripts/tt00_data.py verifies |
| MANIFEST-SUM-1078 | manifest | PASS | checksum row scripts/tt02_data.py verifies |
| MANIFEST-SUM-1079 | manifest | PASS | checksum row scripts/tt03_data.py verifies |
| MANIFEST-SUM-1080 | manifest | PASS | checksum row scripts/tt04_data.py verifies |
| MANIFEST-SUM-1081 | manifest | PASS | checksum row scripts/tt05_data.py verifies |
| MANIFEST-SUM-1082 | manifest | PASS | checksum row scripts/validate_exp01.py verifies |
| MANIFEST-SUM-1083 | manifest | PASS | checksum row scripts/validate_exp02.py verifies |
| MANIFEST-SUM-1084 | manifest | PASS | checksum row scripts/validate_exp03.py verifies |
| MANIFEST-SUM-1085 | manifest | PASS | checksum row scripts/validate_exp04.py verifies |
| MANIFEST-SUM-1086 | manifest | PASS | checksum row scripts/validate_exp05.py verifies |
| MANIFEST-SUM-1087 | manifest | PASS | checksum row scripts/validate_exp06.py verifies |
| MANIFEST-SUM-1088 | manifest | PASS | checksum row scripts/validate_tt00.py verifies |
| MANIFEST-SUM-1089 | manifest | PASS | checksum row scripts/validate_tt01.py verifies |
| MANIFEST-SUM-1090 | manifest | PASS | checksum row scripts/validate_tt02.py verifies |
| MANIFEST-SUM-1091 | manifest | PASS | checksum row scripts/validate_tt03.py verifies |
| MANIFEST-SUM-1092 | manifest | PASS | checksum row scripts/validate_tt04.py verifies |
| MANIFEST-SUM-1093 | manifest | PASS | checksum row scripts/validate_tt05.py verifies |
| MANIFEST-SUM-1094 | manifest | PASS | checksum row scripts/verify_exp03_rebuild.py verifies |
| MANIFEST-SUM-1095 | manifest | PASS | checksum row scripts/verify_exp04_rebuild.py verifies |
| MANIFEST-SUM-1096 | manifest | PASS | checksum row scripts/verify_exp05_rebuild.py verifies |
| MANIFEST-SUM-1097 | manifest | PASS | checksum row scripts/verify_exp06_rebuild.py verifies |
| MANIFEST-SUM-1098 | manifest | PASS | checksum row scripts/verify_tt00_rebuild.py verifies |
| MANIFEST-SUM-1099 | manifest | PASS | checksum row scripts/verify_tt01_rebuild.py verifies |
| MANIFEST-SUM-1100 | manifest | PASS | checksum row scripts/verify_tt02_rebuild.py verifies |
| MANIFEST-SUM-1101 | manifest | PASS | checksum row scripts/verify_tt03_rebuild.py verifies |
| MANIFEST-SUM-1102 | manifest | PASS | checksum row scripts/verify_tt04_rebuild.py verifies |
| MANIFEST-SUM-1103 | manifest | PASS | checksum row scripts/verify_tt05_rebuild.py verifies |
| MANIFEST-SUM-1104 | manifest | PASS | checksum row src/cst_tt/__init__.py verifies |
| MANIFEST-SUM-1105 | manifest | PASS | checksum row src/cst_tt/ancestry.py verifies |
| MANIFEST-SUM-1106 | manifest | PASS | checksum row src/cst_tt/autonomy.py verifies |
| MANIFEST-SUM-1107 | manifest | PASS | checksum row src/cst_tt/bridge_composition_checker.py verifies |
| MANIFEST-SUM-1108 | manifest | PASS | checksum row src/cst_tt/circularity.py verifies |
| MANIFEST-SUM-1109 | manifest | PASS | checksum row src/cst_tt/contracts.py verifies |
| MANIFEST-SUM-1110 | manifest | PASS | checksum row src/cst_tt/corridor.py verifies |
| MANIFEST-SUM-1111 | manifest | PASS | checksum row src/cst_tt/corridor_and_branch_checker.py verifies |
| MANIFEST-SUM-1112 | manifest | PASS | checksum row src/cst_tt/countermodels.py verifies |
| MANIFEST-SUM-1113 | manifest | PASS | checksum row src/cst_tt/fiach.py verifies |
| MANIFEST-SUM-1114 | manifest | PASS | checksum row src/cst_tt/hashing.py verifies |
| MANIFEST-SUM-1115 | manifest | PASS | checksum row src/cst_tt/package.py verifies |
| MANIFEST-SUM-1116 | manifest | PASS | checksum row src/cst_tt/package_auditor.py verifies |
| MANIFEST-SUM-1117 | manifest | PASS | checksum row src/cst_tt/package_gluing.py verifies |
| MANIFEST-SUM-1118 | manifest | PASS | checksum row src/cst_tt/predicates.py verifies |
| MANIFEST-SUM-1119 | manifest | PASS | checksum row src/cst_tt/registry.py verifies |
| MANIFEST-SUM-1120 | manifest | PASS | checksum row src/cst_tt/targets.py verifies |
| MANIFEST-SUM-1121 | manifest | PASS | checksum row src/cst_tt/temporal.py verifies |
| MANIFEST-SUM-1122 | manifest | PASS | checksum row src/cst_tt/transport.py verifies |
| MANIFEST-SUM-1123 | manifest | PASS | checksum row src/cst_tt/transport_auditor.py verifies |
| MANIFEST-SUM-1124 | manifest | PASS | checksum row src/cst_tt/types.py verifies |
| MANIFEST-SUM-1125 | manifest | PASS | checksum row src/cst_tt/withdrawal_autonomy_checker.py verifies |
| MANIFEST-SUM-1126 | manifest | PASS | checksum row synthesis/.gitkeep verifies |
| MANIFEST-SUM-1127 | manifest | PASS | checksum row synthesis/COPY_VS_CONTINUATION_AUDIT.md verifies |
| MANIFEST-SUM-1128 | manifest | PASS | checksum row synthesis/CST-EXP-03_CANDIDATE_GENERATION_SYNTHESIS.md verifies |
| MANIFEST-SUM-1129 | manifest | PASS | checksum row synthesis/EXPLORATION_DOSSIER.md verifies |
| MANIFEST-SUM-1130 | manifest | PASS | checksum row synthesis/FALLBACK_TARGET_SPECIFICATION.md verifies |
| MANIFEST-SUM-1131 | manifest | PASS | checksum row synthesis/FINALIST_COMPARISON.md verifies |
| MANIFEST-SUM-1132 | manifest | PASS | checksum row synthesis/FROZEN_THEOREM_FAMILY.csv verifies |
| MANIFEST-SUM-1133 | manifest | PASS | checksum row synthesis/FROZEN_WITNESS_SUITE.csv verifies |
| MANIFEST-SUM-1134 | manifest | PASS | checksum row synthesis/LATER_LANDING_HANDOFF.md verifies |
| MANIFEST-SUM-1135 | manifest | PASS | checksum row synthesis/PRIMARY_TARGET_SPECIFICATION.md verifies |
| MANIFEST-SUM-1136 | manifest | PASS | checksum row synthesis/README.md verifies |
| MANIFEST-SUM-1137 | manifest | PASS | checksum row synthesis/TARGET_REGISTRY.json verifies |
| MANIFEST-SUM-1138 | manifest | PASS | checksum row synthesis/TARGET_SCENARIO_VERDICTS.csv verifies |
| MANIFEST-SUM-1139 | manifest | PASS | checksum row synthesis/TARGET_SELECTION_SCORECARD.csv verifies |
| MANIFEST-SUM-1140 | manifest | PASS | checksum row synthesis/frozen_target_architecture.dot verifies |
| MANIFEST-SUM-1141 | manifest | PASS | checksum row synthesis/frozen_target_architecture.png verifies |
| MANIFEST-SUM-1142 | manifest | PASS | checksum row synthesis/frozen_target_architecture.svg verifies |
| MANIFEST-SUM-1143 | manifest | PASS | checksum row templates/.gitkeep verifies |
| MANIFEST-SUM-1144 | manifest | PASS | checksum row templates/CANDIDATE_CARD.yml verifies |
| MANIFEST-SUM-1145 | manifest | PASS | checksum row templates/CLAIM_RECORD.yml verifies |
| MANIFEST-SUM-1146 | manifest | PASS | checksum row templates/QUESTION_BANK_RESPONSE.yml verifies |
| MANIFEST-SUM-1147 | manifest | PASS | checksum row templates/SCENARIO_VERDICT_RECORD.yml verifies |
| MANIFEST-SUM-1148 | manifest | PASS | checksum row tests/test_autonomy_certificates.py verifies |
| MANIFEST-SUM-1149 | manifest | PASS | checksum row tests/test_circularity_and_lean_surface.py verifies |
| MANIFEST-SUM-1150 | manifest | PASS | checksum row tests/test_corridor_certificates.py verifies |
| MANIFEST-SUM-1151 | manifest | PASS | checksum row tests/test_corridor_composition.py verifies |
| MANIFEST-SUM-1152 | manifest | PASS | checksum row tests/test_corridor_searches.py verifies |
| MANIFEST-SUM-1153 | manifest | PASS | checksum row tests/test_countermodel_certificates.py verifies |
| MANIFEST-SUM-1154 | manifest | PASS | checksum row tests/test_countermodel_enumeration.py verifies |
| MANIFEST-SUM-1155 | manifest | PASS | checksum row tests/test_direct_successor.py verifies |
| MANIFEST-SUM-1156 | manifest | PASS | checksum row tests/test_fiach_certificate.py verifies |
| MANIFEST-SUM-1157 | manifest | PASS | checksum row tests/test_generated_assets.py verifies |
| MANIFEST-SUM-1158 | manifest | PASS | checksum row tests/test_package_certificates.py verifies |
| MANIFEST-SUM-1159 | manifest | PASS | checksum row tests/test_package_gluing.py verifies |
| MANIFEST-SUM-1160 | manifest | PASS | checksum row tests/test_phase01_boundaries.py verifies |
| MANIFEST-SUM-1161 | manifest | PASS | checksum row tests/test_provenance_and_boundaries.py verifies |
| MANIFEST-SUM-1162 | manifest | PASS | checksum row tests/test_python_types.py verifies |
| MANIFEST-SUM-1163 | manifest | PASS | checksum row tests/test_registries.py verifies |
| MANIFEST-SUM-1164 | manifest | PASS | checksum row tests/test_registry_schema.py verifies |
| MANIFEST-SUM-1165 | manifest | PASS | checksum row tests/test_reproducibility_policy.py verifies |
| MANIFEST-SUM-1166 | manifest | PASS | checksum row tests/test_route_memory_arrow.py verifies |
| MANIFEST-SUM-1167 | manifest | PASS | checksum row tests/test_scaffold_boundaries.py verifies |
| MANIFEST-SUM-1168 | manifest | PASS | checksum row tests/test_schema_examples.py verifies |
| MANIFEST-SUM-1169 | manifest | PASS | checksum row tests/test_temporal_transport_certificates.py verifies |
| MANIFEST-SUM-1170 | manifest | PASS | checksum row tests/test_transport_controls_and_search.py verifies |
| MANIFEST-SUM-1171 | manifest | PASS | checksum row tests/test_tt03_formal_surfaces.py verifies |
| MANIFEST-SUM-1172 | manifest | PASS | checksum row tests/test_tt04_formal_surfaces.py verifies |
| MANIFEST-SUM-1173 | manifest | PASS | checksum row tests/test_tt05_formal_surfaces.py verifies |
| MANIFEST-SUM-1174 | manifest | PASS | checksum row vocabulary/.gitkeep verifies |
| MANIFEST-SUM-1175 | manifest | PASS | checksum row vocabulary/CANONICAL_GLOSSARY.md verifies |
| MANIFEST-SUM-1176 | manifest | PASS | checksum row vocabulary/CLAIM_TYPE_SYSTEM.md verifies |
| MANIFEST-SUM-1177 | manifest | PASS | checksum row vocabulary/TERM_DEPENDENCY_AUDIT.md verifies |
| MANIFEST-SUM-1178 | manifest | PASS | checksum row vocabulary/TYPE_AND_NOTATION_SCAFFOLD.md verifies |
