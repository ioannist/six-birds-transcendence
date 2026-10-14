# CST-TT-01 Validation Report

**Overall status:** PASS
**Checks:** 514 total — 511 passed, 0 failed, 3 skipped

The skipped Lean-build check is not a pass. It records that the pinned compiler was unavailable in this environment.

## Category summary

| Category | PASS | FAIL | SKIP |
|---|---:|---:|---:|
| baseline | 4 | 0 | 2 |
| certificates | 138 | 0 | 0 |
| circularity | 1 | 0 | 0 |
| claim-ceiling | 4 | 0 | 0 |
| countermodels | 78 | 0 | 0 |
| documentation | 36 | 0 | 0 |
| kill-criteria | 3 | 0 | 0 |
| lean-static | 66 | 0 | 0 |
| provenance | 36 | 0 | 0 |
| python | 53 | 0 | 0 |
| registries | 81 | 0 | 0 |
| toolchain | 11 | 0 | 1 |

## Checks

| ID | Category | Status | Detail |
|---|---|---|---|
| `BASE-001` | baseline | **PASS** | repository is a Git worktree |
| `BASE-002` | baseline | **PASS** | CST-TT-00 tag resolves to frozen base |
| `BASE-003` | baseline | **PASS** | frozen CST-TT-00 base is an ancestor of current HEAD |
| `BASE-004` | baseline | **PASS** | repository has no whitespace errors |
| `BASE-005` | baseline | **SKIP** | clean-tree check not requested for this pass |
| `BASE-006` | baseline | **SKIP** | phase tag not required before freeze commit |
| `TOOL-001` | toolchain | **PASS** | Lean toolchain remains pinned to v4.28.0 |
| `TOOL-PIN-01` | toolchain | **PASS** | pyproject contains >=3.13,<3.14 |
| `TOOL-PIN-02` | toolchain | **PASS** | pyproject contains pytest==9.0.2 |
| `TOOL-PIN-03` | toolchain | **PASS** | pyproject contains jsonschema==4.26.0 |
| `TOOL-PIN-04` | toolchain | **PASS** | pyproject contains setuptools==82.0.1 |
| `TOOL-PIN-05` | toolchain | **PASS** | pyproject contains version = "0.1.0" |
| `TOOL-007` | toolchain | **PASS** | running Python is 3.13 (found 3.13.5) |
| `TOOL-LEAN-BUILD` | toolchain | **SKIP** | lean/lake unavailable; no compilation pass claimed |
| `TOOL-STATUS-1` | toolchain | **PASS** | toolchain status names CST-TT-01 |
| `TOOL-STATUS-2` | toolchain | **PASS** | toolchain status records fifteen proof surfaces |
| `TOOL-STATUS-3` | toolchain | **PASS** | toolchain status does not overclaim compilation |
| `TOOL-STATUS-4` | toolchain | **PASS** | toolchain status records the static Lean audit |
| `PY-001` | python | **PASS** | Python source/script bank present (51 files) |
| `PY-COMPILE-001` | python | **PASS** | Python compiles: scripts/build_exp01_assets.py |
| `PY-COMPILE-002` | python | **PASS** | Python compiles: scripts/build_exp02_assets.py |
| `PY-COMPILE-003` | python | **PASS** | Python compiles: scripts/build_exp03_assets.py |
| `PY-COMPILE-004` | python | **PASS** | Python compiles: scripts/build_exp04_assets.py |
| `PY-COMPILE-005` | python | **PASS** | Python compiles: scripts/build_exp05_assets.py |
| `PY-COMPILE-006` | python | **PASS** | Python compiles: scripts/build_exp06_assets.py |
| `PY-COMPILE-007` | python | **PASS** | Python compiles: scripts/build_tt00_assets.py |
| `PY-COMPILE-008` | python | **PASS** | Python compiles: scripts/build_tt01_assets.py |
| `PY-COMPILE-009` | python | **PASS** | Python compiles: scripts/enrich_exp01_assets.py |
| `PY-COMPILE-010` | python | **PASS** | Python compiles: scripts/exp02_supplemental.py |
| `PY-COMPILE-011` | python | **PASS** | Python compiles: scripts/exp03_data.py |
| `PY-COMPILE-012` | python | **PASS** | Python compiles: scripts/exp04_data.py |
| `PY-COMPILE-013` | python | **PASS** | Python compiles: scripts/exp05_data.py |
| `PY-COMPILE-014` | python | **PASS** | Python compiles: scripts/exp06_data.py |
| `PY-COMPILE-015` | python | **PASS** | Python compiles: scripts/extract_corpus.py |
| `PY-COMPILE-016` | python | **PASS** | Python compiles: scripts/finalize_exp02_manifest.py |
| `PY-COMPILE-017` | python | **PASS** | Python compiles: scripts/finalize_exp03_manifest.py |
| `PY-COMPILE-018` | python | **PASS** | Python compiles: scripts/finalize_exp04_manifest.py |
| `PY-COMPILE-019` | python | **PASS** | Python compiles: scripts/finalize_exp05_manifest.py |
| `PY-COMPILE-020` | python | **PASS** | Python compiles: scripts/finalize_exp06_manifest.py |
| `PY-COMPILE-021` | python | **PASS** | Python compiles: scripts/finalize_tt00_manifest.py |
| `PY-COMPILE-022` | python | **PASS** | Python compiles: scripts/finalize_tt01_manifest.py |
| `PY-COMPILE-023` | python | **PASS** | Python compiles: scripts/tt00_data.py |
| `PY-COMPILE-024` | python | **PASS** | Python compiles: scripts/validate_exp01.py |
| `PY-COMPILE-025` | python | **PASS** | Python compiles: scripts/validate_exp02.py |
| `PY-COMPILE-026` | python | **PASS** | Python compiles: scripts/validate_exp03.py |
| `PY-COMPILE-027` | python | **PASS** | Python compiles: scripts/validate_exp04.py |
| `PY-COMPILE-028` | python | **PASS** | Python compiles: scripts/validate_exp05.py |
| `PY-COMPILE-029` | python | **PASS** | Python compiles: scripts/validate_exp06.py |
| `PY-COMPILE-030` | python | **PASS** | Python compiles: scripts/validate_tt00.py |
| `PY-COMPILE-031` | python | **PASS** | Python compiles: scripts/validate_tt01.py |
| `PY-COMPILE-032` | python | **PASS** | Python compiles: scripts/verify_exp03_rebuild.py |
| `PY-COMPILE-033` | python | **PASS** | Python compiles: scripts/verify_exp04_rebuild.py |
| `PY-COMPILE-034` | python | **PASS** | Python compiles: scripts/verify_exp05_rebuild.py |
| `PY-COMPILE-035` | python | **PASS** | Python compiles: scripts/verify_exp06_rebuild.py |
| `PY-COMPILE-036` | python | **PASS** | Python compiles: scripts/verify_tt00_rebuild.py |
| `PY-COMPILE-037` | python | **PASS** | Python compiles: scripts/verify_tt01_rebuild.py |
| `PY-COMPILE-038` | python | **PASS** | Python compiles: src/cst_tt/__init__.py |
| `PY-COMPILE-039` | python | **PASS** | Python compiles: src/cst_tt/ancestry.py |
| `PY-COMPILE-040` | python | **PASS** | Python compiles: src/cst_tt/autonomy.py |
| `PY-COMPILE-041` | python | **PASS** | Python compiles: src/cst_tt/circularity.py |
| `PY-COMPILE-042` | python | **PASS** | Python compiles: src/cst_tt/contracts.py |
| `PY-COMPILE-043` | python | **PASS** | Python compiles: src/cst_tt/corridor.py |
| `PY-COMPILE-044` | python | **PASS** | Python compiles: src/cst_tt/countermodels.py |
| `PY-COMPILE-045` | python | **PASS** | Python compiles: src/cst_tt/hashing.py |
| `PY-COMPILE-046` | python | **PASS** | Python compiles: src/cst_tt/package.py |
| `PY-COMPILE-047` | python | **PASS** | Python compiles: src/cst_tt/predicates.py |
| `PY-COMPILE-048` | python | **PASS** | Python compiles: src/cst_tt/registry.py |
| `PY-COMPILE-049` | python | **PASS** | Python compiles: src/cst_tt/targets.py |
| `PY-COMPILE-050` | python | **PASS** | Python compiles: src/cst_tt/temporal.py |
| `PY-COMPILE-051` | python | **PASS** | Python compiles: src/cst_tt/types.py |
| `PY-TESTS` | python | **PASS** | pytest suite passes |
| `PROV-001` | provenance | **PASS** | frozen temporal-audit source checksum ledger exists |
| `PROV-002` | provenance | **PASS** | seventeen frozen imported surfaces listed (found 17) |
| `PROV-FILE-001` | provenance | **PASS** | imported surface exists: inputs/normative/cst-tt-00/EXECUTION_PLAN.md |
| `PROV-HASH-001` | provenance | **PASS** | imported surface hash matches: inputs/normative/cst-tt-00/EXECUTION_PLAN.md |
| `PROV-FILE-002` | provenance | **PASS** | imported surface exists: inputs/normative/cst-tt-00/FIACH_BASELINE_SPECIFICATION.md |
| `PROV-HASH-002` | provenance | **PASS** | imported surface hash matches: inputs/normative/cst-tt-00/FIACH_BASELINE_SPECIFICATION.md |
| `PROV-FILE-003` | provenance | **PASS** | imported surface exists: inputs/normative/cst-tt-00/IAPS_BASELINE_SPECIFICATION.md |
| `PROV-HASH-003` | provenance | **PASS** | imported surface hash matches: inputs/normative/cst-tt-00/IAPS_BASELINE_SPECIFICATION.md |
| `PROV-FILE-004` | provenance | **PASS** | imported surface exists: inputs/normative/cst-tt-00/TEMPORAL_AUDIT_ORIGINAL_SHA256SUMS.txt |
| `PROV-HASH-004` | provenance | **PASS** | imported surface hash matches: inputs/normative/cst-tt-00/TEMPORAL_AUDIT_ORIGINAL_SHA256SUMS.txt |
| `PROV-FILE-005` | provenance | **PASS** | imported surface exists: inputs/normative/cst-tt-00/TEMPORAL_AUDIT_README.md |
| `PROV-HASH-005` | provenance | **PASS** | imported surface hash matches: inputs/normative/cst-tt-00/TEMPORAL_AUDIT_README.md |
| `PROV-FILE-006` | provenance | **PASS** | imported surface exists: inputs/normative/cst-tt-00/TEMPORAL_SOURCE_MAP.md |
| `PROV-HASH-006` | provenance | **PASS** | imported surface hash matches: inputs/normative/cst-tt-00/TEMPORAL_SOURCE_MAP.md |
| `PROV-FILE-007` | provenance | **PASS** | imported surface exists: inputs/normative/cst-tt-00/TEMPORAL_TRANSCENDENCE_AUDIT.md |
| `PROV-HASH-007` | provenance | **PASS** | imported surface hash matches: inputs/normative/cst-tt-00/TEMPORAL_TRANSCENDENCE_AUDIT.md |
| `PROV-FILE-008` | provenance | **PASS** | imported surface exists: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_An_Audited_Closure_Architecture_for_Consciousness_Exact_Finite_Models_Structural_Theorems_and_Conditional_Realization.tex |
| `PROV-HASH-008` | provenance | **PASS** | imported surface hash matches: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_An_Audited_Closure_Architecture_for_Consciousness_Exact_Finite_Models_Structural_Theorems_and_Conditional_Realization.tex |
| `PROV-FILE-009` | provenance | **PASS** | imported surface exists: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Glass_Is_an_Unclosed_Layer_Kovacs_Memory_as_Predictive_Quotient_Residue.tex |
| `PROV-HASH-009` | provenance | **PASS** | imported surface hash matches: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Glass_Is_an_Unclosed_Layer_Kovacs_Memory_as_Predictive_Quotient_Residue.tex |
| `PROV-FILE-010` | provenance | **PASS** | imported surface exists: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex |
| `PROV-HASH-010` | provenance | **PASS** | imported surface hash matches: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex |
| `PROV-FILE-011` | provenance | **PASS** | imported surface exists: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex |
| `PROV-HASH-011` | provenance | **PASS** | imported surface hash matches: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex |
| `PROV-FILE-012` | provenance | **PASS** | imported surface exists: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_VI_A_Catalog_of_Dynamical_Structural_Laws.tex |
| `PROV-HASH-012` | provenance | **PASS** | imported surface hash matches: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Foundations_VI_A_Catalog_of_Dynamical_Structural_Laws.tex |
| `PROV-FILE-013` | provenance | **PASS** | imported surface exists: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Protocol_Trap_Holonomy_Without_Entropy_Production.tex |
| `PROV-HASH-013` | provenance | **PASS** | imported surface hash matches: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_Six_Birds_Protocol_Trap_Holonomy_Without_Entropy_Production.tex |
| `PROV-FILE-014` | provenance | **PASS** | imported surface exists: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Flatten_a_Stone_with_Six_Birds_Critical_Pairs_Holonomy_and_Confluence_in_Rewriting_Systems.tex |
| `PROV-HASH-014` | provenance | **PASS** | imported surface hash matches: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Flatten_a_Stone_with_Six_Birds_Critical_Pairs_Holonomy_and_Confluence_in_Rewriting_Systems.tex |
| `PROV-FILE-015` | provenance | **PASS** | imported surface exists: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Lay_a_Stone_with_Six_Birds_Finite_State_Semantics_for_Packaging_Directionality_and_Coarse_Graining.tex |
| `PROV-HASH-015` | provenance | **PASS** | imported surface hash matches: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Lay_a_Stone_with_Six_Birds_Finite_State_Semantics_for_Packaging_Directionality_and_Coarse_Graining.tex |
| `PROV-FILE-016` | provenance | **PASS** | imported surface exists: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex |
| `PROV-HASH-016` | provenance | **PASS** | imported surface hash matches: inputs/reference_surfaces/temporal_audit/Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex |
| `PROV-FILE-017` | provenance | **PASS** | imported surface exists: inputs/source_archives/CST_temporal_transcendence_audit.zip |
| `PROV-HASH-017` | provenance | **PASS** | imported surface hash matches: inputs/source_archives/CST_temporal_transcendence_audit.zip |
| `CM-COUNT` | countermodels | **PASS** | fifteen countermodel families enumerate (found 15) |
| `CM-CANDIDATES` | countermodels | **PASS** | total bounded candidates explored is 3,657 |
| `CM-IDS` | countermodels | **PASS** | countermodel identifiers are complete and ordered |
| `CM-01-QUAL` | countermodels | **PASS** | CM-01 satisfies every declared premise and failed-conclusion check |
| `CM-01-MIN` | countermodels | **PASS** | CM-01 carries bounded relative-minimality result |
| `CM-01-RECHECK` | countermodels | **PASS** | CM-01 independently rechecks |
| `CM-01-SMALLER` | countermodels | **PASS** | CM-01 reports smaller candidates |
| `CM-01-SAME` | countermodels | **PASS** | CM-01 has a canonical qualifying witness at minimal size |
| `CM-02-QUAL` | countermodels | **PASS** | CM-02 satisfies every declared premise and failed-conclusion check |
| `CM-02-MIN` | countermodels | **PASS** | CM-02 carries bounded relative-minimality result |
| `CM-02-RECHECK` | countermodels | **PASS** | CM-02 independently rechecks |
| `CM-02-SMALLER` | countermodels | **PASS** | CM-02 reports smaller candidates |
| `CM-02-SAME` | countermodels | **PASS** | CM-02 has a canonical qualifying witness at minimal size |
| `CM-03-QUAL` | countermodels | **PASS** | CM-03 satisfies every declared premise and failed-conclusion check |
| `CM-03-MIN` | countermodels | **PASS** | CM-03 carries bounded relative-minimality result |
| `CM-03-RECHECK` | countermodels | **PASS** | CM-03 independently rechecks |
| `CM-03-SMALLER` | countermodels | **PASS** | CM-03 reports smaller candidates |
| `CM-03-SAME` | countermodels | **PASS** | CM-03 has a canonical qualifying witness at minimal size |
| `CM-04-QUAL` | countermodels | **PASS** | CM-04 satisfies every declared premise and failed-conclusion check |
| `CM-04-MIN` | countermodels | **PASS** | CM-04 carries bounded relative-minimality result |
| `CM-04-RECHECK` | countermodels | **PASS** | CM-04 independently rechecks |
| `CM-04-SMALLER` | countermodels | **PASS** | CM-04 reports smaller candidates |
| `CM-04-SAME` | countermodels | **PASS** | CM-04 has a canonical qualifying witness at minimal size |
| `CM-05-QUAL` | countermodels | **PASS** | CM-05 satisfies every declared premise and failed-conclusion check |
| `CM-05-MIN` | countermodels | **PASS** | CM-05 carries bounded relative-minimality result |
| `CM-05-RECHECK` | countermodels | **PASS** | CM-05 independently rechecks |
| `CM-05-SMALLER` | countermodels | **PASS** | CM-05 reports smaller candidates |
| `CM-05-SAME` | countermodels | **PASS** | CM-05 has a canonical qualifying witness at minimal size |
| `CM-06-QUAL` | countermodels | **PASS** | CM-06 satisfies every declared premise and failed-conclusion check |
| `CM-06-MIN` | countermodels | **PASS** | CM-06 carries bounded relative-minimality result |
| `CM-06-RECHECK` | countermodels | **PASS** | CM-06 independently rechecks |
| `CM-06-SMALLER` | countermodels | **PASS** | CM-06 reports smaller candidates |
| `CM-06-SAME` | countermodels | **PASS** | CM-06 has a canonical qualifying witness at minimal size |
| `CM-07-QUAL` | countermodels | **PASS** | CM-07 satisfies every declared premise and failed-conclusion check |
| `CM-07-MIN` | countermodels | **PASS** | CM-07 carries bounded relative-minimality result |
| `CM-07-RECHECK` | countermodels | **PASS** | CM-07 independently rechecks |
| `CM-07-SMALLER` | countermodels | **PASS** | CM-07 reports smaller candidates |
| `CM-07-SAME` | countermodels | **PASS** | CM-07 has a canonical qualifying witness at minimal size |
| `CM-08-QUAL` | countermodels | **PASS** | CM-08 satisfies every declared premise and failed-conclusion check |
| `CM-08-MIN` | countermodels | **PASS** | CM-08 carries bounded relative-minimality result |
| `CM-08-RECHECK` | countermodels | **PASS** | CM-08 independently rechecks |
| `CM-08-SMALLER` | countermodels | **PASS** | CM-08 reports smaller candidates |
| `CM-08-SAME` | countermodels | **PASS** | CM-08 has a canonical qualifying witness at minimal size |
| `CM-09-QUAL` | countermodels | **PASS** | CM-09 satisfies every declared premise and failed-conclusion check |
| `CM-09-MIN` | countermodels | **PASS** | CM-09 carries bounded relative-minimality result |
| `CM-09-RECHECK` | countermodels | **PASS** | CM-09 independently rechecks |
| `CM-09-SMALLER` | countermodels | **PASS** | CM-09 reports smaller candidates |
| `CM-09-SAME` | countermodels | **PASS** | CM-09 has a canonical qualifying witness at minimal size |
| `CM-10-QUAL` | countermodels | **PASS** | CM-10 satisfies every declared premise and failed-conclusion check |
| `CM-10-MIN` | countermodels | **PASS** | CM-10 carries bounded relative-minimality result |
| `CM-10-RECHECK` | countermodels | **PASS** | CM-10 independently rechecks |
| `CM-10-SMALLER` | countermodels | **PASS** | CM-10 reports smaller candidates |
| `CM-10-SAME` | countermodels | **PASS** | CM-10 has a canonical qualifying witness at minimal size |
| `CM-11-QUAL` | countermodels | **PASS** | CM-11 satisfies every declared premise and failed-conclusion check |
| `CM-11-MIN` | countermodels | **PASS** | CM-11 carries bounded relative-minimality result |
| `CM-11-RECHECK` | countermodels | **PASS** | CM-11 independently rechecks |
| `CM-11-SMALLER` | countermodels | **PASS** | CM-11 reports smaller candidates |
| `CM-11-SAME` | countermodels | **PASS** | CM-11 has a canonical qualifying witness at minimal size |
| `CM-12-QUAL` | countermodels | **PASS** | CM-12 satisfies every declared premise and failed-conclusion check |
| `CM-12-MIN` | countermodels | **PASS** | CM-12 carries bounded relative-minimality result |
| `CM-12-RECHECK` | countermodels | **PASS** | CM-12 independently rechecks |
| `CM-12-SMALLER` | countermodels | **PASS** | CM-12 reports smaller candidates |
| `CM-12-SAME` | countermodels | **PASS** | CM-12 has a canonical qualifying witness at minimal size |
| `CM-13-QUAL` | countermodels | **PASS** | CM-13 satisfies every declared premise and failed-conclusion check |
| `CM-13-MIN` | countermodels | **PASS** | CM-13 carries bounded relative-minimality result |
| `CM-13-RECHECK` | countermodels | **PASS** | CM-13 independently rechecks |
| `CM-13-SMALLER` | countermodels | **PASS** | CM-13 reports smaller candidates |
| `CM-13-SAME` | countermodels | **PASS** | CM-13 has a canonical qualifying witness at minimal size |
| `CM-14-QUAL` | countermodels | **PASS** | CM-14 satisfies every declared premise and failed-conclusion check |
| `CM-14-MIN` | countermodels | **PASS** | CM-14 carries bounded relative-minimality result |
| `CM-14-RECHECK` | countermodels | **PASS** | CM-14 independently rechecks |
| `CM-14-SMALLER` | countermodels | **PASS** | CM-14 reports smaller candidates |
| `CM-14-SAME` | countermodels | **PASS** | CM-14 has a canonical qualifying witness at minimal size |
| `CM-15-QUAL` | countermodels | **PASS** | CM-15 satisfies every declared premise and failed-conclusion check |
| `CM-15-MIN` | countermodels | **PASS** | CM-15 carries bounded relative-minimality result |
| `CM-15-RECHECK` | countermodels | **PASS** | CM-15 independently rechecks |
| `CM-15-SMALLER` | countermodels | **PASS** | CM-15 reports smaller candidates |
| `CM-15-SAME` | countermodels | **PASS** | CM-15 has a canonical qualifying witness at minimal size |
| `KILL-FIACH-04-1` | kill-criteria | **PASS** | detached exact copy passes endpoint package/autonomy premises |
| `KILL-FIACH-04-2` | kill-criteria | **PASS** | detached exact copy fails strict overlap corridor |
| `KILL-FIACH-04-3` | kill-criteria | **PASS** | detached copy is excluded for the intended mixed-stage reason |
| `CERT-SCHEMA` | certificates | **PASS** | countermodel certificate schema is valid Draft 2020-12 |
| `CERT-REG-COUNT` | certificates | **PASS** | countermodel registry has fifteen rows (found 15) |
| `CERT-REG-UNIQUE` | certificates | **PASS** | countermodel IDs are unique |
| `CERT-MODEL-01` | certificates | **PASS** | CM-01 finite model exists |
| `CERT-CARD-01` | certificates | **PASS** | CM-01 human-readable model card exists |
| `CERT-FILE-01` | certificates | **PASS** | CM-01 certificate exists |
| `CERT-VALID-01` | certificates | **PASS** | CM-01 certificate validates against schema |
| `CERT-HASH-01` | certificates | **PASS** | CM-01 certificate binds exact model bytes |
| `CERT-STATUS-01` | certificates | **PASS** | CM-01 result status is checked finite countermodel |
| `CERT-CEILING-01` | certificates | **PASS** | CM-01 retains structural claim ceiling |
| `CERT-LEAN-01` | certificates | **PASS** | CM-01 Lean theorem source exists |
| `CERT-RECHECK-01` | certificates | **PASS** | CM-01 stored model independently rechecks |
| `CERT-MODEL-02` | certificates | **PASS** | CM-02 finite model exists |
| `CERT-CARD-02` | certificates | **PASS** | CM-02 human-readable model card exists |
| `CERT-FILE-02` | certificates | **PASS** | CM-02 certificate exists |
| `CERT-VALID-02` | certificates | **PASS** | CM-02 certificate validates against schema |
| `CERT-HASH-02` | certificates | **PASS** | CM-02 certificate binds exact model bytes |
| `CERT-STATUS-02` | certificates | **PASS** | CM-02 result status is checked finite countermodel |
| `CERT-CEILING-02` | certificates | **PASS** | CM-02 retains structural claim ceiling |
| `CERT-LEAN-02` | certificates | **PASS** | CM-02 Lean theorem source exists |
| `CERT-RECHECK-02` | certificates | **PASS** | CM-02 stored model independently rechecks |
| `CERT-MODEL-03` | certificates | **PASS** | CM-03 finite model exists |
| `CERT-CARD-03` | certificates | **PASS** | CM-03 human-readable model card exists |
| `CERT-FILE-03` | certificates | **PASS** | CM-03 certificate exists |
| `CERT-VALID-03` | certificates | **PASS** | CM-03 certificate validates against schema |
| `CERT-HASH-03` | certificates | **PASS** | CM-03 certificate binds exact model bytes |
| `CERT-STATUS-03` | certificates | **PASS** | CM-03 result status is checked finite countermodel |
| `CERT-CEILING-03` | certificates | **PASS** | CM-03 retains structural claim ceiling |
| `CERT-LEAN-03` | certificates | **PASS** | CM-03 Lean theorem source exists |
| `CERT-RECHECK-03` | certificates | **PASS** | CM-03 stored model independently rechecks |
| `CERT-MODEL-04` | certificates | **PASS** | CM-04 finite model exists |
| `CERT-CARD-04` | certificates | **PASS** | CM-04 human-readable model card exists |
| `CERT-FILE-04` | certificates | **PASS** | CM-04 certificate exists |
| `CERT-VALID-04` | certificates | **PASS** | CM-04 certificate validates against schema |
| `CERT-HASH-04` | certificates | **PASS** | CM-04 certificate binds exact model bytes |
| `CERT-STATUS-04` | certificates | **PASS** | CM-04 result status is checked finite countermodel |
| `CERT-CEILING-04` | certificates | **PASS** | CM-04 retains structural claim ceiling |
| `CERT-LEAN-04` | certificates | **PASS** | CM-04 Lean theorem source exists |
| `CERT-RECHECK-04` | certificates | **PASS** | CM-04 stored model independently rechecks |
| `CERT-MODEL-05` | certificates | **PASS** | CM-05 finite model exists |
| `CERT-CARD-05` | certificates | **PASS** | CM-05 human-readable model card exists |
| `CERT-FILE-05` | certificates | **PASS** | CM-05 certificate exists |
| `CERT-VALID-05` | certificates | **PASS** | CM-05 certificate validates against schema |
| `CERT-HASH-05` | certificates | **PASS** | CM-05 certificate binds exact model bytes |
| `CERT-STATUS-05` | certificates | **PASS** | CM-05 result status is checked finite countermodel |
| `CERT-CEILING-05` | certificates | **PASS** | CM-05 retains structural claim ceiling |
| `CERT-LEAN-05` | certificates | **PASS** | CM-05 Lean theorem source exists |
| `CERT-RECHECK-05` | certificates | **PASS** | CM-05 stored model independently rechecks |
| `CERT-MODEL-06` | certificates | **PASS** | CM-06 finite model exists |
| `CERT-CARD-06` | certificates | **PASS** | CM-06 human-readable model card exists |
| `CERT-FILE-06` | certificates | **PASS** | CM-06 certificate exists |
| `CERT-VALID-06` | certificates | **PASS** | CM-06 certificate validates against schema |
| `CERT-HASH-06` | certificates | **PASS** | CM-06 certificate binds exact model bytes |
| `CERT-STATUS-06` | certificates | **PASS** | CM-06 result status is checked finite countermodel |
| `CERT-CEILING-06` | certificates | **PASS** | CM-06 retains structural claim ceiling |
| `CERT-LEAN-06` | certificates | **PASS** | CM-06 Lean theorem source exists |
| `CERT-RECHECK-06` | certificates | **PASS** | CM-06 stored model independently rechecks |
| `CERT-MODEL-07` | certificates | **PASS** | CM-07 finite model exists |
| `CERT-CARD-07` | certificates | **PASS** | CM-07 human-readable model card exists |
| `CERT-FILE-07` | certificates | **PASS** | CM-07 certificate exists |
| `CERT-VALID-07` | certificates | **PASS** | CM-07 certificate validates against schema |
| `CERT-HASH-07` | certificates | **PASS** | CM-07 certificate binds exact model bytes |
| `CERT-STATUS-07` | certificates | **PASS** | CM-07 result status is checked finite countermodel |
| `CERT-CEILING-07` | certificates | **PASS** | CM-07 retains structural claim ceiling |
| `CERT-LEAN-07` | certificates | **PASS** | CM-07 Lean theorem source exists |
| `CERT-RECHECK-07` | certificates | **PASS** | CM-07 stored model independently rechecks |
| `CERT-MODEL-08` | certificates | **PASS** | CM-08 finite model exists |
| `CERT-CARD-08` | certificates | **PASS** | CM-08 human-readable model card exists |
| `CERT-FILE-08` | certificates | **PASS** | CM-08 certificate exists |
| `CERT-VALID-08` | certificates | **PASS** | CM-08 certificate validates against schema |
| `CERT-HASH-08` | certificates | **PASS** | CM-08 certificate binds exact model bytes |
| `CERT-STATUS-08` | certificates | **PASS** | CM-08 result status is checked finite countermodel |
| `CERT-CEILING-08` | certificates | **PASS** | CM-08 retains structural claim ceiling |
| `CERT-LEAN-08` | certificates | **PASS** | CM-08 Lean theorem source exists |
| `CERT-RECHECK-08` | certificates | **PASS** | CM-08 stored model independently rechecks |
| `CERT-MODEL-09` | certificates | **PASS** | CM-09 finite model exists |
| `CERT-CARD-09` | certificates | **PASS** | CM-09 human-readable model card exists |
| `CERT-FILE-09` | certificates | **PASS** | CM-09 certificate exists |
| `CERT-VALID-09` | certificates | **PASS** | CM-09 certificate validates against schema |
| `CERT-HASH-09` | certificates | **PASS** | CM-09 certificate binds exact model bytes |
| `CERT-STATUS-09` | certificates | **PASS** | CM-09 result status is checked finite countermodel |
| `CERT-CEILING-09` | certificates | **PASS** | CM-09 retains structural claim ceiling |
| `CERT-LEAN-09` | certificates | **PASS** | CM-09 Lean theorem source exists |
| `CERT-RECHECK-09` | certificates | **PASS** | CM-09 stored model independently rechecks |
| `CERT-MODEL-10` | certificates | **PASS** | CM-10 finite model exists |
| `CERT-CARD-10` | certificates | **PASS** | CM-10 human-readable model card exists |
| `CERT-FILE-10` | certificates | **PASS** | CM-10 certificate exists |
| `CERT-VALID-10` | certificates | **PASS** | CM-10 certificate validates against schema |
| `CERT-HASH-10` | certificates | **PASS** | CM-10 certificate binds exact model bytes |
| `CERT-STATUS-10` | certificates | **PASS** | CM-10 result status is checked finite countermodel |
| `CERT-CEILING-10` | certificates | **PASS** | CM-10 retains structural claim ceiling |
| `CERT-LEAN-10` | certificates | **PASS** | CM-10 Lean theorem source exists |
| `CERT-RECHECK-10` | certificates | **PASS** | CM-10 stored model independently rechecks |
| `CERT-MODEL-11` | certificates | **PASS** | CM-11 finite model exists |
| `CERT-CARD-11` | certificates | **PASS** | CM-11 human-readable model card exists |
| `CERT-FILE-11` | certificates | **PASS** | CM-11 certificate exists |
| `CERT-VALID-11` | certificates | **PASS** | CM-11 certificate validates against schema |
| `CERT-HASH-11` | certificates | **PASS** | CM-11 certificate binds exact model bytes |
| `CERT-STATUS-11` | certificates | **PASS** | CM-11 result status is checked finite countermodel |
| `CERT-CEILING-11` | certificates | **PASS** | CM-11 retains structural claim ceiling |
| `CERT-LEAN-11` | certificates | **PASS** | CM-11 Lean theorem source exists |
| `CERT-RECHECK-11` | certificates | **PASS** | CM-11 stored model independently rechecks |
| `CERT-MODEL-12` | certificates | **PASS** | CM-12 finite model exists |
| `CERT-CARD-12` | certificates | **PASS** | CM-12 human-readable model card exists |
| `CERT-FILE-12` | certificates | **PASS** | CM-12 certificate exists |
| `CERT-VALID-12` | certificates | **PASS** | CM-12 certificate validates against schema |
| `CERT-HASH-12` | certificates | **PASS** | CM-12 certificate binds exact model bytes |
| `CERT-STATUS-12` | certificates | **PASS** | CM-12 result status is checked finite countermodel |
| `CERT-CEILING-12` | certificates | **PASS** | CM-12 retains structural claim ceiling |
| `CERT-LEAN-12` | certificates | **PASS** | CM-12 Lean theorem source exists |
| `CERT-RECHECK-12` | certificates | **PASS** | CM-12 stored model independently rechecks |
| `CERT-MODEL-13` | certificates | **PASS** | CM-13 finite model exists |
| `CERT-CARD-13` | certificates | **PASS** | CM-13 human-readable model card exists |
| `CERT-FILE-13` | certificates | **PASS** | CM-13 certificate exists |
| `CERT-VALID-13` | certificates | **PASS** | CM-13 certificate validates against schema |
| `CERT-HASH-13` | certificates | **PASS** | CM-13 certificate binds exact model bytes |
| `CERT-STATUS-13` | certificates | **PASS** | CM-13 result status is checked finite countermodel |
| `CERT-CEILING-13` | certificates | **PASS** | CM-13 retains structural claim ceiling |
| `CERT-LEAN-13` | certificates | **PASS** | CM-13 Lean theorem source exists |
| `CERT-RECHECK-13` | certificates | **PASS** | CM-13 stored model independently rechecks |
| `CERT-MODEL-14` | certificates | **PASS** | CM-14 finite model exists |
| `CERT-CARD-14` | certificates | **PASS** | CM-14 human-readable model card exists |
| `CERT-FILE-14` | certificates | **PASS** | CM-14 certificate exists |
| `CERT-VALID-14` | certificates | **PASS** | CM-14 certificate validates against schema |
| `CERT-HASH-14` | certificates | **PASS** | CM-14 certificate binds exact model bytes |
| `CERT-STATUS-14` | certificates | **PASS** | CM-14 result status is checked finite countermodel |
| `CERT-CEILING-14` | certificates | **PASS** | CM-14 retains structural claim ceiling |
| `CERT-LEAN-14` | certificates | **PASS** | CM-14 Lean theorem source exists |
| `CERT-RECHECK-14` | certificates | **PASS** | CM-14 stored model independently rechecks |
| `CERT-MODEL-15` | certificates | **PASS** | CM-15 finite model exists |
| `CERT-CARD-15` | certificates | **PASS** | CM-15 human-readable model card exists |
| `CERT-FILE-15` | certificates | **PASS** | CM-15 certificate exists |
| `CERT-VALID-15` | certificates | **PASS** | CM-15 certificate validates against schema |
| `CERT-HASH-15` | certificates | **PASS** | CM-15 certificate binds exact model bytes |
| `CERT-STATUS-15` | certificates | **PASS** | CM-15 result status is checked finite countermodel |
| `CERT-CEILING-15` | certificates | **PASS** | CM-15 retains structural claim ceiling |
| `CERT-LEAN-15` | certificates | **PASS** | CM-15 Lean theorem source exists |
| `CERT-RECHECK-15` | certificates | **PASS** | CM-15 stored model independently rechecks |
| `REG-THEOREM-COUNT` | registries | **PASS** | theorem registry retains 35 rows |
| `REG-THEOREM-STATUS` | registries | **PASS** | theorem status split is 21 open / 14 checked ({'open-scaffold': 21, 'checked-finite-countermodel': 14}) |
| `REG-THEOREM-01` | registries | **PASS** | TTH-01 has correct phase-one status |
| `REG-THEOREM-02` | registries | **PASS** | TTH-02 has correct phase-one status |
| `REG-THEOREM-03` | registries | **PASS** | TTH-03 has correct phase-one status |
| `REG-THEOREM-04` | registries | **PASS** | TTH-04 has correct phase-one status |
| `REG-THEOREM-05` | registries | **PASS** | TTH-05 has correct phase-one status |
| `REG-THEOREM-06` | registries | **PASS** | TTH-06 has correct phase-one status |
| `REG-THEOREM-07` | registries | **PASS** | TTH-07 has correct phase-one status |
| `REG-THEOREM-08` | registries | **PASS** | TTH-08 has correct phase-one status |
| `REG-THEOREM-09` | registries | **PASS** | TTH-09 has correct phase-one status |
| `REG-THEOREM-10` | registries | **PASS** | TTH-10 has correct phase-one status |
| `REG-THEOREM-11` | registries | **PASS** | TTN-01 has correct phase-one status |
| `REG-THEOREM-12` | registries | **PASS** | TTN-02 has correct phase-one status |
| `REG-THEOREM-13` | registries | **PASS** | TTN-03 has correct phase-one status |
| `REG-THEOREM-14` | registries | **PASS** | TTN-04 has correct phase-one status |
| `REG-THEOREM-15` | registries | **PASS** | TTN-05 has correct phase-one status |
| `REG-THEOREM-16` | registries | **PASS** | TTN-06 has correct phase-one status |
| `REG-THEOREM-17` | registries | **PASS** | TTN-07 has correct phase-one status |
| `REG-THEOREM-18` | registries | **PASS** | TTN-08 has correct phase-one status |
| `REG-THEOREM-19` | registries | **PASS** | TTN-09 has correct phase-one status |
| `REG-THEOREM-20` | registries | **PASS** | TTN-10 has correct phase-one status |
| `REG-THEOREM-21` | registries | **PASS** | TTN-11 has correct phase-one status |
| `REG-THEOREM-22` | registries | **PASS** | TTN-12 has correct phase-one status |
| `REG-THEOREM-23` | registries | **PASS** | TTN-13 has correct phase-one status |
| `REG-THEOREM-24` | registries | **PASS** | TTN-14 has correct phase-one status |
| `REG-THEOREM-25` | registries | **PASS** | TTD-01 has correct phase-one status |
| `REG-THEOREM-26` | registries | **PASS** | TTD-02 has correct phase-one status |
| `REG-THEOREM-27` | registries | **PASS** | TTD-03 has correct phase-one status |
| `REG-THEOREM-28` | registries | **PASS** | TTF-01 has correct phase-one status |
| `REG-THEOREM-29` | registries | **PASS** | TTF-02 has correct phase-one status |
| `REG-THEOREM-30` | registries | **PASS** | TTF-03 has correct phase-one status |
| `REG-THEOREM-31` | registries | **PASS** | TTF-04 has correct phase-one status |
| `REG-THEOREM-32` | registries | **PASS** | TTF-05 has correct phase-one status |
| `REG-THEOREM-33` | registries | **PASS** | TTF-06 has correct phase-one status |
| `REG-THEOREM-34` | registries | **PASS** | TTF-07 has correct phase-one status |
| `REG-THEOREM-35` | registries | **PASS** | TTF-08 has correct phase-one status |
| `REG-TOY-COUNT` | registries | **PASS** | toy registry retains 21 rows |
| `REG-TOY-STATUS` | registries | **PASS** | toy status split is 14 checked negative / 7 unimplemented ({'specified-not-implemented': 7, 'checked-negative-instance': 14}) |
| `REG-PROJECT-01` | registries | **PASS** | project registry phase='CST-TT-01' |
| `REG-PROJECT-02` | registries | **PASS** | project registry phase_base_tag='CST-TT-00-v1' |
| `REG-PROJECT-03` | registries | **PASS** | project registry phase_base_commit='65b3ab0f94564cee1d16ffb4513045319aaaf6ef' |
| `REG-PROJECT-04` | registries | **PASS** | project registry scientific_results_landed=15 |
| `REG-PROJECT-05` | registries | **PASS** | project registry checked_finite_countermodels=15 |
| `REG-PROJECT-06` | registries | **PASS** | project registry generic_theorems_proved=0 |
| `REG-PROJECT-07` | registries | **PASS** | project registry positive_handoff_witnesses=0 |
| `REG-PROJECT-08` | registries | **PASS** | project registry negative_kernel_status='frozen' |
| `REG-MIN-COUNT` | registries | **PASS** | minimality ledger has fifteen rows |
| `REG-MIN-IDS` | registries | **PASS** | minimality ledger covers every countermodel |
| `REG-MIN-STATUS-01` | registries | **PASS** | CM-01 has bounded minimality status |
| `REG-MIN-SMALL-01` | registries | **PASS** | CM-01 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-02` | registries | **PASS** | CM-02 has bounded minimality status |
| `REG-MIN-SMALL-02` | registries | **PASS** | CM-02 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-03` | registries | **PASS** | CM-03 has bounded minimality status |
| `REG-MIN-SMALL-03` | registries | **PASS** | CM-03 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-04` | registries | **PASS** | CM-04 has bounded minimality status |
| `REG-MIN-SMALL-04` | registries | **PASS** | CM-04 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-05` | registries | **PASS** | CM-05 has bounded minimality status |
| `REG-MIN-SMALL-05` | registries | **PASS** | CM-05 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-06` | registries | **PASS** | CM-06 has bounded minimality status |
| `REG-MIN-SMALL-06` | registries | **PASS** | CM-06 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-07` | registries | **PASS** | CM-07 has bounded minimality status |
| `REG-MIN-SMALL-07` | registries | **PASS** | CM-07 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-08` | registries | **PASS** | CM-08 has bounded minimality status |
| `REG-MIN-SMALL-08` | registries | **PASS** | CM-08 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-09` | registries | **PASS** | CM-09 has bounded minimality status |
| `REG-MIN-SMALL-09` | registries | **PASS** | CM-09 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-10` | registries | **PASS** | CM-10 has bounded minimality status |
| `REG-MIN-SMALL-10` | registries | **PASS** | CM-10 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-11` | registries | **PASS** | CM-11 has bounded minimality status |
| `REG-MIN-SMALL-11` | registries | **PASS** | CM-11 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-12` | registries | **PASS** | CM-12 has bounded minimality status |
| `REG-MIN-SMALL-12` | registries | **PASS** | CM-12 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-13` | registries | **PASS** | CM-13 has bounded minimality status |
| `REG-MIN-SMALL-13` | registries | **PASS** | CM-13 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-14` | registries | **PASS** | CM-14 has bounded minimality status |
| `REG-MIN-SMALL-14` | registries | **PASS** | CM-14 has no smaller qualifying generated candidate |
| `REG-MIN-STATUS-15` | registries | **PASS** | CM-15 has bounded minimality status |
| `REG-MIN-SMALL-15` | registries | **PASS** | CM-15 has no smaller qualifying generated candidate |
| `REG-KILL` | registries | **PASS** | all fourteen kill criteria remain armed |
| `REG-AMEND` | registries | **PASS** | all 20 frozen PTH/FTH prospects remain mapped |
| `LEAN-COUNT` | lean-static | **PASS** | sixteen Lean modules exist under CSTTT (found 16) |
| `LEAN-IMPORT-01` | lean-static | **PASS** | root imports CSTTT.Autonomy.System |
| `LEAN-NS-01` | lean-static | **PASS** | CSTTT.Autonomy.System uses CSTTT namespace |
| `LEAN-DELIM-01` | lean-static | **PASS** | CSTTT.Autonomy.System delimiter counts balance |
| `LEAN-IMPORT-02` | lean-static | **PASS** | root imports CSTTT.Core.Carrier |
| `LEAN-NS-02` | lean-static | **PASS** | CSTTT.Core.Carrier uses CSTTT namespace |
| `LEAN-DELIM-02` | lean-static | **PASS** | CSTTT.Core.Carrier delimiter counts balance |
| `LEAN-IMPORT-03` | lean-static | **PASS** | root imports CSTTT.Core.Episode |
| `LEAN-NS-03` | lean-static | **PASS** | CSTTT.Core.Episode uses CSTTT namespace |
| `LEAN-DELIM-03` | lean-static | **PASS** | CSTTT.Core.Episode delimiter counts balance |
| `LEAN-IMPORT-04` | lean-static | **PASS** | root imports CSTTT.Core.Finite |
| `LEAN-NS-04` | lean-static | **PASS** | CSTTT.Core.Finite uses CSTTT namespace |
| `LEAN-DELIM-04` | lean-static | **PASS** | CSTTT.Core.Finite delimiter counts balance |
| `LEAN-IMPORT-05` | lean-static | **PASS** | root imports CSTTT.Corridor.DirectSuccessor |
| `LEAN-NS-05` | lean-static | **PASS** | CSTTT.Corridor.DirectSuccessor uses CSTTT namespace |
| `LEAN-DELIM-05` | lean-static | **PASS** | CSTTT.Corridor.DirectSuccessor delimiter counts balance |
| `LEAN-IMPORT-06` | lean-static | **PASS** | root imports CSTTT.Corridor.TemporalCorridor |
| `LEAN-NS-06` | lean-static | **PASS** | CSTTT.Corridor.TemporalCorridor uses CSTTT namespace |
| `LEAN-DELIM-06` | lean-static | **PASS** | CSTTT.Corridor.TemporalCorridor delimiter counts balance |
| `LEAN-IMPORT-07` | lean-static | **PASS** | root imports CSTTT.Countermodels.Kernel |
| `LEAN-NS-07` | lean-static | **PASS** | CSTTT.Countermodels.Kernel uses CSTTT namespace |
| `LEAN-DELIM-07` | lean-static | **PASS** | CSTTT.Countermodels.Kernel delimiter counts balance |
| `LEAN-IMPORT-08` | lean-static | **PASS** | root imports CSTTT.Fallback.Ancestry |
| `LEAN-NS-08` | lean-static | **PASS** | CSTTT.Fallback.Ancestry uses CSTTT namespace |
| `LEAN-DELIM-08` | lean-static | **PASS** | CSTTT.Fallback.Ancestry delimiter counts balance |
| `LEAN-IMPORT-09` | lean-static | **PASS** | root imports CSTTT.Package.Clauses |
| `LEAN-NS-09` | lean-static | **PASS** | CSTTT.Package.Clauses uses CSTTT namespace |
| `LEAN-DELIM-09` | lean-static | **PASS** | CSTTT.Package.Clauses delimiter counts balance |
| `LEAN-IMPORT-10` | lean-static | **PASS** | root imports CSTTT.Package.Gluing |
| `LEAN-NS-10` | lean-static | **PASS** | CSTTT.Package.Gluing uses CSTTT namespace |
| `LEAN-DELIM-10` | lean-static | **PASS** | CSTTT.Package.Gluing delimiter counts balance |
| `LEAN-IMPORT-11` | lean-static | **PASS** | root imports CSTTT.Prospects.Statements |
| `LEAN-NS-11` | lean-static | **PASS** | CSTTT.Prospects.Statements uses CSTTT namespace |
| `LEAN-DELIM-11` | lean-static | **PASS** | CSTTT.Prospects.Statements delimiter counts balance |
| `LEAN-IMPORT-12` | lean-static | **PASS** | root imports CSTTT.Targets.TemporalFIACH |
| `LEAN-NS-12` | lean-static | **PASS** | CSTTT.Targets.TemporalFIACH uses CSTTT namespace |
| `LEAN-DELIM-12` | lean-static | **PASS** | CSTTT.Targets.TemporalFIACH delimiter counts balance |
| `LEAN-IMPORT-13` | lean-static | **PASS** | root imports CSTTT.Temporal.Clock |
| `LEAN-NS-13` | lean-static | **PASS** | CSTTT.Temporal.Clock uses CSTTT namespace |
| `LEAN-DELIM-13` | lean-static | **PASS** | CSTTT.Temporal.Clock delimiter counts balance |
| `LEAN-IMPORT-14` | lean-static | **PASS** | root imports CSTTT.Temporal.Closure |
| `LEAN-NS-14` | lean-static | **PASS** | CSTTT.Temporal.Closure uses CSTTT namespace |
| `LEAN-DELIM-14` | lean-static | **PASS** | CSTTT.Temporal.Closure delimiter counts balance |
| `LEAN-IMPORT-15` | lean-static | **PASS** | root imports CSTTT.Temporal.Signature |
| `LEAN-NS-15` | lean-static | **PASS** | CSTTT.Temporal.Signature uses CSTTT namespace |
| `LEAN-DELIM-15` | lean-static | **PASS** | CSTTT.Temporal.Signature delimiter counts balance |
| `LEAN-IMPORT-16` | lean-static | **PASS** | root imports CSTTT.Transport.TemporalBridge |
| `LEAN-NS-16` | lean-static | **PASS** | CSTTT.Transport.TemporalBridge uses CSTTT namespace |
| `LEAN-DELIM-16` | lean-static | **PASS** | CSTTT.Transport.TemporalBridge delimiter counts balance |
| `LEAN-NO-HOLES` | lean-static | **PASS** | Lean sources contain no sorry/admit/axiom/unsafe placeholder |
| `LEAN-CIRC` | circularity | **PASS** | primitive verdict-vocabulary scan has no findings (found 0) |
| `LEAN-KERNEL` | lean-static | **PASS** | explicit countermodel kernel source is present |
| `LEAN-CM-01` | lean-static | **PASS** | kernel contains CM-01 theorem surface |
| `LEAN-CM-02` | lean-static | **PASS** | kernel contains CM-02 theorem surface |
| `LEAN-CM-03` | lean-static | **PASS** | kernel contains CM-03 theorem surface |
| `LEAN-CM-04` | lean-static | **PASS** | kernel contains CM-04 theorem surface |
| `LEAN-CM-05` | lean-static | **PASS** | kernel contains CM-05 theorem surface |
| `LEAN-CM-06` | lean-static | **PASS** | kernel contains CM-06 theorem surface |
| `LEAN-CM-07` | lean-static | **PASS** | kernel contains CM-07 theorem surface |
| `LEAN-CM-08` | lean-static | **PASS** | kernel contains CM-08 theorem surface |
| `LEAN-CM-09` | lean-static | **PASS** | kernel contains CM-09 theorem surface |
| `LEAN-CM-10` | lean-static | **PASS** | kernel contains CM-10 theorem surface |
| `LEAN-CM-11` | lean-static | **PASS** | kernel contains CM-11 theorem surface |
| `LEAN-CM-12` | lean-static | **PASS** | kernel contains CM-12 theorem surface |
| `LEAN-CM-13` | lean-static | **PASS** | kernel contains CM-13 theorem surface |
| `LEAN-CM-14` | lean-static | **PASS** | kernel contains CM-14 theorem surface |
| `LEAN-CM-15` | lean-static | **PASS** | kernel contains CM-15 theorem surface |
| `LEAN-NONCLAIM-sameSubject` | claim-ceiling | **PASS** | kernel excludes verdict primitive sameSubject |
| `LEAN-NONCLAIM-personalIdentity` | claim-ceiling | **PASS** | kernel excludes verdict primitive personalIdentity |
| `LEAN-NONCLAIM-survivesAs` | claim-ceiling | **PASS** | kernel excludes verdict primitive survivesAs |
| `LEAN-NONCLAIM-isConscious` | claim-ceiling | **PASS** | kernel excludes verdict primitive isConscious |
| `DOC-FILE-01` | documentation | **PASS** | documentation exists: docs/NEGATIVE_KERNEL.md |
| `DOC-CONTENT-01-1` | documentation | **PASS** | docs/NEGATIVE_KERNEL.md contains required phrase: fifteen deterministic finite countermodels |
| `DOC-CONTENT-01-2` | documentation | **PASS** | docs/NEGATIVE_KERNEL.md contains required phrase: None establishes or refutes consciousness |
| `DOC-FILE-02` | documentation | **PASS** | documentation exists: docs/COUNTERMODEL_MINIMALITY.md |
| `DOC-CONTENT-02-1` | documentation | **PASS** | docs/COUNTERMODEL_MINIMALITY.md contains required phrase: Minimality is always relative |
| `DOC-CONTENT-02-2` | documentation | **PASS** | docs/COUNTERMODEL_MINIMALITY.md contains required phrase: No claim of absolute minimality |
| `DOC-FILE-03` | documentation | **PASS** | documentation exists: docs/PHASE_BOUNDARY.md |
| `DOC-CONTENT-03-1` | documentation | **PASS** | docs/PHASE_BOUNDARY.md contains required phrase: no positive Temporal-FIACH |
| `DOC-CONTENT-03-2` | documentation | **PASS** | docs/PHASE_BOUNDARY.md contains required phrase: CST-TT-02 |
| `DOC-FILE-04` | documentation | **PASS** | documentation exists: README.md |
| `DOC-CONTENT-04-1` | documentation | **PASS** | README.md contains required phrase: CST-TT-01 |
| `DOC-CONTENT-04-2` | documentation | **PASS** | README.md contains required phrase: no positive Temporal-FIACH witness |
| `DOC-FILE-05` | documentation | **PASS** | documentation exists: STATE.md |
| `DOC-CONTENT-05-1` | documentation | **PASS** | STATE.md contains required phrase: Checked finite countermodels: 15 |
| `DOC-CONTENT-05-2` | documentation | **PASS** | STATE.md contains required phrase: Detached-copy kill criterion: not triggered |
| `DOC-FILE-06` | documentation | **PASS** | documentation exists: manifests/CST-TT-01_COMPLETION_REPORT.md |
| `DOC-CONTENT-06-1` | documentation | **PASS** | manifests/CST-TT-01_COMPLETION_REPORT.md contains required phrase: 3,657 deterministic finite candidates |
| `DOC-CONTENT-06-2` | documentation | **PASS** | manifests/CST-TT-01_COMPLETION_REPORT.md contains required phrase: Temporal-IAPS remains locked |
| `DOC-FILE-07` | documentation | **PASS** | documentation exists: RESTORE_AND_VERIFY.md |
| `DOC-CONTENT-07-1` | documentation | **PASS** | RESTORE_AND_VERIFY.md contains required phrase: CST-TT-01-v1 |
| `DOC-CONTENT-07-2` | documentation | **PASS** | RESTORE_AND_VERIFY.md contains required phrase: lake build |
| `DOC-CM-01` | documentation | **PASS** | negative-kernel document contains CM-01 card |
| `DOC-CM-02` | documentation | **PASS** | negative-kernel document contains CM-02 card |
| `DOC-CM-03` | documentation | **PASS** | negative-kernel document contains CM-03 card |
| `DOC-CM-04` | documentation | **PASS** | negative-kernel document contains CM-04 card |
| `DOC-CM-05` | documentation | **PASS** | negative-kernel document contains CM-05 card |
| `DOC-CM-06` | documentation | **PASS** | negative-kernel document contains CM-06 card |
| `DOC-CM-07` | documentation | **PASS** | negative-kernel document contains CM-07 card |
| `DOC-CM-08` | documentation | **PASS** | negative-kernel document contains CM-08 card |
| `DOC-CM-09` | documentation | **PASS** | negative-kernel document contains CM-09 card |
| `DOC-CM-10` | documentation | **PASS** | negative-kernel document contains CM-10 card |
| `DOC-CM-11` | documentation | **PASS** | negative-kernel document contains CM-11 card |
| `DOC-CM-12` | documentation | **PASS** | negative-kernel document contains CM-12 card |
| `DOC-CM-13` | documentation | **PASS** | negative-kernel document contains CM-13 card |
| `DOC-CM-14` | documentation | **PASS** | negative-kernel document contains CM-14 card |
| `DOC-CM-15` | documentation | **PASS** | negative-kernel document contains CM-15 card |
