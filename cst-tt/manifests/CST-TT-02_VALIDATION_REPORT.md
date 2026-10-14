# CST-TT-02 Validation Report

**Overall status:** PASS
**Checks:** 567 total — 563 passed, 0 failed, 4 skipped

The skipped Lean-build check is not a pass. It records that the pinned compiler was unavailable in this environment.

## Category summary

| Category | PASS | FAIL | SKIP |
|---|---:|---:|---:|
| baseline | 4 | 0 | 2 |
| boundaries | 23 | 0 | 0 |
| bounded-exhaustion | 12 | 0 | 0 |
| controls | 145 | 0 | 0 |
| documentation | 32 | 0 | 0 |
| lean-static | 55 | 0 | 0 |
| manifest | 0 | 0 | 1 |
| package | 42 | 0 | 0 |
| provenance | 19 | 0 | 0 |
| python | 60 | 0 | 0 |
| registries | 63 | 0 | 0 |
| schemas | 65 | 0 | 0 |
| staged-assembly | 18 | 0 | 0 |
| temporal-C6 | 11 | 0 | 0 |
| toolchain | 14 | 0 | 1 |

## Checks

| ID | Category | Status | Detail |
|---|---|---|---|
| `BASE-001` | baseline | **PASS** | repository is a Git worktree |
| `BASE-002` | baseline | **PASS** | CST-TT-01 tag resolves to the frozen phase base |
| `BASE-003` | baseline | **PASS** | frozen CST-TT-01 base is an ancestor of current HEAD |
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
| `TOOL-STATUS-1` | toolchain | **PASS** | toolchain status names CST-TT-02 |
| `TOOL-STATUS-2` | toolchain | **PASS** | toolchain status records two generic package proof sources |
| `TOOL-STATUS-3` | toolchain | **PASS** | toolchain status records two positive package certificates |
| `TOOL-STATUS-4` | toolchain | **PASS** | toolchain status records one staged certificate |
| `TOOL-STATUS-5` | toolchain | **PASS** | toolchain status records eighteen controls |
| `TOOL-STATUS-6` | toolchain | **PASS** | toolchain status does not overclaim compilation |
| `TOOL-STATUS-7` | toolchain | **PASS** | toolchain status records the CST-TT-02 static Lean audit |
| `PY-001` | python | **PASS** | at least twenty-five Python source files are present (58) |
| `PY-COMPILE-001` | python | **PASS** | scripts/build_exp01_assets.py compiles |
| `PY-COMPILE-002` | python | **PASS** | scripts/build_exp02_assets.py compiles |
| `PY-COMPILE-003` | python | **PASS** | scripts/build_exp03_assets.py compiles |
| `PY-COMPILE-004` | python | **PASS** | scripts/build_exp04_assets.py compiles |
| `PY-COMPILE-005` | python | **PASS** | scripts/build_exp05_assets.py compiles |
| `PY-COMPILE-006` | python | **PASS** | scripts/build_exp06_assets.py compiles |
| `PY-COMPILE-007` | python | **PASS** | scripts/build_tt00_assets.py compiles |
| `PY-COMPILE-008` | python | **PASS** | scripts/build_tt01_assets.py compiles |
| `PY-COMPILE-009` | python | **PASS** | scripts/build_tt02_assets.py compiles |
| `PY-COMPILE-010` | python | **PASS** | scripts/enrich_exp01_assets.py compiles |
| `PY-COMPILE-011` | python | **PASS** | scripts/exp02_supplemental.py compiles |
| `PY-COMPILE-012` | python | **PASS** | scripts/exp03_data.py compiles |
| `PY-COMPILE-013` | python | **PASS** | scripts/exp04_data.py compiles |
| `PY-COMPILE-014` | python | **PASS** | scripts/exp05_data.py compiles |
| `PY-COMPILE-015` | python | **PASS** | scripts/exp06_data.py compiles |
| `PY-COMPILE-016` | python | **PASS** | scripts/extract_corpus.py compiles |
| `PY-COMPILE-017` | python | **PASS** | scripts/finalize_exp02_manifest.py compiles |
| `PY-COMPILE-018` | python | **PASS** | scripts/finalize_exp03_manifest.py compiles |
| `PY-COMPILE-019` | python | **PASS** | scripts/finalize_exp04_manifest.py compiles |
| `PY-COMPILE-020` | python | **PASS** | scripts/finalize_exp05_manifest.py compiles |
| `PY-COMPILE-021` | python | **PASS** | scripts/finalize_exp06_manifest.py compiles |
| `PY-COMPILE-022` | python | **PASS** | scripts/finalize_tt00_manifest.py compiles |
| `PY-COMPILE-023` | python | **PASS** | scripts/finalize_tt01_manifest.py compiles |
| `PY-COMPILE-024` | python | **PASS** | scripts/finalize_tt02_manifest.py compiles |
| `PY-COMPILE-025` | python | **PASS** | scripts/tt00_data.py compiles |
| `PY-COMPILE-026` | python | **PASS** | scripts/tt02_data.py compiles |
| `PY-COMPILE-027` | python | **PASS** | scripts/validate_exp01.py compiles |
| `PY-COMPILE-028` | python | **PASS** | scripts/validate_exp02.py compiles |
| `PY-COMPILE-029` | python | **PASS** | scripts/validate_exp03.py compiles |
| `PY-COMPILE-030` | python | **PASS** | scripts/validate_exp04.py compiles |
| `PY-COMPILE-031` | python | **PASS** | scripts/validate_exp05.py compiles |
| `PY-COMPILE-032` | python | **PASS** | scripts/validate_exp06.py compiles |
| `PY-COMPILE-033` | python | **PASS** | scripts/validate_tt00.py compiles |
| `PY-COMPILE-034` | python | **PASS** | scripts/validate_tt01.py compiles |
| `PY-COMPILE-035` | python | **PASS** | scripts/validate_tt02.py compiles |
| `PY-COMPILE-036` | python | **PASS** | scripts/verify_exp03_rebuild.py compiles |
| `PY-COMPILE-037` | python | **PASS** | scripts/verify_exp04_rebuild.py compiles |
| `PY-COMPILE-038` | python | **PASS** | scripts/verify_exp05_rebuild.py compiles |
| `PY-COMPILE-039` | python | **PASS** | scripts/verify_exp06_rebuild.py compiles |
| `PY-COMPILE-040` | python | **PASS** | scripts/verify_tt00_rebuild.py compiles |
| `PY-COMPILE-041` | python | **PASS** | scripts/verify_tt01_rebuild.py compiles |
| `PY-COMPILE-042` | python | **PASS** | scripts/verify_tt02_rebuild.py compiles |
| `PY-COMPILE-043` | python | **PASS** | src/cst_tt/__init__.py compiles |
| `PY-COMPILE-044` | python | **PASS** | src/cst_tt/ancestry.py compiles |
| `PY-COMPILE-045` | python | **PASS** | src/cst_tt/autonomy.py compiles |
| `PY-COMPILE-046` | python | **PASS** | src/cst_tt/circularity.py compiles |
| `PY-COMPILE-047` | python | **PASS** | src/cst_tt/contracts.py compiles |
| `PY-COMPILE-048` | python | **PASS** | src/cst_tt/corridor.py compiles |
| `PY-COMPILE-049` | python | **PASS** | src/cst_tt/countermodels.py compiles |
| `PY-COMPILE-050` | python | **PASS** | src/cst_tt/hashing.py compiles |
| `PY-COMPILE-051` | python | **PASS** | src/cst_tt/package.py compiles |
| `PY-COMPILE-052` | python | **PASS** | src/cst_tt/package_auditor.py compiles |
| `PY-COMPILE-053` | python | **PASS** | src/cst_tt/package_gluing.py compiles |
| `PY-COMPILE-054` | python | **PASS** | src/cst_tt/predicates.py compiles |
| `PY-COMPILE-055` | python | **PASS** | src/cst_tt/registry.py compiles |
| `PY-COMPILE-056` | python | **PASS** | src/cst_tt/targets.py compiles |
| `PY-COMPILE-057` | python | **PASS** | src/cst_tt/temporal.py compiles |
| `PY-COMPILE-058` | python | **PASS** | src/cst_tt/types.py compiles |
| `PY-TESTS` | python | **PASS** | full pytest suite passes |
| `PROV-001` | provenance | **PASS** | input checksum ledger retains the four frozen base inputs (4) |
| `PROV-HASH-001` | provenance | **PASS** | input checksum row 1 resolves and matches |
| `PROV-HASH-002` | provenance | **PASS** | input checksum row 2 resolves and matches |
| `PROV-HASH-003` | provenance | **PASS** | input checksum row 3 resolves and matches |
| `PROV-HASH-004` | provenance | **PASS** | input checksum row 4 resolves and matches |
| `PROV-TEMP-COUNT` | provenance | **PASS** | nine temporal-audit source manuscripts are retained |
| `PROV-TEMP-01` | provenance | **PASS** | Tsiokos_2026_An_Audited_Closure_Architecture_for_Consciousness_Exact_Finite_Models_Structural_Theorems_and_Conditional_Realization.tex is nonempty source provenance |
| `PROV-TEMP-02` | provenance | **PASS** | Tsiokos_2026_Glass_Is_an_Unclosed_Layer_Kovacs_Memory_as_Predictive_Quotient_Residue.tex is nonempty source provenance |
| `PROV-TEMP-03` | provenance | **PASS** | Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex is nonempty source provenance |
| `PROV-TEMP-04` | provenance | **PASS** | Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex is nonempty source provenance |
| `PROV-TEMP-05` | provenance | **PASS** | Tsiokos_2026_Six_Birds_Foundations_VI_A_Catalog_of_Dynamical_Structural_Laws.tex is nonempty source provenance |
| `PROV-TEMP-06` | provenance | **PASS** | Tsiokos_2026_Six_Birds_Protocol_Trap_Holonomy_Without_Entropy_Production.tex is nonempty source provenance |
| `PROV-TEMP-07` | provenance | **PASS** | Tsiokos_2026_To_Flatten_a_Stone_with_Six_Birds_Critical_Pairs_Holonomy_and_Confluence_in_Rewriting_Systems.tex is nonempty source provenance |
| `PROV-TEMP-08` | provenance | **PASS** | Tsiokos_2026_To_Lay_a_Stone_with_Six_Birds_Finite_State_Semantics_for_Packaging_Directionality_and_Coarse_Graining.tex is nonempty source provenance |
| `PROV-TEMP-09` | provenance | **PASS** | Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex is nonempty source provenance |
| `PROV-NORM-TEMPORAL_TRANSCE` | provenance | **PASS** | inputs/normative/cst-tt-00/TEMPORAL_TRANSCENDENCE_AUDIT.md is retained |
| `PROV-NORM-EXECUTION_PLAN` | provenance | **PASS** | inputs/normative/cst-tt-00/EXECUTION_PLAN.md is retained |
| `PROV-NORM-FIACH_BASELINE_S` | provenance | **PASS** | inputs/normative/cst-tt-00/FIACH_BASELINE_SPECIFICATION.md is retained |
| `PROV-NORM-IAPS_BASELINE_SP` | provenance | **PASS** | inputs/normative/cst-tt-00/IAPS_BASELINE_SPECIFICATION.md is retained |
| `PKG-COUNT` | package | **PASS** | exactly two positive package witnesses are registered |
| `PKG-01-MODEL` | package | **PASS** | PKG-POS-01-TARGET model exists |
| `PKG-01-CERT` | package | **PASS** | PKG-POS-01-TARGET certificate exists |
| `PKG-01-01` | package | **PASS** | PKG-POS-01-TARGET passes integrated |
| `PKG-01-02` | package | **PASS** | PKG-POS-01-TARGET passes coverage |
| `PKG-01-03` | package | **PASS** | PKG-POS-01-TARGET passes locals |
| `PKG-01-04` | package | **PASS** | PKG-POS-01-TARGET passes gates |
| `PKG-01-05` | package | **PASS** | PKG-POS-01-TARGET passes tree |
| `PKG-01-06` | package | **PASS** | PKG-POS-01-TARGET passes running |
| `PKG-01-07` | package | **PASS** | PKG-POS-01-TARGET passes edges |
| `PKG-01-08` | package | **PASS** | PKG-POS-01-TARGET passes global |
| `PKG-01-09` | package | **PASS** | PKG-POS-01-TARGET passes temporal |
| `PKG-01-10` | package | **PASS** | PKG-POS-01-TARGET passes ownership |
| `PKG-01-11` | package | **PASS** | PKG-POS-01-TARGET passes separation |
| `PKG-01-12` | package | **PASS** | PKG-POS-01-TARGET passes no-failures |
| `PKG-01-13` | package | **PASS** | PKG-POS-01-TARGET passes eight-clauses |
| `PKG-01-14` | package | **PASS** | PKG-POS-01-TARGET passes forty-four-coordinates |
| `PKG-01-HASH` | package | **PASS** | PKG-POS-01-TARGET model hash is bound in registry and certificate |
| `PKG-01-AUDIT` | package | **PASS** | PKG-POS-01-TARGET stored audit equals independent recomputation |
| `PKG-01-SCHEMA` | package | **PASS** | PKG-POS-01-TARGET certificate validates |
| `PKG-01-LANE` | package | **PASS** | PKG-POS-01-TARGET is typed only as S-R |
| `PKG-02-MODEL` | package | **PASS** | PKG-POS-02-SOURCE model exists |
| `PKG-02-CERT` | package | **PASS** | PKG-POS-02-SOURCE certificate exists |
| `PKG-02-01` | package | **PASS** | PKG-POS-02-SOURCE passes integrated |
| `PKG-02-02` | package | **PASS** | PKG-POS-02-SOURCE passes coverage |
| `PKG-02-03` | package | **PASS** | PKG-POS-02-SOURCE passes locals |
| `PKG-02-04` | package | **PASS** | PKG-POS-02-SOURCE passes gates |
| `PKG-02-05` | package | **PASS** | PKG-POS-02-SOURCE passes tree |
| `PKG-02-06` | package | **PASS** | PKG-POS-02-SOURCE passes running |
| `PKG-02-07` | package | **PASS** | PKG-POS-02-SOURCE passes edges |
| `PKG-02-08` | package | **PASS** | PKG-POS-02-SOURCE passes global |
| `PKG-02-09` | package | **PASS** | PKG-POS-02-SOURCE passes temporal |
| `PKG-02-10` | package | **PASS** | PKG-POS-02-SOURCE passes ownership |
| `PKG-02-11` | package | **PASS** | PKG-POS-02-SOURCE passes separation |
| `PKG-02-12` | package | **PASS** | PKG-POS-02-SOURCE passes no-failures |
| `PKG-02-13` | package | **PASS** | PKG-POS-02-SOURCE passes eight-clauses |
| `PKG-02-14` | package | **PASS** | PKG-POS-02-SOURCE passes forty-four-coordinates |
| `PKG-02-HASH` | package | **PASS** | PKG-POS-02-SOURCE model hash is bound in registry and certificate |
| `PKG-02-AUDIT` | package | **PASS** | PKG-POS-02-SOURCE stored audit equals independent recomputation |
| `PKG-02-SCHEMA` | package | **PASS** | PKG-POS-02-SOURCE certificate validates |
| `PKG-02-LANE` | package | **PASS** | PKG-POS-02-SOURCE is typed only as S-R |
| `PKG-DISTINCT` | package | **PASS** | source and target package carrier codes are distinct |
| `C6-01` | temporal-C6 | **PASS** | C6 satisfies future_sufficient |
| `C6-02` | temporal-C6 | **PASS** | C6 satisfies order_stable |
| `C6-03` | temporal-C6 | **PASS** | C6 satisfies successor_available |
| `C6-04` | temporal-C6 | **PASS** | C6 satisfies viable_tick |
| `C6-05` | temporal-C6 | **PASS** | C6 satisfies genuine_progress |
| `C6-06` | temporal-C6 | **PASS** | C6 satisfies endogenous_arrow |
| `C6-07` | temporal-C6 | **PASS** | C6 satisfies record_descends |
| `C6-08` | temporal-C6 | **PASS** | C6 satisfies route_residue_retained |
| `C6-09` | temporal-C6 | **PASS** | C6 satisfies no_external_scheduler |
| `C6-10` | temporal-C6 | **PASS** | C6 satisfies temporal_owner_matches |
| `C6-11` | temporal-C6 | **PASS** | C6 satisfies maintenance_owner_matches |
| `STG-01` | staged-assembly | **PASS** | staged assembly satisfies source_package_valid |
| `STG-02` | staged-assembly | **PASS** | staged assembly satisfies target_package_valid |
| `STG-03` | staged-assembly | **PASS** | staged assembly satisfies carriers_distinct |
| `STG-04` | staged-assembly | **PASS** | staged assembly satisfies exactly_eight_clause_maps |
| `STG-05` | staged-assembly | **PASS** | staged assembly satisfies maps_separately_typed |
| `STG-06` | staged-assembly | **PASS** | staged assembly satisfies coordinate_maps_total |
| `STG-07` | staged-assembly | **PASS** | staged assembly satisfies value_maps_sound |
| `STG-08` | staged-assembly | **PASS** | staged assembly satisfies hard_gates_never_averaged |
| `STG-09` | staged-assembly | **PASS** | staged assembly satisfies target_global_assembled |
| `STG-10` | staged-assembly | **PASS** | staged assembly satisfies forbidden_verdict_fields_absent |
| `STG-11` | staged-assembly | **PASS** | staged assembly satisfies staged_assembly_valid |
| `STG-FAILURES` | staged-assembly | **PASS** | positive staged assembly has no failed obligations |
| `STG-AUDIT` | staged-assembly | **PASS** | stored staged audit equals independent recomputation |
| `STG-HASH-1` | staged-assembly | **PASS** | staged certificate binds assembly hash |
| `STG-HASH-2` | staged-assembly | **PASS** | staged certificate binds source model hash |
| `STG-HASH-3` | staged-assembly | **PASS** | staged certificate binds target model hash |
| `STG-SCHEMA` | staged-assembly | **PASS** | staged certificate validates |
| `STG-LANES` | staged-assembly | **PASS** | staged assembly is typed only as S-T and S-R |
| `CTRL-COUNT` | controls | **PASS** | seventeen package controls and one staged control are registered |
| `CTRL-01-ART` | controls | **PASS** | PC-01 artifact exists |
| `CTRL-01-CERT` | controls | **PASS** | PC-01 certificate exists |
| `CTRL-01-REJECT` | controls | **PASS** | PC-01 is rejected by its checker |
| `CTRL-01-PRIMARY` | controls | **PASS** | PC-01 exposes its registered primary failure |
| `CTRL-01-EXACT` | controls | **PASS** | PC-01 failure set equals registry |
| `CTRL-01-STORED` | controls | **PASS** | PC-01 certificate stores recomputed failures |
| `CTRL-01-HASH` | controls | **PASS** | PC-01 certificate binds exact artifact |
| `CTRL-01-SCHEMA` | controls | **PASS** | PC-01 certificate validates |
| `CTRL-02-ART` | controls | **PASS** | PC-02 artifact exists |
| `CTRL-02-CERT` | controls | **PASS** | PC-02 certificate exists |
| `CTRL-02-REJECT` | controls | **PASS** | PC-02 is rejected by its checker |
| `CTRL-02-PRIMARY` | controls | **PASS** | PC-02 exposes its registered primary failure |
| `CTRL-02-EXACT` | controls | **PASS** | PC-02 failure set equals registry |
| `CTRL-02-STORED` | controls | **PASS** | PC-02 certificate stores recomputed failures |
| `CTRL-02-HASH` | controls | **PASS** | PC-02 certificate binds exact artifact |
| `CTRL-02-SCHEMA` | controls | **PASS** | PC-02 certificate validates |
| `CTRL-03-ART` | controls | **PASS** | PC-03 artifact exists |
| `CTRL-03-CERT` | controls | **PASS** | PC-03 certificate exists |
| `CTRL-03-REJECT` | controls | **PASS** | PC-03 is rejected by its checker |
| `CTRL-03-PRIMARY` | controls | **PASS** | PC-03 exposes its registered primary failure |
| `CTRL-03-EXACT` | controls | **PASS** | PC-03 failure set equals registry |
| `CTRL-03-STORED` | controls | **PASS** | PC-03 certificate stores recomputed failures |
| `CTRL-03-HASH` | controls | **PASS** | PC-03 certificate binds exact artifact |
| `CTRL-03-SCHEMA` | controls | **PASS** | PC-03 certificate validates |
| `CTRL-04-ART` | controls | **PASS** | PC-04 artifact exists |
| `CTRL-04-CERT` | controls | **PASS** | PC-04 certificate exists |
| `CTRL-04-REJECT` | controls | **PASS** | PC-04 is rejected by its checker |
| `CTRL-04-PRIMARY` | controls | **PASS** | PC-04 exposes its registered primary failure |
| `CTRL-04-EXACT` | controls | **PASS** | PC-04 failure set equals registry |
| `CTRL-04-STORED` | controls | **PASS** | PC-04 certificate stores recomputed failures |
| `CTRL-04-HASH` | controls | **PASS** | PC-04 certificate binds exact artifact |
| `CTRL-04-SCHEMA` | controls | **PASS** | PC-04 certificate validates |
| `CTRL-05-ART` | controls | **PASS** | PC-05 artifact exists |
| `CTRL-05-CERT` | controls | **PASS** | PC-05 certificate exists |
| `CTRL-05-REJECT` | controls | **PASS** | PC-05 is rejected by its checker |
| `CTRL-05-PRIMARY` | controls | **PASS** | PC-05 exposes its registered primary failure |
| `CTRL-05-EXACT` | controls | **PASS** | PC-05 failure set equals registry |
| `CTRL-05-STORED` | controls | **PASS** | PC-05 certificate stores recomputed failures |
| `CTRL-05-HASH` | controls | **PASS** | PC-05 certificate binds exact artifact |
| `CTRL-05-SCHEMA` | controls | **PASS** | PC-05 certificate validates |
| `CTRL-06-ART` | controls | **PASS** | PC-06 artifact exists |
| `CTRL-06-CERT` | controls | **PASS** | PC-06 certificate exists |
| `CTRL-06-REJECT` | controls | **PASS** | PC-06 is rejected by its checker |
| `CTRL-06-PRIMARY` | controls | **PASS** | PC-06 exposes its registered primary failure |
| `CTRL-06-EXACT` | controls | **PASS** | PC-06 failure set equals registry |
| `CTRL-06-STORED` | controls | **PASS** | PC-06 certificate stores recomputed failures |
| `CTRL-06-HASH` | controls | **PASS** | PC-06 certificate binds exact artifact |
| `CTRL-06-SCHEMA` | controls | **PASS** | PC-06 certificate validates |
| `CTRL-07-ART` | controls | **PASS** | PC-07 artifact exists |
| `CTRL-07-CERT` | controls | **PASS** | PC-07 certificate exists |
| `CTRL-07-REJECT` | controls | **PASS** | PC-07 is rejected by its checker |
| `CTRL-07-PRIMARY` | controls | **PASS** | PC-07 exposes its registered primary failure |
| `CTRL-07-EXACT` | controls | **PASS** | PC-07 failure set equals registry |
| `CTRL-07-STORED` | controls | **PASS** | PC-07 certificate stores recomputed failures |
| `CTRL-07-HASH` | controls | **PASS** | PC-07 certificate binds exact artifact |
| `CTRL-07-SCHEMA` | controls | **PASS** | PC-07 certificate validates |
| `CTRL-08-ART` | controls | **PASS** | PC-08 artifact exists |
| `CTRL-08-CERT` | controls | **PASS** | PC-08 certificate exists |
| `CTRL-08-REJECT` | controls | **PASS** | PC-08 is rejected by its checker |
| `CTRL-08-PRIMARY` | controls | **PASS** | PC-08 exposes its registered primary failure |
| `CTRL-08-EXACT` | controls | **PASS** | PC-08 failure set equals registry |
| `CTRL-08-STORED` | controls | **PASS** | PC-08 certificate stores recomputed failures |
| `CTRL-08-HASH` | controls | **PASS** | PC-08 certificate binds exact artifact |
| `CTRL-08-SCHEMA` | controls | **PASS** | PC-08 certificate validates |
| `CTRL-09-ART` | controls | **PASS** | PC-09 artifact exists |
| `CTRL-09-CERT` | controls | **PASS** | PC-09 certificate exists |
| `CTRL-09-REJECT` | controls | **PASS** | PC-09 is rejected by its checker |
| `CTRL-09-PRIMARY` | controls | **PASS** | PC-09 exposes its registered primary failure |
| `CTRL-09-EXACT` | controls | **PASS** | PC-09 failure set equals registry |
| `CTRL-09-STORED` | controls | **PASS** | PC-09 certificate stores recomputed failures |
| `CTRL-09-HASH` | controls | **PASS** | PC-09 certificate binds exact artifact |
| `CTRL-09-SCHEMA` | controls | **PASS** | PC-09 certificate validates |
| `CTRL-10-ART` | controls | **PASS** | PC-10 artifact exists |
| `CTRL-10-CERT` | controls | **PASS** | PC-10 certificate exists |
| `CTRL-10-REJECT` | controls | **PASS** | PC-10 is rejected by its checker |
| `CTRL-10-PRIMARY` | controls | **PASS** | PC-10 exposes its registered primary failure |
| `CTRL-10-EXACT` | controls | **PASS** | PC-10 failure set equals registry |
| `CTRL-10-STORED` | controls | **PASS** | PC-10 certificate stores recomputed failures |
| `CTRL-10-HASH` | controls | **PASS** | PC-10 certificate binds exact artifact |
| `CTRL-10-SCHEMA` | controls | **PASS** | PC-10 certificate validates |
| `CTRL-11-ART` | controls | **PASS** | PC-11 artifact exists |
| `CTRL-11-CERT` | controls | **PASS** | PC-11 certificate exists |
| `CTRL-11-REJECT` | controls | **PASS** | PC-11 is rejected by its checker |
| `CTRL-11-PRIMARY` | controls | **PASS** | PC-11 exposes its registered primary failure |
| `CTRL-11-EXACT` | controls | **PASS** | PC-11 failure set equals registry |
| `CTRL-11-STORED` | controls | **PASS** | PC-11 certificate stores recomputed failures |
| `CTRL-11-HASH` | controls | **PASS** | PC-11 certificate binds exact artifact |
| `CTRL-11-SCHEMA` | controls | **PASS** | PC-11 certificate validates |
| `CTRL-12-ART` | controls | **PASS** | PC-12 artifact exists |
| `CTRL-12-CERT` | controls | **PASS** | PC-12 certificate exists |
| `CTRL-12-REJECT` | controls | **PASS** | PC-12 is rejected by its checker |
| `CTRL-12-PRIMARY` | controls | **PASS** | PC-12 exposes its registered primary failure |
| `CTRL-12-EXACT` | controls | **PASS** | PC-12 failure set equals registry |
| `CTRL-12-STORED` | controls | **PASS** | PC-12 certificate stores recomputed failures |
| `CTRL-12-HASH` | controls | **PASS** | PC-12 certificate binds exact artifact |
| `CTRL-12-SCHEMA` | controls | **PASS** | PC-12 certificate validates |
| `CTRL-13-ART` | controls | **PASS** | PC-13 artifact exists |
| `CTRL-13-CERT` | controls | **PASS** | PC-13 certificate exists |
| `CTRL-13-REJECT` | controls | **PASS** | PC-13 is rejected by its checker |
| `CTRL-13-PRIMARY` | controls | **PASS** | PC-13 exposes its registered primary failure |
| `CTRL-13-EXACT` | controls | **PASS** | PC-13 failure set equals registry |
| `CTRL-13-STORED` | controls | **PASS** | PC-13 certificate stores recomputed failures |
| `CTRL-13-HASH` | controls | **PASS** | PC-13 certificate binds exact artifact |
| `CTRL-13-SCHEMA` | controls | **PASS** | PC-13 certificate validates |
| `CTRL-14-ART` | controls | **PASS** | PC-14 artifact exists |
| `CTRL-14-CERT` | controls | **PASS** | PC-14 certificate exists |
| `CTRL-14-REJECT` | controls | **PASS** | PC-14 is rejected by its checker |
| `CTRL-14-PRIMARY` | controls | **PASS** | PC-14 exposes its registered primary failure |
| `CTRL-14-EXACT` | controls | **PASS** | PC-14 failure set equals registry |
| `CTRL-14-STORED` | controls | **PASS** | PC-14 certificate stores recomputed failures |
| `CTRL-14-HASH` | controls | **PASS** | PC-14 certificate binds exact artifact |
| `CTRL-14-SCHEMA` | controls | **PASS** | PC-14 certificate validates |
| `CTRL-15-ART` | controls | **PASS** | PC-15 artifact exists |
| `CTRL-15-CERT` | controls | **PASS** | PC-15 certificate exists |
| `CTRL-15-REJECT` | controls | **PASS** | PC-15 is rejected by its checker |
| `CTRL-15-PRIMARY` | controls | **PASS** | PC-15 exposes its registered primary failure |
| `CTRL-15-EXACT` | controls | **PASS** | PC-15 failure set equals registry |
| `CTRL-15-STORED` | controls | **PASS** | PC-15 certificate stores recomputed failures |
| `CTRL-15-HASH` | controls | **PASS** | PC-15 certificate binds exact artifact |
| `CTRL-15-SCHEMA` | controls | **PASS** | PC-15 certificate validates |
| `CTRL-16-ART` | controls | **PASS** | PC-16 artifact exists |
| `CTRL-16-CERT` | controls | **PASS** | PC-16 certificate exists |
| `CTRL-16-REJECT` | controls | **PASS** | PC-16 is rejected by its checker |
| `CTRL-16-PRIMARY` | controls | **PASS** | PC-16 exposes its registered primary failure |
| `CTRL-16-EXACT` | controls | **PASS** | PC-16 failure set equals registry |
| `CTRL-16-STORED` | controls | **PASS** | PC-16 certificate stores recomputed failures |
| `CTRL-16-HASH` | controls | **PASS** | PC-16 certificate binds exact artifact |
| `CTRL-16-SCHEMA` | controls | **PASS** | PC-16 certificate validates |
| `CTRL-17-ART` | controls | **PASS** | PC-17 artifact exists |
| `CTRL-17-CERT` | controls | **PASS** | PC-17 certificate exists |
| `CTRL-17-REJECT` | controls | **PASS** | PC-17 is rejected by its checker |
| `CTRL-17-PRIMARY` | controls | **PASS** | PC-17 exposes its registered primary failure |
| `CTRL-17-EXACT` | controls | **PASS** | PC-17 failure set equals registry |
| `CTRL-17-STORED` | controls | **PASS** | PC-17 certificate stores recomputed failures |
| `CTRL-17-HASH` | controls | **PASS** | PC-17 certificate binds exact artifact |
| `CTRL-17-SCHEMA` | controls | **PASS** | PC-17 certificate validates |
| `CTRL-18-ART` | controls | **PASS** | SC-01 artifact exists |
| `CTRL-18-CERT` | controls | **PASS** | SC-01 certificate exists |
| `CTRL-18-REJECT` | controls | **PASS** | SC-01 is rejected by its checker |
| `CTRL-18-PRIMARY` | controls | **PASS** | SC-01 exposes its registered primary failure |
| `CTRL-18-EXACT` | controls | **PASS** | SC-01 failure set equals registry |
| `CTRL-18-STORED` | controls | **PASS** | SC-01 certificate stores recomputed failures |
| `CTRL-18-HASH` | controls | **PASS** | SC-01 certificate binds exact artifact |
| `CTRL-18-SCHEMA` | controls | **PASS** | SC-01 certificate validates |
| `EXH-001` | bounded-exhaustion | **PASS** | stored exhaustion certificate equals independent rerun |
| `EXH-002` | bounded-exhaustion | **PASS** | 1,025,416 bounded candidates were examined |
| `EXH-003` | bounded-exhaustion | **PASS** | 18,972 cases satisfy running-intersection and edge-compatibility premises |
| `EXH-004` | bounded-exhaustion | **PASS** | every premise-satisfying case glued |
| `EXH-005` | bounded-exhaustion | **PASS** | bounded search found no violation |
| `EXH-006` | bounded-exhaustion | **PASS** | bounded checker reports PASS |
| `EXH-007` | bounded-exhaustion | **PASS** | five path/star configurations are covered |
| `EXH-CFG-01` | bounded-exhaustion | **PASS** | configuration path-2 has no gluing failure |
| `EXH-CFG-02` | bounded-exhaustion | **PASS** | configuration path-3 has no gluing failure |
| `EXH-CFG-03` | bounded-exhaustion | **PASS** | configuration star-3 has no gluing failure |
| `EXH-CFG-04` | bounded-exhaustion | **PASS** | configuration path-4 has no gluing failure |
| `EXH-CFG-05` | bounded-exhaustion | **PASS** | configuration star-4 has no gluing failure |
| `REG-001` | registries | **PASS** | theorem registry retains 35 theorem/no-go surfaces |
| `REG-002` | registries | **PASS** | toy registry has 23 entries |
| `REG-003` | registries | **PASS** | definition registry has 45 entries |
| `REG-004` | registries | **PASS** | certificate schema registry has 10 entries |
| `REG-005` | registries | **PASS** | package obligation registry has 10 entries |
| `REG-006` | registries | **PASS** | staged obligation registry has 10 entries |
| `REG-UNIQUE-1` | registries | **PASS** | theorem_id values are unique |
| `REG-UNIQUE-2` | registries | **PASS** | toy_id values are unique |
| `REG-UNIQUE-3` | registries | **PASS** | definition_id values are unique |
| `REG-UNIQUE-4` | registries | **PASS** | schema_id values are unique |
| `REG-THM-STATUS-1` | registries | **PASS** | theorem status distribution is frozen |
| `REG-TTH-01-STATUS` | registries | **PASS** | TTH-01 has the landed proof-source status |
| `REG-TTH-01-LEAN` | registries | **PASS** | TTH-01 points to its package proof source |
| `REG-TTH-02-STATUS` | registries | **PASS** | TTH-02 has the landed proof-source status |
| `REG-TTH-02-LEAN` | registries | **PASS** | TTH-02 points to its package proof source |
| `REG-PKG-LANES` | registries | **PASS** | all package obligations are S-R only |
| `REG-STG-LANES` | registries | **PASS** | all staged obligations are exactly S-T and S-R |
| `REG-PKG-OB-01` | registries | **PASS** | package obligation 1 is ordered and has positive witnesses |
| `REG-PKG-NEG-01` | registries | **PASS** | package obligation 1 has at least one exact negative control |
| `REG-PKG-OB-02` | registries | **PASS** | package obligation 2 is ordered and has positive witnesses |
| `REG-PKG-NEG-02` | registries | **PASS** | package obligation 2 has at least one exact negative control |
| `REG-PKG-OB-03` | registries | **PASS** | package obligation 3 is ordered and has positive witnesses |
| `REG-PKG-NEG-03` | registries | **PASS** | package obligation 3 has at least one exact negative control |
| `REG-PKG-OB-04` | registries | **PASS** | package obligation 4 is ordered and has positive witnesses |
| `REG-PKG-NEG-04` | registries | **PASS** | package obligation 4 has at least one exact negative control |
| `REG-PKG-OB-05` | registries | **PASS** | package obligation 5 is ordered and has positive witnesses |
| `REG-PKG-NEG-05` | registries | **PASS** | package obligation 5 has at least one exact negative control |
| `REG-PKG-OB-06` | registries | **PASS** | package obligation 6 is ordered and has positive witnesses |
| `REG-PKG-NEG-06` | registries | **PASS** | package obligation 6 has at least one exact negative control |
| `REG-PKG-OB-07` | registries | **PASS** | package obligation 7 is ordered and has positive witnesses |
| `REG-PKG-NEG-07` | registries | **PASS** | package obligation 7 has at least one exact negative control |
| `REG-PKG-OB-08` | registries | **PASS** | package obligation 8 is ordered and has positive witnesses |
| `REG-PKG-NEG-08` | registries | **PASS** | package obligation 8 has at least one exact negative control |
| `REG-PKG-OB-09` | registries | **PASS** | package obligation 9 is ordered and has positive witnesses |
| `REG-PKG-NEG-09` | registries | **PASS** | package obligation 9 has at least one exact negative control |
| `REG-PKG-OB-10` | registries | **PASS** | package obligation 10 is ordered and has positive witnesses |
| `REG-PKG-NEG-10` | registries | **PASS** | package obligation 10 has at least one exact negative control |
| `REG-STG-OB-01` | registries | **PASS** | staged obligation 1 is ordered and has the positive assembly |
| `REG-STG-OB-02` | registries | **PASS** | staged obligation 2 is ordered and has the positive assembly |
| `REG-STG-OB-03` | registries | **PASS** | staged obligation 3 is ordered and has the positive assembly |
| `REG-STG-OB-04` | registries | **PASS** | staged obligation 4 is ordered and has the positive assembly |
| `REG-STG-OB-05` | registries | **PASS** | staged obligation 5 is ordered and has the positive assembly |
| `REG-STG-OB-06` | registries | **PASS** | staged obligation 6 is ordered and has the positive assembly |
| `REG-STG-OB-07` | registries | **PASS** | staged obligation 7 is ordered and has the positive assembly |
| `REG-STG-OB-08` | registries | **PASS** | staged obligation 8 is ordered and has the positive assembly |
| `REG-STG-OB-09` | registries | **PASS** | staged obligation 9 is ordered and has the positive assembly |
| `REG-STG-OB-10` | registries | **PASS** | staged obligation 10 is ordered and has the positive assembly |
| `REG-PROJ-01` | registries | **PASS** | project registry freezes phase='CST-TT-02' |
| `REG-PROJ-02` | registries | **PASS** | project registry freezes phase_base_tag='CST-TT-01-v1' |
| `REG-PROJ-03` | registries | **PASS** | project registry freezes phase_base_commit='488db50b20d6d9c67493de3e9fd758e6e9e205ce' |
| `REG-PROJ-04` | registries | **PASS** | project registry freezes generic_theorem_proof_sources_landed=2 |
| `REG-PROJ-05` | registries | **PASS** | project registry freezes generic_theorems_lean_compiled=0 |
| `REG-PROJ-06` | registries | **PASS** | project registry freezes checked_finite_package_witnesses=2 |
| `REG-PROJ-07` | registries | **PASS** | project registry freezes checked_staged_package_assemblies=1 |
| `REG-PROJ-08` | registries | **PASS** | project registry freezes checked_package_obligation_controls=18 |
| `REG-PROJ-09` | registries | **PASS** | project registry freezes bounded_gluing_candidates=1025416 |
| `REG-PROJ-10` | registries | **PASS** | project registry freezes bounded_gluing_premise_cases=18972 |
| `REG-PROJ-11` | registries | **PASS** | project registry freezes positive_handoff_witnesses=0 |
| `REG-PROJ-12` | registries | **PASS** | project registry freezes fallback_unlocked=False |
| `REG-PROJ-13` | registries | **PASS** | project registry freezes next_phase='CST-TT-03' |
| `REG-SUMMARY` | registries | **PASS** | phase summary retains primary route and locks fallback |
| `REG-K-PKG-01` | registries | **PASS** | K-PKG-01 is not triggered |
| `REG-K-PKG-02` | registries | **PASS** | K-PKG-02 is not triggered |
| `SCHEMA-01-FILE` | schemas | **PASS** | schema CS-01 exists |
| `SCHEMA-01-EXAMPLE` | schemas | **PASS** | schema CS-01 example exists |
| `SCHEMA-01-VALID` | schemas | **PASS** | schema CS-01 accepts its scaffold |
| `SCHEMA-02-FILE` | schemas | **PASS** | schema CS-02 exists |
| `SCHEMA-02-EXAMPLE` | schemas | **PASS** | schema CS-02 example exists |
| `SCHEMA-02-VALID` | schemas | **PASS** | schema CS-02 accepts its scaffold |
| `SCHEMA-03-FILE` | schemas | **PASS** | schema CS-03 exists |
| `SCHEMA-03-EXAMPLE` | schemas | **PASS** | schema CS-03 example exists |
| `SCHEMA-03-VALID` | schemas | **PASS** | schema CS-03 accepts its scaffold |
| `SCHEMA-04-FILE` | schemas | **PASS** | schema CS-04 exists |
| `SCHEMA-04-EXAMPLE` | schemas | **PASS** | schema CS-04 example exists |
| `SCHEMA-04-VALID` | schemas | **PASS** | schema CS-04 accepts its scaffold |
| `SCHEMA-05-FILE` | schemas | **PASS** | schema CS-05 exists |
| `SCHEMA-05-EXAMPLE` | schemas | **PASS** | schema CS-05 example exists |
| `SCHEMA-05-VALID` | schemas | **PASS** | schema CS-05 accepts its scaffold |
| `SCHEMA-06-FILE` | schemas | **PASS** | schema CS-06 exists |
| `SCHEMA-06-EXAMPLE` | schemas | **PASS** | schema CS-06 example exists |
| `SCHEMA-06-VALID` | schemas | **PASS** | schema CS-06 accepts its scaffold |
| `SCHEMA-07-FILE` | schemas | **PASS** | schema CS-07 exists |
| `SCHEMA-07-EXAMPLE` | schemas | **PASS** | schema CS-07 example exists |
| `SCHEMA-07-VALID` | schemas | **PASS** | schema CS-07 accepts its scaffold |
| `SCHEMA-08-FILE` | schemas | **PASS** | schema CS-08 exists |
| `SCHEMA-08-EXAMPLE` | schemas | **PASS** | schema CS-08 example exists |
| `SCHEMA-08-VALID` | schemas | **PASS** | schema CS-08 accepts its scaffold |
| `SCHEMA-09-FILE` | schemas | **PASS** | schema CS-09 exists |
| `SCHEMA-09-EXAMPLE` | schemas | **PASS** | schema CS-09 example exists |
| `SCHEMA-09-VALID` | schemas | **PASS** | schema CS-09 accepts its scaffold |
| `SCHEMA-10-FILE` | schemas | **PASS** | schema CS-10 exists |
| `SCHEMA-10-EXAMPLE` | schemas | **PASS** | schema CS-10 example exists |
| `SCHEMA-10-VALID` | schemas | **PASS** | schema CS-10 accepts its scaffold |
| `SCHEMA-THM-01` | schemas | **PASS** | theorem row TTH-01 validates against registry schema |
| `SCHEMA-THM-02` | schemas | **PASS** | theorem row TTH-02 validates against registry schema |
| `SCHEMA-THM-03` | schemas | **PASS** | theorem row TTH-03 validates against registry schema |
| `SCHEMA-THM-04` | schemas | **PASS** | theorem row TTH-04 validates against registry schema |
| `SCHEMA-THM-05` | schemas | **PASS** | theorem row TTH-05 validates against registry schema |
| `SCHEMA-THM-06` | schemas | **PASS** | theorem row TTH-06 validates against registry schema |
| `SCHEMA-THM-07` | schemas | **PASS** | theorem row TTH-07 validates against registry schema |
| `SCHEMA-THM-08` | schemas | **PASS** | theorem row TTH-08 validates against registry schema |
| `SCHEMA-THM-09` | schemas | **PASS** | theorem row TTH-09 validates against registry schema |
| `SCHEMA-THM-10` | schemas | **PASS** | theorem row TTH-10 validates against registry schema |
| `SCHEMA-THM-11` | schemas | **PASS** | theorem row TTN-01 validates against registry schema |
| `SCHEMA-THM-12` | schemas | **PASS** | theorem row TTN-02 validates against registry schema |
| `SCHEMA-THM-13` | schemas | **PASS** | theorem row TTN-03 validates against registry schema |
| `SCHEMA-THM-14` | schemas | **PASS** | theorem row TTN-04 validates against registry schema |
| `SCHEMA-THM-15` | schemas | **PASS** | theorem row TTN-05 validates against registry schema |
| `SCHEMA-THM-16` | schemas | **PASS** | theorem row TTN-06 validates against registry schema |
| `SCHEMA-THM-17` | schemas | **PASS** | theorem row TTN-07 validates against registry schema |
| `SCHEMA-THM-18` | schemas | **PASS** | theorem row TTN-08 validates against registry schema |
| `SCHEMA-THM-19` | schemas | **PASS** | theorem row TTN-09 validates against registry schema |
| `SCHEMA-THM-20` | schemas | **PASS** | theorem row TTN-10 validates against registry schema |
| `SCHEMA-THM-21` | schemas | **PASS** | theorem row TTN-11 validates against registry schema |
| `SCHEMA-THM-22` | schemas | **PASS** | theorem row TTN-12 validates against registry schema |
| `SCHEMA-THM-23` | schemas | **PASS** | theorem row TTN-13 validates against registry schema |
| `SCHEMA-THM-24` | schemas | **PASS** | theorem row TTN-14 validates against registry schema |
| `SCHEMA-THM-25` | schemas | **PASS** | theorem row TTD-01 validates against registry schema |
| `SCHEMA-THM-26` | schemas | **PASS** | theorem row TTD-02 validates against registry schema |
| `SCHEMA-THM-27` | schemas | **PASS** | theorem row TTD-03 validates against registry schema |
| `SCHEMA-THM-28` | schemas | **PASS** | theorem row TTF-01 validates against registry schema |
| `SCHEMA-THM-29` | schemas | **PASS** | theorem row TTF-02 validates against registry schema |
| `SCHEMA-THM-30` | schemas | **PASS** | theorem row TTF-03 validates against registry schema |
| `SCHEMA-THM-31` | schemas | **PASS** | theorem row TTF-04 validates against registry schema |
| `SCHEMA-THM-32` | schemas | **PASS** | theorem row TTF-05 validates against registry schema |
| `SCHEMA-THM-33` | schemas | **PASS** | theorem row TTF-06 validates against registry schema |
| `SCHEMA-THM-34` | schemas | **PASS** | theorem row TTF-07 validates against registry schema |
| `SCHEMA-THM-35` | schemas | **PASS** | theorem row TTF-08 validates against registry schema |
| `LEAN-001` | lean-static | **PASS** | at least seventeen Lean modules are present (18) |
| `LEAN-NOPLACE-001` | lean-static | **PASS** | CSTTT/Autonomy/System.lean has no proof placeholder command |
| `LEAN-DELIM-001` | lean-static | **PASS** | CSTTT/Autonomy/System.lean has balanced simple delimiters |
| `LEAN-NOPLACE-002` | lean-static | **PASS** | CSTTT/Core/Carrier.lean has no proof placeholder command |
| `LEAN-DELIM-002` | lean-static | **PASS** | CSTTT/Core/Carrier.lean has balanced simple delimiters |
| `LEAN-NOPLACE-003` | lean-static | **PASS** | CSTTT/Core/Episode.lean has no proof placeholder command |
| `LEAN-DELIM-003` | lean-static | **PASS** | CSTTT/Core/Episode.lean has balanced simple delimiters |
| `LEAN-NOPLACE-004` | lean-static | **PASS** | CSTTT/Core/Finite.lean has no proof placeholder command |
| `LEAN-DELIM-004` | lean-static | **PASS** | CSTTT/Core/Finite.lean has balanced simple delimiters |
| `LEAN-NOPLACE-005` | lean-static | **PASS** | CSTTT/Corridor/DirectSuccessor.lean has no proof placeholder command |
| `LEAN-DELIM-005` | lean-static | **PASS** | CSTTT/Corridor/DirectSuccessor.lean has balanced simple delimiters |
| `LEAN-NOPLACE-006` | lean-static | **PASS** | CSTTT/Corridor/TemporalCorridor.lean has no proof placeholder command |
| `LEAN-DELIM-006` | lean-static | **PASS** | CSTTT/Corridor/TemporalCorridor.lean has balanced simple delimiters |
| `LEAN-NOPLACE-007` | lean-static | **PASS** | CSTTT/Countermodels/Kernel.lean has no proof placeholder command |
| `LEAN-DELIM-007` | lean-static | **PASS** | CSTTT/Countermodels/Kernel.lean has balanced simple delimiters |
| `LEAN-NOPLACE-008` | lean-static | **PASS** | CSTTT/Fallback/Ancestry.lean has no proof placeholder command |
| `LEAN-DELIM-008` | lean-static | **PASS** | CSTTT/Fallback/Ancestry.lean has balanced simple delimiters |
| `LEAN-NOPLACE-009` | lean-static | **PASS** | CSTTT/Package/Clauses.lean has no proof placeholder command |
| `LEAN-DELIM-009` | lean-static | **PASS** | CSTTT/Package/Clauses.lean has balanced simple delimiters |
| `LEAN-NOPLACE-010` | lean-static | **PASS** | CSTTT/Package/FiniteGluing.lean has no proof placeholder command |
| `LEAN-DELIM-010` | lean-static | **PASS** | CSTTT/Package/FiniteGluing.lean has balanced simple delimiters |
| `LEAN-NOPLACE-011` | lean-static | **PASS** | CSTTT/Package/Gluing.lean has no proof placeholder command |
| `LEAN-DELIM-011` | lean-static | **PASS** | CSTTT/Package/Gluing.lean has balanced simple delimiters |
| `LEAN-NOPLACE-012` | lean-static | **PASS** | CSTTT/Package/TemporalPackage.lean has no proof placeholder command |
| `LEAN-DELIM-012` | lean-static | **PASS** | CSTTT/Package/TemporalPackage.lean has balanced simple delimiters |
| `LEAN-NOPLACE-013` | lean-static | **PASS** | CSTTT/Prospects/Statements.lean has no proof placeholder command |
| `LEAN-DELIM-013` | lean-static | **PASS** | CSTTT/Prospects/Statements.lean has balanced simple delimiters |
| `LEAN-NOPLACE-014` | lean-static | **PASS** | CSTTT/Targets/TemporalFIACH.lean has no proof placeholder command |
| `LEAN-DELIM-014` | lean-static | **PASS** | CSTTT/Targets/TemporalFIACH.lean has balanced simple delimiters |
| `LEAN-NOPLACE-015` | lean-static | **PASS** | CSTTT/Temporal/Clock.lean has no proof placeholder command |
| `LEAN-DELIM-015` | lean-static | **PASS** | CSTTT/Temporal/Clock.lean has balanced simple delimiters |
| `LEAN-NOPLACE-016` | lean-static | **PASS** | CSTTT/Temporal/Closure.lean has no proof placeholder command |
| `LEAN-DELIM-016` | lean-static | **PASS** | CSTTT/Temporal/Closure.lean has balanced simple delimiters |
| `LEAN-NOPLACE-017` | lean-static | **PASS** | CSTTT/Temporal/Signature.lean has no proof placeholder command |
| `LEAN-DELIM-017` | lean-static | **PASS** | CSTTT/Temporal/Signature.lean has balanced simple delimiters |
| `LEAN-NOPLACE-018` | lean-static | **PASS** | CSTTT/Transport/TemporalBridge.lean has no proof placeholder command |
| `LEAN-DELIM-018` | lean-static | **PASS** | CSTTT/Transport/TemporalBridge.lean has balanced simple delimiters |
| `LEAN-CIRCULARITY` | lean-static | **PASS** | primitive Lean tree passes forbidden-verdict vocabulary scan |
| `LEAN-GLUE-01` | lean-static | **PASS** | finite gluing source contains ScopedReach |
| `LEAN-GLUE-02` | lean-static | **PASS** | finite gluing source contains RootedJoinTree |
| `LEAN-GLUE-03` | lean-static | **PASS** | finite gluing source contains localEqualityAlongScopedReach |
| `LEAN-GLUE-04` | lean-static | **PASS** | finite gluing source contains gluedAssignment |
| `LEAN-GLUE-05` | lean-static | **PASS** | finite gluing source contains gluedAssignmentAgrees |
| `LEAN-GLUE-06` | lean-static | **PASS** | finite gluing source contains IntegratedPackageWitness |
| `LEAN-GLUE-07` | lean-static | **PASS** | finite gluing source contains acyclicLocalWitnessGluing |
| `LEAN-GLUE-08` | lean-static | **PASS** | finite gluing source contains StagedHeterogeneousEvidence |
| `LEAN-GLUE-09` | lean-static | **PASS** | finite gluing source contains stagedHeterogeneousPackageAssembly |
| `LEAN-TEMP-01` | lean-static | **PASS** | temporal package source contains TemporalSubstance |
| `LEAN-TEMP-02` | lean-static | **PASS** | temporal package source contains EightClauseIntegratedPackage |
| `LEAN-IMPORT-1` | lean-static | **PASS** | root module imports finite gluing |
| `LEAN-IMPORT-2` | lean-static | **PASS** | root module imports temporal package |
| `LEAN-LAYER-01` | lean-static | **PASS** | Clauses.lean does not import later corridor/autonomy/target layers |
| `LEAN-LAYER-02` | lean-static | **PASS** | FiniteGluing.lean does not import later corridor/autonomy/target layers |
| `LEAN-LAYER-03` | lean-static | **PASS** | Gluing.lean does not import later corridor/autonomy/target layers |
| `LEAN-LAYER-04` | lean-static | **PASS** | TemporalPackage.lean does not import later corridor/autonomy/target layers |
| `DOC-00-EXISTS` | documentation | **PASS** | docs/INTEGRATED_PACKAGE_SEMANTICS.md exists |
| `DOC-00-01` | documentation | **PASS** | docs/INTEGRATED_PACKAGE_SEMANTICS.md contains required phrase: finite structural target realization |
| `DOC-00-02` | documentation | **PASS** | docs/INTEGRATED_PACKAGE_SEMANTICS.md contains required phrase: eight separately audited clause slots |
| `DOC-00-03` | documentation | **PASS** | docs/INTEGRATED_PACKAGE_SEMANTICS.md contains required phrase: running intersection |
| `DOC-00-04` | documentation | **PASS** | docs/INTEGRATED_PACKAGE_SEMANTICS.md contains required phrase: None of these assets is a handoff or lineage witness |
| `DOC-01-EXISTS` | documentation | **PASS** | docs/ACYCLIC_GLUING_THEOREM.md exists |
| `DOC-01-01` | documentation | **PASS** | docs/ACYCLIC_GLUING_THEOREM.md contains required phrase: acyclicLocalWitnessGluing |
| `DOC-01-02` | documentation | **PASS** | docs/ACYCLIC_GLUING_THEOREM.md contains required phrase: running-intersection |
| `DOC-01-03` | documentation | **PASS** | docs/ACYCLIC_GLUING_THEOREM.md contains required phrase: Python is not a proof oracle |
| `DOC-01-04` | documentation | **PASS** | docs/ACYCLIC_GLUING_THEOREM.md contains required phrase: 1,025,416 |
| `DOC-02-EXISTS` | documentation | **PASS** | docs/C6_TEMPORAL_SUBSTANCE.md exists |
| `DOC-02-01` | documentation | **PASS** | docs/C6_TEMPORAL_SUBSTANCE.md contains required phrase: future sufficiency |
| `DOC-02-02` | documentation | **PASS** | docs/C6_TEMPORAL_SUBSTANCE.md contains required phrase: genuine progress |
| `DOC-02-03` | documentation | **PASS** | docs/C6_TEMPORAL_SUBSTANCE.md contains required phrase: endogenous arrow |
| `DOC-02-04` | documentation | **PASS** | docs/C6_TEMPORAL_SUBSTANCE.md contains required phrase: external scheduler |
| `DOC-02-05` | documentation | **PASS** | docs/C6_TEMPORAL_SUBSTANCE.md contains required phrase: does not entail any other C-clause |
| `DOC-03-EXISTS` | documentation | **PASS** | docs/STAGED_PACKAGE_ASSEMBLY.md exists |
| `DOC-03-01` | documentation | **PASS** | docs/STAGED_PACKAGE_ASSEMBLY.md contains required phrase: distinct carrier vocabularies |
| `DOC-03-02` | documentation | **PASS** | docs/STAGED_PACKAGE_ASSEMBLY.md contains required phrase: eight typed clause maps |
| `DOC-03-03` | documentation | **PASS** | docs/STAGED_PACKAGE_ASSEMBLY.md contains required phrase: does not establish temporal lineage |
| `DOC-04-EXISTS` | documentation | **PASS** | docs/PACKAGE_CONTROL_SUITE.md exists |
| `DOC-04-01` | documentation | **PASS** | docs/PACKAGE_CONTROL_SUITE.md contains required phrase: PC-01 |
| `DOC-04-02` | documentation | **PASS** | docs/PACKAGE_CONTROL_SUITE.md contains required phrase: PC-17 |
| `DOC-04-03` | documentation | **PASS** | docs/PACKAGE_CONTROL_SUITE.md contains required phrase: SC-01 |
| `DOC-04-04` | documentation | **PASS** | docs/PACKAGE_CONTROL_SUITE.md contains required phrase: Every package obligation PKG-O01 through PKG-O10 |
| `DOC-05-EXISTS` | documentation | **PASS** | docs/PHASE_BOUNDARY.md exists |
| `DOC-05-01` | documentation | **PASS** | docs/PHASE_BOUNDARY.md contains required phrase: exact finite C1-C8 package semantics |
| `DOC-05-02` | documentation | **PASS** | docs/PHASE_BOUNDARY.md contains required phrase: substantive C6 temporal closure |
| `DOC-05-03` | documentation | **PASS** | docs/PHASE_BOUNDARY.md contains required phrase: strict temporal lineage |
| `DOC-05-04` | documentation | **PASS** | docs/PHASE_BOUNDARY.md contains required phrase: withdrawal autonomy |
| `DOC-05-05` | documentation | **PASS** | docs/PHASE_BOUNDARY.md contains required phrase: positive Temporal-FIACH or Temporal-IAPS witness |
| `DOC-05-06` | documentation | **PASS** | docs/PHASE_BOUNDARY.md contains required phrase: CST-TT-03 |
| `BOUND-NO-HANDOFF` | boundaries | **PASS** | phase explicitly declines a positive handoff witness |
| `BOUND-COMP-1` | boundaries | **PASS** | completion report contains boundary phrase: No positive Temporal-FIACH witness |
| `BOUND-COMP-2` | boundaries | **PASS** | completion report contains boundary phrase: No theorem is represented as Lean-compiled |
| `BOUND-COMP-3` | boundaries | **PASS** | completion report contains boundary phrase: Temporal-IAPS fallback remains locked |
| `BOUND-COMP-4` | boundaries | **PASS** | completion report contains boundary phrase: CST-TT-03 |
| `BOUND-PKG-POS--lineage` | boundaries | **PASS** | PKG-POS-01-TARGET.model.json omits verdict field "lineage" |
| `BOUND-PKG-POS--ancestry` | boundaries | **PASS** | PKG-POS-01-TARGET.model.json omits verdict field "ancestry" |
| `BOUND-PKG-POS--temporal_corridor` | boundaries | **PASS** | PKG-POS-01-TARGET.model.json omits verdict field "temporal_corridor" |
| `BOUND-PKG-POS--autonomy` | boundaries | **PASS** | PKG-POS-01-TARGET.model.json omits verdict field "autonomy" |
| `BOUND-PKG-POS--withdrawal` | boundaries | **PASS** | PKG-POS-01-TARGET.model.json omits verdict field "withdrawal" |
| `BOUND-PKG-POS--fiach` | boundaries | **PASS** | PKG-POS-01-TARGET.model.json omits verdict field "fiach" |
| `BOUND-PKG-POS--consciousness` | boundaries | **PASS** | PKG-POS-01-TARGET.model.json omits verdict field "consciousness" |
| `BOUND-PKG-POS--survival` | boundaries | **PASS** | PKG-POS-01-TARGET.model.json omits verdict field "survival" |
| `BOUND-PKG-POS--identity` | boundaries | **PASS** | PKG-POS-01-TARGET.model.json omits verdict field "identity" |
| `BOUND-PKG-POS--lineage` | boundaries | **PASS** | PKG-POS-02-SOURCE.model.json omits verdict field "lineage" |
| `BOUND-PKG-POS--ancestry` | boundaries | **PASS** | PKG-POS-02-SOURCE.model.json omits verdict field "ancestry" |
| `BOUND-PKG-POS--temporal_corridor` | boundaries | **PASS** | PKG-POS-02-SOURCE.model.json omits verdict field "temporal_corridor" |
| `BOUND-PKG-POS--autonomy` | boundaries | **PASS** | PKG-POS-02-SOURCE.model.json omits verdict field "autonomy" |
| `BOUND-PKG-POS--withdrawal` | boundaries | **PASS** | PKG-POS-02-SOURCE.model.json omits verdict field "withdrawal" |
| `BOUND-PKG-POS--fiach` | boundaries | **PASS** | PKG-POS-02-SOURCE.model.json omits verdict field "fiach" |
| `BOUND-PKG-POS--consciousness` | boundaries | **PASS** | PKG-POS-02-SOURCE.model.json omits verdict field "consciousness" |
| `BOUND-PKG-POS--survival` | boundaries | **PASS** | PKG-POS-02-SOURCE.model.json omits verdict field "survival" |
| `BOUND-PKG-POS--identity` | boundaries | **PASS** | PKG-POS-02-SOURCE.model.json omits verdict field "identity" |
| `MAN-001` | manifest | **SKIP** | phase manifest not required before finalization |
