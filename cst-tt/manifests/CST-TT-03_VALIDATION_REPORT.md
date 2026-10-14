# CST-TT-03 Validation Report

**Overall status:** PASS
**Checks:** 868 total — 865 passed, 0 failed, 3 skipped

The skipped Lean-build check is not a pass. It records that the pinned compiler was unavailable in this environment.

## Category summary

| Category | PASS | FAIL | SKIP |
|---|---:|---:|---:|
| arrow | 6 | 0 | 0 |
| baseline | 5 | 0 | 1 |
| boundaries | 47 | 0 | 0 |
| bounded-search | 14 | 0 | 0 |
| controls | 198 | 0 | 0 |
| documentation | 20 | 0 | 0 |
| inherited | 38 | 0 | 0 |
| lean-static | 87 | 0 | 0 |
| manifest | 0 | 0 | 1 |
| memory | 12 | 0 | 0 |
| provenance | 18 | 0 | 0 |
| python | 67 | 0 | 0 |
| registries | 236 | 0 | 0 |
| routes | 17 | 0 | 0 |
| schemas | 61 | 0 | 0 |
| toolchain | 17 | 0 | 1 |
| transport | 22 | 0 | 0 |

## Checks

| ID | Category | Status | Detail |
|---|---|---|---|
| `BASE-001` | baseline | **PASS** | repository is a Git worktree |
| `BASE-002` | baseline | **PASS** | CST-TT-02 tag resolves to the frozen base |
| `BASE-003` | baseline | **PASS** | frozen CST-TT-02 base is an ancestor of current HEAD |
| `BASE-004` | baseline | **PASS** | repository has no whitespace errors |
| `BASE-005` | baseline | **PASS** | working tree is clean |
| `BASE-006` | baseline | **SKIP** | phase tag not required before freeze |
| `TOOL-001` | toolchain | **PASS** | Lean toolchain remains pinned to v4.28.0 |
| `TOOL-PIN-01` | toolchain | **PASS** | pyproject contains >=3.13,<3.14 |
| `TOOL-PIN-02` | toolchain | **PASS** | pyproject contains pytest==9.0.2 |
| `TOOL-PIN-03` | toolchain | **PASS** | pyproject contains jsonschema==4.26.0 |
| `TOOL-PIN-04` | toolchain | **PASS** | pyproject contains setuptools==82.0.1 |
| `TOOL-PY` | toolchain | **PASS** | running Python is 3.13 (found 3.13.5) |
| `TOOL-STATUS-01` | toolchain | **PASS** | toolchain status phase='CST-TT-03' |
| `TOOL-STATUS-02` | toolchain | **PASS** | toolchain status pinned_toolchain='leanprover/lean4:v4.28.0' |
| `TOOL-STATUS-03` | toolchain | **PASS** | toolchain status registered_generic_proof_source_count=8 |
| `TOOL-STATUS-04` | toolchain | **PASS** | toolchain status new_registered_proof_source_count=6 |
| `TOOL-STATUS-05` | toolchain | **PASS** | toolchain status positive_transport_certificate_count=2 |
| `TOOL-STATUS-06` | toolchain | **PASS** | toolchain status route_certificate_count=2 |
| `TOOL-STATUS-07` | toolchain | **PASS** | toolchain status memory_certificate_count=2 |
| `TOOL-STATUS-08` | toolchain | **PASS** | toolchain status record_arrow_certificate_count=1 |
| `TOOL-STATUS-09` | toolchain | **PASS** | toolchain status control_certificate_count=28 |
| `TOOL-STATUS-10` | toolchain | **PASS** | toolchain status compile_claimed=False |
| `TOOL-STATUS-11` | toolchain | **PASS** | toolchain status static_lean_source_audit_status='passed-by-cst-tt-03-static-suite' |
| `TOOL-LEAN-BUILD` | toolchain | **SKIP** | lean/lake unavailable; no compilation pass claimed |
| `PY-001` | python | **PASS** | at least thirty Python source files are present (65) |
| `PY-COMPILE-001` | python | **PASS** | scripts/build_exp01_assets.py compiles |
| `PY-COMPILE-002` | python | **PASS** | scripts/build_exp02_assets.py compiles |
| `PY-COMPILE-003` | python | **PASS** | scripts/build_exp03_assets.py compiles |
| `PY-COMPILE-004` | python | **PASS** | scripts/build_exp04_assets.py compiles |
| `PY-COMPILE-005` | python | **PASS** | scripts/build_exp05_assets.py compiles |
| `PY-COMPILE-006` | python | **PASS** | scripts/build_exp06_assets.py compiles |
| `PY-COMPILE-007` | python | **PASS** | scripts/build_tt00_assets.py compiles |
| `PY-COMPILE-008` | python | **PASS** | scripts/build_tt01_assets.py compiles |
| `PY-COMPILE-009` | python | **PASS** | scripts/build_tt02_assets.py compiles |
| `PY-COMPILE-010` | python | **PASS** | scripts/build_tt03_assets.py compiles |
| `PY-COMPILE-011` | python | **PASS** | scripts/enrich_exp01_assets.py compiles |
| `PY-COMPILE-012` | python | **PASS** | scripts/exp02_supplemental.py compiles |
| `PY-COMPILE-013` | python | **PASS** | scripts/exp03_data.py compiles |
| `PY-COMPILE-014` | python | **PASS** | scripts/exp04_data.py compiles |
| `PY-COMPILE-015` | python | **PASS** | scripts/exp05_data.py compiles |
| `PY-COMPILE-016` | python | **PASS** | scripts/exp06_data.py compiles |
| `PY-COMPILE-017` | python | **PASS** | scripts/extract_corpus.py compiles |
| `PY-COMPILE-018` | python | **PASS** | scripts/finalize_exp02_manifest.py compiles |
| `PY-COMPILE-019` | python | **PASS** | scripts/finalize_exp03_manifest.py compiles |
| `PY-COMPILE-020` | python | **PASS** | scripts/finalize_exp04_manifest.py compiles |
| `PY-COMPILE-021` | python | **PASS** | scripts/finalize_exp05_manifest.py compiles |
| `PY-COMPILE-022` | python | **PASS** | scripts/finalize_exp06_manifest.py compiles |
| `PY-COMPILE-023` | python | **PASS** | scripts/finalize_tt00_manifest.py compiles |
| `PY-COMPILE-024` | python | **PASS** | scripts/finalize_tt01_manifest.py compiles |
| `PY-COMPILE-025` | python | **PASS** | scripts/finalize_tt02_manifest.py compiles |
| `PY-COMPILE-026` | python | **PASS** | scripts/finalize_tt03_manifest.py compiles |
| `PY-COMPILE-027` | python | **PASS** | scripts/tt00_data.py compiles |
| `PY-COMPILE-028` | python | **PASS** | scripts/tt02_data.py compiles |
| `PY-COMPILE-029` | python | **PASS** | scripts/tt03_data.py compiles |
| `PY-COMPILE-030` | python | **PASS** | scripts/validate_exp01.py compiles |
| `PY-COMPILE-031` | python | **PASS** | scripts/validate_exp02.py compiles |
| `PY-COMPILE-032` | python | **PASS** | scripts/validate_exp03.py compiles |
| `PY-COMPILE-033` | python | **PASS** | scripts/validate_exp04.py compiles |
| `PY-COMPILE-034` | python | **PASS** | scripts/validate_exp05.py compiles |
| `PY-COMPILE-035` | python | **PASS** | scripts/validate_exp06.py compiles |
| `PY-COMPILE-036` | python | **PASS** | scripts/validate_tt00.py compiles |
| `PY-COMPILE-037` | python | **PASS** | scripts/validate_tt01.py compiles |
| `PY-COMPILE-038` | python | **PASS** | scripts/validate_tt02.py compiles |
| `PY-COMPILE-039` | python | **PASS** | scripts/validate_tt03.py compiles |
| `PY-COMPILE-040` | python | **PASS** | scripts/verify_exp03_rebuild.py compiles |
| `PY-COMPILE-041` | python | **PASS** | scripts/verify_exp04_rebuild.py compiles |
| `PY-COMPILE-042` | python | **PASS** | scripts/verify_exp05_rebuild.py compiles |
| `PY-COMPILE-043` | python | **PASS** | scripts/verify_exp06_rebuild.py compiles |
| `PY-COMPILE-044` | python | **PASS** | scripts/verify_tt00_rebuild.py compiles |
| `PY-COMPILE-045` | python | **PASS** | scripts/verify_tt01_rebuild.py compiles |
| `PY-COMPILE-046` | python | **PASS** | scripts/verify_tt02_rebuild.py compiles |
| `PY-COMPILE-047` | python | **PASS** | scripts/verify_tt03_rebuild.py compiles |
| `PY-COMPILE-048` | python | **PASS** | src/cst_tt/__init__.py compiles |
| `PY-COMPILE-049` | python | **PASS** | src/cst_tt/ancestry.py compiles |
| `PY-COMPILE-050` | python | **PASS** | src/cst_tt/autonomy.py compiles |
| `PY-COMPILE-051` | python | **PASS** | src/cst_tt/circularity.py compiles |
| `PY-COMPILE-052` | python | **PASS** | src/cst_tt/contracts.py compiles |
| `PY-COMPILE-053` | python | **PASS** | src/cst_tt/corridor.py compiles |
| `PY-COMPILE-054` | python | **PASS** | src/cst_tt/countermodels.py compiles |
| `PY-COMPILE-055` | python | **PASS** | src/cst_tt/hashing.py compiles |
| `PY-COMPILE-056` | python | **PASS** | src/cst_tt/package.py compiles |
| `PY-COMPILE-057` | python | **PASS** | src/cst_tt/package_auditor.py compiles |
| `PY-COMPILE-058` | python | **PASS** | src/cst_tt/package_gluing.py compiles |
| `PY-COMPILE-059` | python | **PASS** | src/cst_tt/predicates.py compiles |
| `PY-COMPILE-060` | python | **PASS** | src/cst_tt/registry.py compiles |
| `PY-COMPILE-061` | python | **PASS** | src/cst_tt/targets.py compiles |
| `PY-COMPILE-062` | python | **PASS** | src/cst_tt/temporal.py compiles |
| `PY-COMPILE-063` | python | **PASS** | src/cst_tt/transport.py compiles |
| `PY-COMPILE-064` | python | **PASS** | src/cst_tt/transport_auditor.py compiles |
| `PY-COMPILE-065` | python | **PASS** | src/cst_tt/types.py compiles |
| `PY-TESTS` | python | **PASS** | full pytest suite passes |
| `PROV-001` | provenance | **PASS** | four frozen top-level inputs remain hash-bound |
| `PROV-INPUT-01` | provenance | **PASS** | frozen input checksum row 1 verifies |
| `PROV-INPUT-02` | provenance | **PASS** | frozen input checksum row 2 verifies |
| `PROV-INPUT-03` | provenance | **PASS** | frozen input checksum row 3 verifies |
| `PROV-INPUT-04` | provenance | **PASS** | frozen input checksum row 4 verifies |
| `PROV-SOURCE-COUNT` | provenance | **PASS** | nine temporal SBT source manuscripts are retained |
| `PROV-SOURCE-01` | provenance | **PASS** | Tsiokos_2026_An_Audited_Closure_Architecture_for_Consciousness_Exact_Finite_Models_Structural_Theorems_and_Conditional_Realization.tex is retained and nonempty |
| `PROV-SOURCE-02` | provenance | **PASS** | Tsiokos_2026_Glass_Is_an_Unclosed_Layer_Kovacs_Memory_as_Predictive_Quotient_Residue.tex is retained and nonempty |
| `PROV-SOURCE-03` | provenance | **PASS** | Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex is retained and nonempty |
| `PROV-SOURCE-04` | provenance | **PASS** | Tsiokos_2026_Six_Birds_Foundations_IV_A_Catalog_of_Layer_Agnostic_Structural_Laws.tex is retained and nonempty |
| `PROV-SOURCE-05` | provenance | **PASS** | Tsiokos_2026_Six_Birds_Foundations_VI_A_Catalog_of_Dynamical_Structural_Laws.tex is retained and nonempty |
| `PROV-SOURCE-06` | provenance | **PASS** | Tsiokos_2026_Six_Birds_Protocol_Trap_Holonomy_Without_Entropy_Production.tex is retained and nonempty |
| `PROV-SOURCE-07` | provenance | **PASS** | Tsiokos_2026_To_Flatten_a_Stone_with_Six_Birds_Critical_Pairs_Holonomy_and_Confluence_in_Rewriting_Systems.tex is retained and nonempty |
| `PROV-SOURCE-08` | provenance | **PASS** | Tsiokos_2026_To_Lay_a_Stone_with_Six_Birds_Finite_State_Semantics_for_Packaging_Directionality_and_Coarse_Graining.tex is retained and nonempty |
| `PROV-SOURCE-09` | provenance | **PASS** | Tsiokos_2026_To_Notch_a_Stone_with_Six_Birds_Time_as_a_Theory_Artifact_of_Order_Measure_and_Arrow.tex is retained and nonempty |
| `PROV-TAG-01` | provenance | **PASS** | CST-TT-00-v1 resolves to its frozen commit |
| `PROV-TAG-02` | provenance | **PASS** | CST-TT-01-v1 resolves to its frozen commit |
| `PROV-TAG-03` | provenance | **PASS** | CST-TT-02-v1 resolves to its frozen commit |
| `INHERIT-CM-COUNT` | inherited | **PASS** | the fifteen-countermodel negative kernel remains intact |
| `INHERIT-CM-01-MODEL` | inherited | **PASS** | CM-01 model remains present |
| `INHERIT-CM-01-CERT` | inherited | **PASS** | CM-01 certificate remains present |
| `INHERIT-CM-02-MODEL` | inherited | **PASS** | CM-02 model remains present |
| `INHERIT-CM-02-CERT` | inherited | **PASS** | CM-02 certificate remains present |
| `INHERIT-CM-03-MODEL` | inherited | **PASS** | CM-03 model remains present |
| `INHERIT-CM-03-CERT` | inherited | **PASS** | CM-03 certificate remains present |
| `INHERIT-CM-04-MODEL` | inherited | **PASS** | CM-04 model remains present |
| `INHERIT-CM-04-CERT` | inherited | **PASS** | CM-04 certificate remains present |
| `INHERIT-CM-05-MODEL` | inherited | **PASS** | CM-05 model remains present |
| `INHERIT-CM-05-CERT` | inherited | **PASS** | CM-05 certificate remains present |
| `INHERIT-CM-06-MODEL` | inherited | **PASS** | CM-06 model remains present |
| `INHERIT-CM-06-CERT` | inherited | **PASS** | CM-06 certificate remains present |
| `INHERIT-CM-07-MODEL` | inherited | **PASS** | CM-07 model remains present |
| `INHERIT-CM-07-CERT` | inherited | **PASS** | CM-07 certificate remains present |
| `INHERIT-CM-08-MODEL` | inherited | **PASS** | CM-08 model remains present |
| `INHERIT-CM-08-CERT` | inherited | **PASS** | CM-08 certificate remains present |
| `INHERIT-CM-09-MODEL` | inherited | **PASS** | CM-09 model remains present |
| `INHERIT-CM-09-CERT` | inherited | **PASS** | CM-09 certificate remains present |
| `INHERIT-CM-10-MODEL` | inherited | **PASS** | CM-10 model remains present |
| `INHERIT-CM-10-CERT` | inherited | **PASS** | CM-10 certificate remains present |
| `INHERIT-CM-11-MODEL` | inherited | **PASS** | CM-11 model remains present |
| `INHERIT-CM-11-CERT` | inherited | **PASS** | CM-11 certificate remains present |
| `INHERIT-CM-12-MODEL` | inherited | **PASS** | CM-12 model remains present |
| `INHERIT-CM-12-CERT` | inherited | **PASS** | CM-12 certificate remains present |
| `INHERIT-CM-13-MODEL` | inherited | **PASS** | CM-13 model remains present |
| `INHERIT-CM-13-CERT` | inherited | **PASS** | CM-13 certificate remains present |
| `INHERIT-CM-14-MODEL` | inherited | **PASS** | CM-14 model remains present |
| `INHERIT-CM-14-CERT` | inherited | **PASS** | CM-14 certificate remains present |
| `INHERIT-CM-15-MODEL` | inherited | **PASS** | CM-15 model remains present |
| `INHERIT-CM-15-CERT` | inherited | **PASS** | CM-15 certificate remains present |
| `INHERIT-PKG-COUNT` | inherited | **PASS** | two integrated package witnesses remain registered |
| `INHERIT-PKG-01-HASH` | inherited | **PASS** | PKG-POS-01-TARGET model hash verifies |
| `INHERIT-PKG-01-AUDIT` | inherited | **PASS** | PKG-POS-01-TARGET package audit recomputes exactly |
| `INHERIT-PKG-02-HASH` | inherited | **PASS** | PKG-POS-02-SOURCE model hash verifies |
| `INHERIT-PKG-02-AUDIT` | inherited | **PASS** | PKG-POS-02-SOURCE package audit recomputes exactly |
| `INHERIT-STAGED-LINK` | inherited | **PASS** | staged assembly and both typed endpoint packages remain present |
| `INHERIT-STAGED-AUDIT` | inherited | **PASS** | staged heterogeneous package assembly recomputes exactly |
| `ROUTE-COUNT` | routes | **PASS** | exactly two route-discipline witnesses are registered |
| `ROUTE-01-MODEL` | routes | **PASS** | ROUTE-POS-01 model exists |
| `ROUTE-01-CERT` | routes | **PASS** | ROUTE-POS-01 certificate exists |
| `ROUTE-01-HASH` | routes | **PASS** | ROUTE-POS-01 model hash matches registry and certificate |
| `ROUTE-01-AUDIT` | routes | **PASS** | ROUTE-POS-01 audit recomputes exactly |
| `ROUTE-01-SCHEMA` | routes | **PASS** | ROUTE-POS-01 certificate validates: no schema errors |
| `ROUTE-01-LANE` | routes | **PASS** | ROUTE-POS-01 remains S-T only |
| `ROUTE-02-MODEL` | routes | **PASS** | ROUTE-NEG-01 model exists |
| `ROUTE-02-CERT` | routes | **PASS** | ROUTE-NEG-01 certificate exists |
| `ROUTE-02-HASH` | routes | **PASS** | ROUTE-NEG-01 model hash matches registry and certificate |
| `ROUTE-02-AUDIT` | routes | **PASS** | ROUTE-NEG-01 audit recomputes exactly |
| `ROUTE-02-SCHEMA` | routes | **PASS** | ROUTE-NEG-01 certificate validates: no schema errors |
| `ROUTE-02-LANE` | routes | **PASS** | ROUTE-NEG-01 remains S-T only |
| `ROUTE-POS-FLAT` | routes | **PASS** | confluent completion has a valid flat endpoint certificate |
| `ROUTE-POS-NOHOL` | routes | **PASS** | confluent completion removes declared residue and translation holonomy |
| `ROUTE-NEG-INDEXED` | routes | **PASS** | holonomy witness is well-formed but not flat |
| `ROUTE-NEG-HOL` | routes | **PASS** | translation holonomy obstructs a boundary-indexed global now |
| `TRANS-COUNT` | transport | **PASS** | exactly two positive temporal-transport certificates are registered |
| `TRANS-01-MODEL` | transport | **PASS** | TR-POS-01 model exists |
| `TRANS-01-CERT` | transport | **PASS** | TR-POS-01 certificate exists |
| `TRANS-01-HASH` | transport | **PASS** | TR-POS-01 model hash matches registry and certificate |
| `TRANS-01-AUDIT` | transport | **PASS** | TR-POS-01 audit recomputes exactly |
| `TRANS-01-VALID` | transport | **PASS** | TR-POS-01 satisfies every frozen transport obligation |
| `TRANS-01-CARRIERS` | transport | **PASS** | TR-POS-01 uses separately identified carriers |
| `TRANS-01-REP` | transport | **PASS** | TR-POS-01 descends on the declared source predictive quotient |
| `TRANS-01-ARROW` | transport | **PASS** | TR-POS-01 preserves progress and strict record descent |
| `TRANS-01-OWNER` | transport | **PASS** | TR-POS-01 translates maintenance and target ownership |
| `TRANS-01-SCHEMA` | transport | **PASS** | TR-POS-01 certificate validates: no schema errors |
| `TRANS-01-BOUND-01` | boundaries | **PASS** | TR-POS-01 omits verdict key same_subject |
| `TRANS-01-BOUND-02` | boundaries | **PASS** | TR-POS-01 omits verdict key same_person |
| `TRANS-01-BOUND-03` | boundaries | **PASS** | TR-POS-01 omits verdict key personal_identity |
| `TRANS-01-BOUND-04` | boundaries | **PASS** | TR-POS-01 omits verdict key survival |
| `TRANS-01-BOUND-05` | boundaries | **PASS** | TR-POS-01 omits verdict key consciousness |
| `TRANS-01-BOUND-06` | boundaries | **PASS** | TR-POS-01 omits verdict key temporal_fiach |
| `TRANS-01-BOUND-07` | boundaries | **PASS** | TR-POS-01 omits verdict key continuation_verdict |
| `TRANS-02-MODEL` | transport | **PASS** | TR-POS-02-FLAT model exists |
| `TRANS-02-CERT` | transport | **PASS** | TR-POS-02-FLAT certificate exists |
| `TRANS-02-HASH` | transport | **PASS** | TR-POS-02-FLAT model hash matches registry and certificate |
| `TRANS-02-AUDIT` | transport | **PASS** | TR-POS-02-FLAT audit recomputes exactly |
| `TRANS-02-VALID` | transport | **PASS** | TR-POS-02-FLAT satisfies every frozen transport obligation |
| `TRANS-02-CARRIERS` | transport | **PASS** | TR-POS-02-FLAT uses separately identified carriers |
| `TRANS-02-REP` | transport | **PASS** | TR-POS-02-FLAT descends on the declared source predictive quotient |
| `TRANS-02-ARROW` | transport | **PASS** | TR-POS-02-FLAT preserves progress and strict record descent |
| `TRANS-02-OWNER` | transport | **PASS** | TR-POS-02-FLAT translates maintenance and target ownership |
| `TRANS-02-SCHEMA` | transport | **PASS** | TR-POS-02-FLAT certificate validates: no schema errors |
| `TRANS-02-BOUND-01` | boundaries | **PASS** | TR-POS-02-FLAT omits verdict key same_subject |
| `TRANS-02-BOUND-02` | boundaries | **PASS** | TR-POS-02-FLAT omits verdict key same_person |
| `TRANS-02-BOUND-03` | boundaries | **PASS** | TR-POS-02-FLAT omits verdict key personal_identity |
| `TRANS-02-BOUND-04` | boundaries | **PASS** | TR-POS-02-FLAT omits verdict key survival |
| `TRANS-02-BOUND-05` | boundaries | **PASS** | TR-POS-02-FLAT omits verdict key consciousness |
| `TRANS-02-BOUND-06` | boundaries | **PASS** | TR-POS-02-FLAT omits verdict key temporal_fiach |
| `TRANS-02-BOUND-07` | boundaries | **PASS** | TR-POS-02-FLAT omits verdict key continuation_verdict |
| `TRANS-FLAT-REF` | transport | **PASS** | flat transport binds the separately checked route certificate |
| `MEM-COUNT` | memory | **PASS** | route-memory and flat alternatives are both registered |
| `MEM-01-HASH` | memory | **PASS** | MEM-POS-01 hash verifies |
| `MEM-01-AUDIT` | memory | **PASS** | MEM-POS-01 audit recomputes exactly |
| `MEM-01-VALID` | memory | **PASS** | MEM-POS-01 satisfies its declared memory-or-flatness branch |
| `MEM-01-SCHEMA` | memory | **PASS** | MEM-POS-01 certificate validates: no schema errors |
| `MEM-02-HASH` | memory | **PASS** | MEM-FLAT-01 hash verifies |
| `MEM-02-AUDIT` | memory | **PASS** | MEM-FLAT-01 audit recomputes exactly |
| `MEM-02-VALID` | memory | **PASS** | MEM-FLAT-01 satisfies its declared memory-or-flatness branch |
| `MEM-02-SCHEMA` | memory | **PASS** | MEM-FLAT-01 certificate validates: no schema errors |
| `MEM-POS-NOPRED` | memory | **PASS** | current equality does not determine the predictive future in the memory witness |
| `MEM-POS-REPAIR` | memory | **PASS** | route residue repairs the predictive representation |
| `MEM-FLAT-ALT` | memory | **PASS** | flatness supplies the memory-free alternative |
| `ARROW-COUNT` | arrow | **PASS** | one positive record-arrow witness is registered |
| `ARROW-HASH` | arrow | **PASS** | record-arrow model hash verifies |
| `ARROW-AUDIT` | arrow | **PASS** | record-arrow audit recomputes exactly |
| `ARROW-VALID` | arrow | **PASS** | strict record descent is transported |
| `ARROW-SEARCH` | arrow | **PASS** | bounded map search examined 125 maps and found 10 strict maps |
| `ARROW-SCHEMA` | arrow | **PASS** | record-arrow certificate validates: no schema errors |
| `CTRL-COUNT` | controls | **PASS** | exactly twenty-eight transport/route/memory/arrow controls are registered |
| `CTRL-FAMILIES` | controls | **PASS** | control-family counts are frozen ({'transport': 15, 'route': 8, 'memory': 1, 'record-arrow': 4}) |
| `CTRL-01-MODEL` | controls | **PASS** | TR-C01 model exists |
| `CTRL-01-CERT` | controls | **PASS** | TR-C01 certificate exists |
| `CTRL-01-HASH` | controls | **PASS** | TR-C01 model hash matches certificate |
| `CTRL-01-INVALID` | controls | **PASS** | TR-C01 is rejected by its declared checker |
| `CTRL-01-PRIMARY` | controls | **PASS** | TR-C01 exposes expected failure carriers-distinct |
| `CTRL-01-FAILURES` | controls | **PASS** | TR-C01 observed failures recompute exactly |
| `CTRL-01-SCHEMA` | controls | **PASS** | TR-C01 certificate validates: no schema errors |
| `CTRL-02-MODEL` | controls | **PASS** | TR-C02 model exists |
| `CTRL-02-CERT` | controls | **PASS** | TR-C02 certificate exists |
| `CTRL-02-HASH` | controls | **PASS** | TR-C02 model hash matches certificate |
| `CTRL-02-INVALID` | controls | **PASS** | TR-C02 is rejected by its declared checker |
| `CTRL-02-PRIMARY` | controls | **PASS** | TR-C02 exposes expected failure component-maps-complete |
| `CTRL-02-FAILURES` | controls | **PASS** | TR-C02 observed failures recompute exactly |
| `CTRL-02-SCHEMA` | controls | **PASS** | TR-C02 certificate validates: no schema errors |
| `CTRL-03-MODEL` | controls | **PASS** | TR-C03 model exists |
| `CTRL-03-CERT` | controls | **PASS** | TR-C03 certificate exists |
| `CTRL-03-HASH` | controls | **PASS** | TR-C03 model hash matches certificate |
| `CTRL-03-INVALID` | controls | **PASS** | TR-C03 is rejected by its declared checker |
| `CTRL-03-PRIMARY` | controls | **PASS** | TR-C03 exposes expected failure predictive-representative-independence |
| `CTRL-03-FAILURES` | controls | **PASS** | TR-C03 observed failures recompute exactly |
| `CTRL-03-SCHEMA` | controls | **PASS** | TR-C03 certificate validates: no schema errors |
| `CTRL-04-MODEL` | controls | **PASS** | TR-C04 model exists |
| `CTRL-04-CERT` | controls | **PASS** | TR-C04 certificate exists |
| `CTRL-04-HASH` | controls | **PASS** | TR-C04 model hash matches certificate |
| `CTRL-04-INVALID` | controls | **PASS** | TR-C04 is rejected by its declared checker |
| `CTRL-04-PRIMARY` | controls | **PASS** | TR-C04 exposes expected failure mapped-signature-agreement |
| `CTRL-04-FAILURES` | controls | **PASS** | TR-C04 observed failures recompute exactly |
| `CTRL-04-SCHEMA` | controls | **PASS** | TR-C04 certificate validates: no schema errors |
| `CTRL-05-MODEL` | controls | **PASS** | TR-C05 model exists |
| `CTRL-05-CERT` | controls | **PASS** | TR-C05 certificate exists |
| `CTRL-05-HASH` | controls | **PASS** | TR-C05 model hash matches certificate |
| `CTRL-05-INVALID` | controls | **PASS** | TR-C05 is rejected by its declared checker |
| `CTRL-05-PRIMARY` | controls | **PASS** | TR-C05 exposes expected failure successor-preserved |
| `CTRL-05-FAILURES` | controls | **PASS** | TR-C05 observed failures recompute exactly |
| `CTRL-05-SCHEMA` | controls | **PASS** | TR-C05 certificate validates: no schema errors |
| `CTRL-06-MODEL` | controls | **PASS** | TR-C06 model exists |
| `CTRL-06-CERT` | controls | **PASS** | TR-C06 certificate exists |
| `CTRL-06-HASH` | controls | **PASS** | TR-C06 model hash matches certificate |
| `CTRL-06-INVALID` | controls | **PASS** | TR-C06 is rejected by its declared checker |
| `CTRL-06-PRIMARY` | controls | **PASS** | TR-C06 exposes expected failure tick-progress-preserved |
| `CTRL-06-FAILURES` | controls | **PASS** | TR-C06 observed failures recompute exactly |
| `CTRL-06-SCHEMA` | controls | **PASS** | TR-C06 certificate validates: no schema errors |
| `CTRL-07-MODEL` | controls | **PASS** | TR-C07 model exists |
| `CTRL-07-CERT` | controls | **PASS** | TR-C07 certificate exists |
| `CTRL-07-HASH` | controls | **PASS** | TR-C07 model hash matches certificate |
| `CTRL-07-INVALID` | controls | **PASS** | TR-C07 is rejected by its declared checker |
| `CTRL-07-PRIMARY` | controls | **PASS** | TR-C07 exposes expected failure strict-record-arrow-preserved |
| `CTRL-07-FAILURES` | controls | **PASS** | TR-C07 observed failures recompute exactly |
| `CTRL-07-SCHEMA` | controls | **PASS** | TR-C07 certificate validates: no schema errors |
| `CTRL-08-MODEL` | controls | **PASS** | TR-C08 model exists |
| `CTRL-08-CERT` | controls | **PASS** | TR-C08 certificate exists |
| `CTRL-08-HASH` | controls | **PASS** | TR-C08 model hash matches certificate |
| `CTRL-08-INVALID` | controls | **PASS** | TR-C08 is rejected by its declared checker |
| `CTRL-08-PRIMARY` | controls | **PASS** | TR-C08 exposes expected failure route-discipline-satisfied |
| `CTRL-08-FAILURES` | controls | **PASS** | TR-C08 observed failures recompute exactly |
| `CTRL-08-SCHEMA` | controls | **PASS** | TR-C08 certificate validates: no schema errors |
| `CTRL-09-MODEL` | controls | **PASS** | TR-C09 model exists |
| `CTRL-09-CERT` | controls | **PASS** | TR-C09 certificate exists |
| `CTRL-09-HASH` | controls | **PASS** | TR-C09 model hash matches certificate |
| `CTRL-09-INVALID` | controls | **PASS** | TR-C09 is rejected by its declared checker |
| `CTRL-09-PRIMARY` | controls | **PASS** | TR-C09 exposes expected failure maintenance-translated |
| `CTRL-09-FAILURES` | controls | **PASS** | TR-C09 observed failures recompute exactly |
| `CTRL-09-SCHEMA` | controls | **PASS** | TR-C09 certificate validates: no schema errors |
| `CTRL-10-MODEL` | controls | **PASS** | TR-C10 model exists |
| `CTRL-10-CERT` | controls | **PASS** | TR-C10 certificate exists |
| `CTRL-10-HASH` | controls | **PASS** | TR-C10 model hash matches certificate |
| `CTRL-10-INVALID` | controls | **PASS** | TR-C10 is rejected by its declared checker |
| `CTRL-10-PRIMARY` | controls | **PASS** | TR-C10 exposes expected failure ownership-interface-valid |
| `CTRL-10-FAILURES` | controls | **PASS** | TR-C10 observed failures recompute exactly |
| `CTRL-10-SCHEMA` | controls | **PASS** | TR-C10 certificate validates: no schema errors |
| `CTRL-11-MODEL` | controls | **PASS** | TR-C11 model exists |
| `CTRL-11-CERT` | controls | **PASS** | TR-C11 certificate exists |
| `CTRL-11-HASH` | controls | **PASS** | TR-C11 model hash matches certificate |
| `CTRL-11-INVALID` | controls | **PASS** | TR-C11 is rejected by its declared checker |
| `CTRL-11-PRIMARY` | controls | **PASS** | TR-C11 exposes expected failure forbidden-verdict-fields-absent |
| `CTRL-11-FAILURES` | controls | **PASS** | TR-C11 observed failures recompute exactly |
| `CTRL-11-SCHEMA` | controls | **PASS** | TR-C11 certificate validates: no schema errors |
| `CTRL-12-MODEL` | controls | **PASS** | TR-C12 model exists |
| `CTRL-12-CERT` | controls | **PASS** | TR-C12 certificate exists |
| `CTRL-12-HASH` | controls | **PASS** | TR-C12 model hash matches certificate |
| `CTRL-12-INVALID` | controls | **PASS** | TR-C12 is rejected by its declared checker |
| `CTRL-12-PRIMARY` | controls | **PASS** | TR-C12 exposes expected failure target-temporal-witness-valid |
| `CTRL-12-FAILURES` | controls | **PASS** | TR-C12 observed failures recompute exactly |
| `CTRL-12-SCHEMA` | controls | **PASS** | TR-C12 certificate validates: no schema errors |
| `CTRL-13-MODEL` | controls | **PASS** | TR-C13 model exists |
| `CTRL-13-CERT` | controls | **PASS** | TR-C13 certificate exists |
| `CTRL-13-HASH` | controls | **PASS** | TR-C13 model hash matches certificate |
| `CTRL-13-INVALID` | controls | **PASS** | TR-C13 is rejected by its declared checker |
| `CTRL-13-PRIMARY` | controls | **PASS** | TR-C13 exposes expected failure alphabets-distinct |
| `CTRL-13-FAILURES` | controls | **PASS** | TR-C13 observed failures recompute exactly |
| `CTRL-13-SCHEMA` | controls | **PASS** | TR-C13 certificate validates: no schema errors |
| `CTRL-14-MODEL` | controls | **PASS** | TR-C14 model exists |
| `CTRL-14-CERT` | controls | **PASS** | TR-C14 certificate exists |
| `CTRL-14-HASH` | controls | **PASS** | TR-C14 model hash matches certificate |
| `CTRL-14-INVALID` | controls | **PASS** | TR-C14 is rejected by its declared checker |
| `CTRL-14-PRIMARY` | controls | **PASS** | TR-C14 exposes expected failure route-discipline-satisfied |
| `CTRL-14-FAILURES` | controls | **PASS** | TR-C14 observed failures recompute exactly |
| `CTRL-14-SCHEMA` | controls | **PASS** | TR-C14 certificate validates: no schema errors |
| `CTRL-15-MODEL` | controls | **PASS** | TR-C15 model exists |
| `CTRL-15-CERT` | controls | **PASS** | TR-C15 certificate exists |
| `CTRL-15-HASH` | controls | **PASS** | TR-C15 model hash matches certificate |
| `CTRL-15-INVALID` | controls | **PASS** | TR-C15 is rejected by its declared checker |
| `CTRL-15-PRIMARY` | controls | **PASS** | TR-C15 exposes expected failure route-residue-retention-noncollapsing |
| `CTRL-15-FAILURES` | controls | **PASS** | TR-C15 observed failures recompute exactly |
| `CTRL-15-SCHEMA` | controls | **PASS** | TR-C15 certificate validates: no schema errors |
| `CTRL-16-MODEL` | controls | **PASS** | ROUTE-C01 model exists |
| `CTRL-16-CERT` | controls | **PASS** | ROUTE-C01 certificate exists |
| `CTRL-16-HASH` | controls | **PASS** | ROUTE-C01 model hash matches certificate |
| `CTRL-16-INVALID` | controls | **PASS** | ROUTE-C01 is rejected by its declared checker |
| `CTRL-16-PRIMARY` | controls | **PASS** | ROUTE-C01 exposes expected failure every-declared-critical-pair-joins |
| `CTRL-16-FAILURES` | controls | **PASS** | ROUTE-C01 observed failures recompute exactly |
| `CTRL-16-SCHEMA` | controls | **PASS** | ROUTE-C01 certificate validates: no schema errors |
| `CTRL-17-MODEL` | controls | **PASS** | ROUTE-C02 model exists |
| `CTRL-17-CERT` | controls | **PASS** | ROUTE-C02 certificate exists |
| `CTRL-17-HASH` | controls | **PASS** | ROUTE-C02 model hash matches certificate |
| `CTRL-17-INVALID` | controls | **PASS** | ROUTE-C02 is rejected by its declared checker |
| `CTRL-17-PRIMARY` | controls | **PASS** | ROUTE-C02 exposes expected failure route-residue-trivial |
| `CTRL-17-FAILURES` | controls | **PASS** | ROUTE-C02 observed failures recompute exactly |
| `CTRL-17-SCHEMA` | controls | **PASS** | ROUTE-C02 certificate validates: no schema errors |
| `CTRL-18-MODEL` | controls | **PASS** | ROUTE-C03 model exists |
| `CTRL-18-CERT` | controls | **PASS** | ROUTE-C03 certificate exists |
| `CTRL-18-HASH` | controls | **PASS** | ROUTE-C03 model hash matches certificate |
| `CTRL-18-INVALID` | controls | **PASS** | ROUTE-C03 is rejected by its declared checker |
| `CTRL-18-PRIMARY` | controls | **PASS** | ROUTE-C03 exposes expected failure clock-translation-holonomy-zero |
| `CTRL-18-FAILURES` | controls | **PASS** | ROUTE-C03 observed failures recompute exactly |
| `CTRL-18-SCHEMA` | controls | **PASS** | ROUTE-C03 certificate validates: no schema errors |
| `CTRL-19-MODEL` | controls | **PASS** | ROUTE-C04 model exists |
| `CTRL-19-CERT` | controls | **PASS** | ROUTE-C04 certificate exists |
| `CTRL-19-HASH` | controls | **PASS** | ROUTE-C04 model hash matches certificate |
| `CTRL-19-INVALID` | controls | **PASS** | ROUTE-C04 is rejected by its declared checker |
| `CTRL-19-PRIMARY` | controls | **PASS** | ROUTE-C04 exposes expected failure all-routes-valid |
| `CTRL-19-FAILURES` | controls | **PASS** | ROUTE-C04 observed failures recompute exactly |
| `CTRL-19-SCHEMA` | controls | **PASS** | ROUTE-C04 certificate validates: no schema errors |
| `CTRL-20-MODEL` | controls | **PASS** | ROUTE-C05 model exists |
| `CTRL-20-CERT` | controls | **PASS** | ROUTE-C05 certificate exists |
| `CTRL-20-HASH` | controls | **PASS** | ROUTE-C05 model hash matches certificate |
| `CTRL-20-INVALID` | controls | **PASS** | ROUTE-C05 is rejected by its declared checker |
| `CTRL-20-PRIMARY` | controls | **PASS** | ROUTE-C05 exposes expected failure unique-normal-form-per-boundary |
| `CTRL-20-FAILURES` | controls | **PASS** | ROUTE-C05 observed failures recompute exactly |
| `CTRL-20-SCHEMA` | controls | **PASS** | ROUTE-C05 certificate validates: no schema errors |
| `CTRL-21-MODEL` | controls | **PASS** | ROUTE-C06 model exists |
| `CTRL-21-CERT` | controls | **PASS** | ROUTE-C06 certificate exists |
| `CTRL-21-HASH` | controls | **PASS** | ROUTE-C06 model hash matches certificate |
| `CTRL-21-INVALID` | controls | **PASS** | ROUTE-C06 is rejected by its declared checker |
| `CTRL-21-PRIMARY` | controls | **PASS** | ROUTE-C06 exposes expected failure direct-factored-agreement |
| `CTRL-21-FAILURES` | controls | **PASS** | ROUTE-C06 observed failures recompute exactly |
| `CTRL-21-SCHEMA` | controls | **PASS** | ROUTE-C06 certificate validates: no schema errors |
| `CTRL-22-MODEL` | controls | **PASS** | ROUTE-C07 model exists |
| `CTRL-22-CERT` | controls | **PASS** | ROUTE-C07 certificate exists |
| `CTRL-22-HASH` | controls | **PASS** | ROUTE-C07 model hash matches certificate |
| `CTRL-22-INVALID` | controls | **PASS** | ROUTE-C07 is rejected by its declared checker |
| `CTRL-22-PRIMARY` | controls | **PASS** | ROUTE-C07 exposes expected failure forbidden-verdict-fields-absent |
| `CTRL-22-FAILURES` | controls | **PASS** | ROUTE-C07 observed failures recompute exactly |
| `CTRL-22-SCHEMA` | controls | **PASS** | ROUTE-C07 certificate validates: no schema errors |
| `CTRL-23-MODEL` | controls | **PASS** | ROUTE-C08 model exists |
| `CTRL-23-CERT` | controls | **PASS** | ROUTE-C08 certificate exists |
| `CTRL-23-HASH` | controls | **PASS** | ROUTE-C08 model hash matches certificate |
| `CTRL-23-INVALID` | controls | **PASS** | ROUTE-C08 is rejected by its declared checker |
| `CTRL-23-PRIMARY` | controls | **PASS** | ROUTE-C08 exposes expected failure memory-or-flatness-satisfied |
| `CTRL-23-FAILURES` | controls | **PASS** | ROUTE-C08 observed failures recompute exactly |
| `CTRL-23-SCHEMA` | controls | **PASS** | ROUTE-C08 certificate validates: no schema errors |
| `CTRL-24-MODEL` | controls | **PASS** | MEM-C01 model exists |
| `CTRL-24-CERT` | controls | **PASS** | MEM-C01 certificate exists |
| `CTRL-24-HASH` | controls | **PASS** | MEM-C01 model hash matches certificate |
| `CTRL-24-INVALID` | controls | **PASS** | MEM-C01 is rejected by its declared checker |
| `CTRL-24-PRIMARY` | controls | **PASS** | MEM-C01 exposes expected failure route-memory-separates-collision |
| `CTRL-24-FAILURES` | controls | **PASS** | MEM-C01 observed failures recompute exactly |
| `CTRL-24-SCHEMA` | controls | **PASS** | MEM-C01 certificate validates: no schema errors |
| `CTRL-25-MODEL` | controls | **PASS** | ARROW-C01 model exists |
| `CTRL-25-CERT` | controls | **PASS** | ARROW-C01 certificate exists |
| `CTRL-25-HASH` | controls | **PASS** | ARROW-C01 model hash matches certificate |
| `CTRL-25-INVALID` | controls | **PASS** | ARROW-C01 is rejected by its declared checker |
| `CTRL-25-PRIMARY` | controls | **PASS** | ARROW-C01 exposes expected failure strict-progress-preserved |
| `CTRL-25-FAILURES` | controls | **PASS** | ARROW-C01 observed failures recompute exactly |
| `CTRL-25-SCHEMA` | controls | **PASS** | ARROW-C01 certificate validates: no schema errors |
| `CTRL-26-MODEL` | controls | **PASS** | ARROW-C02 model exists |
| `CTRL-26-CERT` | controls | **PASS** | ARROW-C02 certificate exists |
| `CTRL-26-HASH` | controls | **PASS** | ARROW-C02 model hash matches certificate |
| `CTRL-26-INVALID` | controls | **PASS** | ARROW-C02 is rejected by its declared checker |
| `CTRL-26-PRIMARY` | controls | **PASS** | ARROW-C02 exposes expected failure nonstrict-monotone |
| `CTRL-26-FAILURES` | controls | **PASS** | ARROW-C02 observed failures recompute exactly |
| `CTRL-26-SCHEMA` | controls | **PASS** | ARROW-C02 certificate validates: no schema errors |
| `CTRL-27-MODEL` | controls | **PASS** | ARROW-C03 model exists |
| `CTRL-27-CERT` | controls | **PASS** | ARROW-C03 certificate exists |
| `CTRL-27-HASH` | controls | **PASS** | ARROW-C03 model hash matches certificate |
| `CTRL-27-INVALID` | controls | **PASS** | ARROW-C03 is rejected by its declared checker |
| `CTRL-27-PRIMARY` | controls | **PASS** | ARROW-C03 exposes expected failure map-total |
| `CTRL-27-FAILURES` | controls | **PASS** | ARROW-C03 observed failures recompute exactly |
| `CTRL-27-SCHEMA` | controls | **PASS** | ARROW-C03 certificate validates: no schema errors |
| `CTRL-28-MODEL` | controls | **PASS** | ARROW-C04 model exists |
| `CTRL-28-CERT` | controls | **PASS** | ARROW-C04 certificate exists |
| `CTRL-28-HASH` | controls | **PASS** | ARROW-C04 model hash matches certificate |
| `CTRL-28-INVALID` | controls | **PASS** | ARROW-C04 is rejected by its declared checker |
| `CTRL-28-PRIMARY` | controls | **PASS** | ARROW-C04 exposes expected failure source-has-strict-arrow |
| `CTRL-28-FAILURES` | controls | **PASS** | ARROW-C04 observed failures recompute exactly |
| `CTRL-28-SCHEMA` | controls | **PASS** | ARROW-C04 certificate validates: no schema errors |
| `SEARCH-TRANS-EXACT` | bounded-search | **PASS** | BOUNDED_TRANSPORT_SHAPE_SEARCH.json reproduces byte-equivalent semantic content |
| `SEARCH-TRANS-PASS` | bounded-search | **PASS** | BOUNDED_TRANSPORT_SHAPE_SEARCH.json reports PASS |
| `SEARCH-TRANS-COUNT` | bounded-search | **PASS** | BOUNDED_TRANSPORT_SHAPE_SEARCH.json retains the declared bounded count 12 |
| `SEARCH-CONF-EXACT` | bounded-search | **PASS** | BOUNDED_CONFLUENCE_SHAPE_SEARCH.json reproduces byte-equivalent semantic content |
| `SEARCH-CONF-PASS` | bounded-search | **PASS** | BOUNDED_CONFLUENCE_SHAPE_SEARCH.json reports PASS |
| `SEARCH-CONF-COUNT` | bounded-search | **PASS** | BOUNDED_CONFLUENCE_SHAPE_SEARCH.json retains the declared bounded count 354 |
| `SEARCH-MEM-EXACT` | bounded-search | **PASS** | BOUNDED_MEMORY_OR_FLATNESS_EXHAUSTION.json reproduces byte-equivalent semantic content |
| `SEARCH-MEM-PASS` | bounded-search | **PASS** | BOUNDED_MEMORY_OR_FLATNESS_EXHAUSTION.json reports PASS |
| `SEARCH-MEM-COUNT` | bounded-search | **PASS** | BOUNDED_MEMORY_OR_FLATNESS_EXHAUSTION.json retains the declared bounded count 64 |
| `SEARCH-NOW-EXACT` | bounded-search | **PASS** | BOUNDED_GLOBAL_NOW_OBSTRUCTION_SEARCH.json reproduces byte-equivalent semantic content |
| `SEARCH-NOW-PASS` | bounded-search | **PASS** | BOUNDED_GLOBAL_NOW_OBSTRUCTION_SEARCH.json reports PASS |
| `SEARCH-NOW-COUNT` | bounded-search | **PASS** | BOUNDED_GLOBAL_NOW_OBSTRUCTION_SEARCH.json retains the declared bounded count 4 |
| `SEARCH-TRANS-MIN` | bounded-search | **PASS** | first feasible transport shape is source/target (3,2) in the declared family |
| `SEARCH-CONF-MIN` | bounded-search | **PASS** | first acyclic two-branch confluence diamond has four nodes |
| `REG-THM-COUNT` | registries | **PASS** | theorem_id registry has 35 rows |
| `REG-THM-UNIQUE` | registries | **PASS** | theorem_id values are unique |
| `REG-TOY-COUNT` | registries | **PASS** | toy_id registry has 23 rows |
| `REG-TOY-UNIQUE` | registries | **PASS** | toy_id values are unique |
| `REG-DEF-COUNT` | registries | **PASS** | definition_id registry has 54 rows |
| `REG-DEF-UNIQUE` | registries | **PASS** | definition_id values are unique |
| `REG-SCHEMA-COUNT` | registries | **PASS** | schema_id registry has 15 rows |
| `REG-SCHEMA-UNIQUE` | registries | **PASS** | schema_id values are unique |
| `REG-KILL-COUNT` | registries | **PASS** | kill_id registry has 18 rows |
| `REG-KILL-UNIQUE` | registries | **PASS** | kill_id values are unique |
| `REG-THM-STATUS` | registries | **PASS** | theorem status distribution matches CST-TT-03 |
| `REG-ADV-01` | registries | **PASS** | TTH-03 is advanced in CST-TT-03 |
| `REG-ADV-02` | registries | **PASS** | TTH-09 is advanced in CST-TT-03 |
| `REG-ADV-03` | registries | **PASS** | TTH-10 is advanced in CST-TT-03 |
| `REG-ADV-04` | registries | **PASS** | TTN-04 is advanced in CST-TT-03 |
| `REG-ADV-05` | registries | **PASS** | TTN-05 is advanced in CST-TT-03 |
| `REG-THM-01-DEPS` | registries | **PASS** | TTH-01 theorem dependencies resolve |
| `REG-THM-01-TOYS` | registries | **PASS** | TTH-01 toy dependencies resolve |
| `REG-THM-01-LEAN` | registries | **PASS** | TTH-01 has one or more resolved Lean declarations |
| `REG-THM-02-DEPS` | registries | **PASS** | TTH-02 theorem dependencies resolve |
| `REG-THM-02-TOYS` | registries | **PASS** | TTH-02 toy dependencies resolve |
| `REG-THM-02-LEAN` | registries | **PASS** | TTH-02 has one or more resolved Lean declarations |
| `REG-THM-03-DEPS` | registries | **PASS** | TTH-03 theorem dependencies resolve |
| `REG-THM-03-TOYS` | registries | **PASS** | TTH-03 toy dependencies resolve |
| `REG-THM-03-LEAN` | registries | **PASS** | TTH-03 has one or more resolved Lean declarations |
| `REG-THM-04-DEPS` | registries | **PASS** | TTH-04 theorem dependencies resolve |
| `REG-THM-04-TOYS` | registries | **PASS** | TTH-04 toy dependencies resolve |
| `REG-THM-04-LEAN` | registries | **PASS** | TTH-04 has one or more resolved Lean declarations |
| `REG-THM-05-DEPS` | registries | **PASS** | TTH-05 theorem dependencies resolve |
| `REG-THM-05-TOYS` | registries | **PASS** | TTH-05 toy dependencies resolve |
| `REG-THM-05-LEAN` | registries | **PASS** | TTH-05 has one or more resolved Lean declarations |
| `REG-THM-06-DEPS` | registries | **PASS** | TTH-06 theorem dependencies resolve |
| `REG-THM-06-TOYS` | registries | **PASS** | TTH-06 toy dependencies resolve |
| `REG-THM-06-LEAN` | registries | **PASS** | TTH-06 has one or more resolved Lean declarations |
| `REG-THM-07-DEPS` | registries | **PASS** | TTH-07 theorem dependencies resolve |
| `REG-THM-07-TOYS` | registries | **PASS** | TTH-07 toy dependencies resolve |
| `REG-THM-07-LEAN` | registries | **PASS** | TTH-07 has one or more resolved Lean declarations |
| `REG-THM-08-DEPS` | registries | **PASS** | TTH-08 theorem dependencies resolve |
| `REG-THM-08-TOYS` | registries | **PASS** | TTH-08 toy dependencies resolve |
| `REG-THM-08-LEAN` | registries | **PASS** | TTH-08 has one or more resolved Lean declarations |
| `REG-THM-09-DEPS` | registries | **PASS** | TTH-09 theorem dependencies resolve |
| `REG-THM-09-TOYS` | registries | **PASS** | TTH-09 toy dependencies resolve |
| `REG-THM-09-LEAN` | registries | **PASS** | TTH-09 has one or more resolved Lean declarations |
| `REG-THM-10-DEPS` | registries | **PASS** | TTH-10 theorem dependencies resolve |
| `REG-THM-10-TOYS` | registries | **PASS** | TTH-10 toy dependencies resolve |
| `REG-THM-10-LEAN` | registries | **PASS** | TTH-10 has one or more resolved Lean declarations |
| `REG-THM-11-DEPS` | registries | **PASS** | TTN-01 theorem dependencies resolve |
| `REG-THM-11-TOYS` | registries | **PASS** | TTN-01 toy dependencies resolve |
| `REG-THM-11-LEAN` | registries | **PASS** | TTN-01 has one or more resolved Lean declarations |
| `REG-THM-12-DEPS` | registries | **PASS** | TTN-02 theorem dependencies resolve |
| `REG-THM-12-TOYS` | registries | **PASS** | TTN-02 toy dependencies resolve |
| `REG-THM-12-LEAN` | registries | **PASS** | TTN-02 has one or more resolved Lean declarations |
| `REG-THM-13-DEPS` | registries | **PASS** | TTN-03 theorem dependencies resolve |
| `REG-THM-13-TOYS` | registries | **PASS** | TTN-03 toy dependencies resolve |
| `REG-THM-13-LEAN` | registries | **PASS** | TTN-03 has one or more resolved Lean declarations |
| `REG-THM-14-DEPS` | registries | **PASS** | TTN-04 theorem dependencies resolve |
| `REG-THM-14-TOYS` | registries | **PASS** | TTN-04 toy dependencies resolve |
| `REG-THM-14-LEAN` | registries | **PASS** | TTN-04 has one or more resolved Lean declarations |
| `REG-THM-15-DEPS` | registries | **PASS** | TTN-05 theorem dependencies resolve |
| `REG-THM-15-TOYS` | registries | **PASS** | TTN-05 toy dependencies resolve |
| `REG-THM-15-LEAN` | registries | **PASS** | TTN-05 has one or more resolved Lean declarations |
| `REG-THM-16-DEPS` | registries | **PASS** | TTN-06 theorem dependencies resolve |
| `REG-THM-16-TOYS` | registries | **PASS** | TTN-06 toy dependencies resolve |
| `REG-THM-16-LEAN` | registries | **PASS** | TTN-06 has one or more resolved Lean declarations |
| `REG-THM-17-DEPS` | registries | **PASS** | TTN-07 theorem dependencies resolve |
| `REG-THM-17-TOYS` | registries | **PASS** | TTN-07 toy dependencies resolve |
| `REG-THM-17-LEAN` | registries | **PASS** | TTN-07 has one or more resolved Lean declarations |
| `REG-THM-18-DEPS` | registries | **PASS** | TTN-08 theorem dependencies resolve |
| `REG-THM-18-TOYS` | registries | **PASS** | TTN-08 toy dependencies resolve |
| `REG-THM-18-LEAN` | registries | **PASS** | TTN-08 has one or more resolved Lean declarations |
| `REG-THM-19-DEPS` | registries | **PASS** | TTN-09 theorem dependencies resolve |
| `REG-THM-19-TOYS` | registries | **PASS** | TTN-09 toy dependencies resolve |
| `REG-THM-19-LEAN` | registries | **PASS** | TTN-09 has one or more resolved Lean declarations |
| `REG-THM-20-DEPS` | registries | **PASS** | TTN-10 theorem dependencies resolve |
| `REG-THM-20-TOYS` | registries | **PASS** | TTN-10 toy dependencies resolve |
| `REG-THM-20-LEAN` | registries | **PASS** | TTN-10 has one or more resolved Lean declarations |
| `REG-THM-21-DEPS` | registries | **PASS** | TTN-11 theorem dependencies resolve |
| `REG-THM-21-TOYS` | registries | **PASS** | TTN-11 toy dependencies resolve |
| `REG-THM-21-LEAN` | registries | **PASS** | TTN-11 has one or more resolved Lean declarations |
| `REG-THM-22-DEPS` | registries | **PASS** | TTN-12 theorem dependencies resolve |
| `REG-THM-22-TOYS` | registries | **PASS** | TTN-12 toy dependencies resolve |
| `REG-THM-22-LEAN` | registries | **PASS** | TTN-12 has one or more resolved Lean declarations |
| `REG-THM-23-DEPS` | registries | **PASS** | TTN-13 theorem dependencies resolve |
| `REG-THM-23-TOYS` | registries | **PASS** | TTN-13 toy dependencies resolve |
| `REG-THM-23-LEAN` | registries | **PASS** | TTN-13 has one or more resolved Lean declarations |
| `REG-THM-24-DEPS` | registries | **PASS** | TTN-14 theorem dependencies resolve |
| `REG-THM-24-TOYS` | registries | **PASS** | TTN-14 toy dependencies resolve |
| `REG-THM-24-LEAN` | registries | **PASS** | TTN-14 has one or more resolved Lean declarations |
| `REG-THM-25-DEPS` | registries | **PASS** | TTD-01 theorem dependencies resolve |
| `REG-THM-25-TOYS` | registries | **PASS** | TTD-01 toy dependencies resolve |
| `REG-THM-25-LEAN` | registries | **PASS** | TTD-01 has one or more resolved Lean declarations |
| `REG-THM-26-DEPS` | registries | **PASS** | TTD-02 theorem dependencies resolve |
| `REG-THM-26-TOYS` | registries | **PASS** | TTD-02 toy dependencies resolve |
| `REG-THM-26-LEAN` | registries | **PASS** | TTD-02 has one or more resolved Lean declarations |
| `REG-THM-27-DEPS` | registries | **PASS** | TTD-03 theorem dependencies resolve |
| `REG-THM-27-TOYS` | registries | **PASS** | TTD-03 toy dependencies resolve |
| `REG-THM-27-LEAN` | registries | **PASS** | TTD-03 has one or more resolved Lean declarations |
| `REG-THM-28-DEPS` | registries | **PASS** | TTF-01 theorem dependencies resolve |
| `REG-THM-28-TOYS` | registries | **PASS** | TTF-01 toy dependencies resolve |
| `REG-THM-28-LEAN` | registries | **PASS** | TTF-01 has one or more resolved Lean declarations |
| `REG-THM-29-DEPS` | registries | **PASS** | TTF-02 theorem dependencies resolve |
| `REG-THM-29-TOYS` | registries | **PASS** | TTF-02 toy dependencies resolve |
| `REG-THM-29-LEAN` | registries | **PASS** | TTF-02 has one or more resolved Lean declarations |
| `REG-THM-30-DEPS` | registries | **PASS** | TTF-03 theorem dependencies resolve |
| `REG-THM-30-TOYS` | registries | **PASS** | TTF-03 toy dependencies resolve |
| `REG-THM-30-LEAN` | registries | **PASS** | TTF-03 has one or more resolved Lean declarations |
| `REG-THM-31-DEPS` | registries | **PASS** | TTF-04 theorem dependencies resolve |
| `REG-THM-31-TOYS` | registries | **PASS** | TTF-04 toy dependencies resolve |
| `REG-THM-31-LEAN` | registries | **PASS** | TTF-04 has one or more resolved Lean declarations |
| `REG-THM-32-DEPS` | registries | **PASS** | TTF-05 theorem dependencies resolve |
| `REG-THM-32-TOYS` | registries | **PASS** | TTF-05 toy dependencies resolve |
| `REG-THM-32-LEAN` | registries | **PASS** | TTF-05 has one or more resolved Lean declarations |
| `REG-THM-33-DEPS` | registries | **PASS** | TTF-06 theorem dependencies resolve |
| `REG-THM-33-TOYS` | registries | **PASS** | TTF-06 toy dependencies resolve |
| `REG-THM-33-LEAN` | registries | **PASS** | TTF-06 has one or more resolved Lean declarations |
| `REG-THM-34-DEPS` | registries | **PASS** | TTF-07 theorem dependencies resolve |
| `REG-THM-34-TOYS` | registries | **PASS** | TTF-07 toy dependencies resolve |
| `REG-THM-34-LEAN` | registries | **PASS** | TTF-07 has one or more resolved Lean declarations |
| `REG-THM-35-DEPS` | registries | **PASS** | TTF-08 theorem dependencies resolve |
| `REG-THM-35-TOYS` | registries | **PASS** | TTF-08 toy dependencies resolve |
| `REG-THM-35-LEAN` | registries | **PASS** | TTF-08 has one or more resolved Lean declarations |
| `REG-DEF-01-MODULE` | registries | **PASS** | D-001 module resolves |
| `REG-DEF-01-NAME` | registries | **PASS** | D-001 name occurs in its module |
| `REG-DEF-02-MODULE` | registries | **PASS** | D-002 module resolves |
| `REG-DEF-02-NAME` | registries | **PASS** | D-002 name occurs in its module |
| `REG-DEF-03-MODULE` | registries | **PASS** | D-003 module resolves |
| `REG-DEF-03-NAME` | registries | **PASS** | D-003 name occurs in its module |
| `REG-DEF-04-MODULE` | registries | **PASS** | D-004 module resolves |
| `REG-DEF-04-NAME` | registries | **PASS** | D-004 name occurs in its module |
| `REG-DEF-05-MODULE` | registries | **PASS** | D-005 module resolves |
| `REG-DEF-05-NAME` | registries | **PASS** | D-005 name occurs in its module |
| `REG-DEF-06-MODULE` | registries | **PASS** | D-006 module resolves |
| `REG-DEF-06-NAME` | registries | **PASS** | D-006 name occurs in its module |
| `REG-DEF-07-MODULE` | registries | **PASS** | D-007 module resolves |
| `REG-DEF-07-NAME` | registries | **PASS** | D-007 name occurs in its module |
| `REG-DEF-08-MODULE` | registries | **PASS** | D-008 module resolves |
| `REG-DEF-08-NAME` | registries | **PASS** | D-008 name occurs in its module |
| `REG-DEF-09-MODULE` | registries | **PASS** | D-009 module resolves |
| `REG-DEF-09-NAME` | registries | **PASS** | D-009 name occurs in its module |
| `REG-DEF-10-MODULE` | registries | **PASS** | D-010 module resolves |
| `REG-DEF-10-NAME` | registries | **PASS** | D-010 name occurs in its module |
| `REG-DEF-11-MODULE` | registries | **PASS** | D-011 module resolves |
| `REG-DEF-11-NAME` | registries | **PASS** | D-011 name occurs in its module |
| `REG-DEF-12-MODULE` | registries | **PASS** | D-012 module resolves |
| `REG-DEF-12-NAME` | registries | **PASS** | D-012 name occurs in its module |
| `REG-DEF-13-MODULE` | registries | **PASS** | D-013 module resolves |
| `REG-DEF-13-NAME` | registries | **PASS** | D-013 name occurs in its module |
| `REG-DEF-14-MODULE` | registries | **PASS** | D-014 module resolves |
| `REG-DEF-14-NAME` | registries | **PASS** | D-014 name occurs in its module |
| `REG-DEF-15-MODULE` | registries | **PASS** | D-015 module resolves |
| `REG-DEF-15-NAME` | registries | **PASS** | D-015 name occurs in its module |
| `REG-DEF-16-MODULE` | registries | **PASS** | D-016 module resolves |
| `REG-DEF-16-NAME` | registries | **PASS** | D-016 name occurs in its module |
| `REG-DEF-17-MODULE` | registries | **PASS** | D-017 module resolves |
| `REG-DEF-17-NAME` | registries | **PASS** | D-017 name occurs in its module |
| `REG-DEF-18-MODULE` | registries | **PASS** | D-018 module resolves |
| `REG-DEF-18-NAME` | registries | **PASS** | D-018 name occurs in its module |
| `REG-DEF-19-MODULE` | registries | **PASS** | D-019 module resolves |
| `REG-DEF-19-NAME` | registries | **PASS** | D-019 name occurs in its module |
| `REG-DEF-20-MODULE` | registries | **PASS** | D-020 module resolves |
| `REG-DEF-20-NAME` | registries | **PASS** | D-020 name occurs in its module |
| `REG-DEF-21-MODULE` | registries | **PASS** | D-021 module resolves |
| `REG-DEF-21-NAME` | registries | **PASS** | D-021 name occurs in its module |
| `REG-DEF-22-MODULE` | registries | **PASS** | D-022 module resolves |
| `REG-DEF-22-NAME` | registries | **PASS** | D-022 name occurs in its module |
| `REG-DEF-23-MODULE` | registries | **PASS** | D-023 module resolves |
| `REG-DEF-23-NAME` | registries | **PASS** | D-023 name occurs in its module |
| `REG-DEF-24-MODULE` | registries | **PASS** | D-024 module resolves |
| `REG-DEF-24-NAME` | registries | **PASS** | D-024 name occurs in its module |
| `REG-DEF-25-MODULE` | registries | **PASS** | D-025 module resolves |
| `REG-DEF-25-NAME` | registries | **PASS** | D-025 name occurs in its module |
| `REG-DEF-26-MODULE` | registries | **PASS** | D-026 module resolves |
| `REG-DEF-26-NAME` | registries | **PASS** | D-026 name occurs in its module |
| `REG-DEF-27-MODULE` | registries | **PASS** | D-027 module resolves |
| `REG-DEF-27-NAME` | registries | **PASS** | D-027 name occurs in its module |
| `REG-DEF-28-MODULE` | registries | **PASS** | D-028 module resolves |
| `REG-DEF-28-NAME` | registries | **PASS** | D-028 name occurs in its module |
| `REG-DEF-29-MODULE` | registries | **PASS** | D-029 module resolves |
| `REG-DEF-29-NAME` | registries | **PASS** | D-029 name occurs in its module |
| `REG-DEF-30-MODULE` | registries | **PASS** | D-030 module resolves |
| `REG-DEF-30-NAME` | registries | **PASS** | D-030 name occurs in its module |
| `REG-DEF-31-MODULE` | registries | **PASS** | D-031 module resolves |
| `REG-DEF-31-NAME` | registries | **PASS** | D-031 name occurs in its module |
| `REG-DEF-32-MODULE` | registries | **PASS** | D-032 module resolves |
| `REG-DEF-32-NAME` | registries | **PASS** | D-032 name occurs in its module |
| `REG-DEF-33-MODULE` | registries | **PASS** | D-033 module resolves |
| `REG-DEF-33-NAME` | registries | **PASS** | D-033 name occurs in its module |
| `REG-DEF-34-MODULE` | registries | **PASS** | D-034 module resolves |
| `REG-DEF-34-NAME` | registries | **PASS** | D-034 name occurs in its module |
| `REG-DEF-35-MODULE` | registries | **PASS** | D-035 module resolves |
| `REG-DEF-35-NAME` | registries | **PASS** | D-035 name occurs in its module |
| `REG-DEF-36-MODULE` | registries | **PASS** | D-036 module resolves |
| `REG-DEF-36-NAME` | registries | **PASS** | D-036 name occurs in its module |
| `REG-DEF-37-MODULE` | registries | **PASS** | D-037 module resolves |
| `REG-DEF-37-NAME` | registries | **PASS** | D-037 name occurs in its module |
| `REG-DEF-38-MODULE` | registries | **PASS** | D-038 module resolves |
| `REG-DEF-38-NAME` | registries | **PASS** | D-038 name occurs in its module |
| `REG-DEF-39-MODULE` | registries | **PASS** | D-039 module resolves |
| `REG-DEF-39-NAME` | registries | **PASS** | D-039 name occurs in its module |
| `REG-DEF-40-MODULE` | registries | **PASS** | D-040 module resolves |
| `REG-DEF-40-NAME` | registries | **PASS** | D-040 name occurs in its module |
| `REG-DEF-41-MODULE` | registries | **PASS** | D-041 module resolves |
| `REG-DEF-41-NAME` | registries | **PASS** | D-041 name occurs in its module |
| `REG-DEF-42-MODULE` | registries | **PASS** | D-042 module resolves |
| `REG-DEF-42-NAME` | registries | **PASS** | D-042 name occurs in its module |
| `REG-DEF-43-MODULE` | registries | **PASS** | D-043 module resolves |
| `REG-DEF-43-NAME` | registries | **PASS** | D-043 name occurs in its module |
| `REG-DEF-44-MODULE` | registries | **PASS** | D-044 module resolves |
| `REG-DEF-44-NAME` | registries | **PASS** | D-044 name occurs in its module |
| `REG-DEF-45-MODULE` | registries | **PASS** | D-045 module resolves |
| `REG-DEF-45-NAME` | registries | **PASS** | D-045 name occurs in its module |
| `REG-DEF-46-MODULE` | registries | **PASS** | D-046 module resolves |
| `REG-DEF-46-NAME` | registries | **PASS** | D-046 name occurs in its module |
| `REG-DEF-47-MODULE` | registries | **PASS** | D-047 module resolves |
| `REG-DEF-47-NAME` | registries | **PASS** | D-047 name occurs in its module |
| `REG-DEF-48-MODULE` | registries | **PASS** | D-048 module resolves |
| `REG-DEF-48-NAME` | registries | **PASS** | D-048 name occurs in its module |
| `REG-DEF-49-MODULE` | registries | **PASS** | D-049 module resolves |
| `REG-DEF-49-NAME` | registries | **PASS** | D-049 name occurs in its module |
| `REG-DEF-50-MODULE` | registries | **PASS** | D-050 module resolves |
| `REG-DEF-50-NAME` | registries | **PASS** | D-050 name occurs in its module |
| `REG-DEF-51-MODULE` | registries | **PASS** | D-051 module resolves |
| `REG-DEF-51-NAME` | registries | **PASS** | D-051 name occurs in its module |
| `REG-DEF-52-MODULE` | registries | **PASS** | D-052 module resolves |
| `REG-DEF-52-NAME` | registries | **PASS** | D-052 name occurs in its module |
| `REG-DEF-53-MODULE` | registries | **PASS** | D-053 module resolves |
| `REG-DEF-53-NAME` | registries | **PASS** | D-053 name occurs in its module |
| `REG-DEF-54-MODULE` | registries | **PASS** | D-054 module resolves |
| `REG-DEF-54-NAME` | registries | **PASS** | D-054 name occurs in its module |
| `REG-KILL-01` | registries | **PASS** | K-ARROW-01 was tested and not triggered |
| `REG-KILL-02` | registries | **PASS** | K-PKG-01 was tested and not triggered |
| `REG-KILL-03` | registries | **PASS** | K-PKG-02 was tested and not triggered |
| `REG-KILL-04` | registries | **PASS** | K-ROUTE-01 was tested and not triggered |
| `REG-KILL-05` | registries | **PASS** | K-TRANS-01 was tested and not triggered |
| `REG-KILL-06` | registries | **PASS** | K-TRANS-02 was tested and not triggered |
| `REG-FALLBACK` | registries | **PASS** | Temporal-IAPS fallback remains locked |
| `SCHEMA-COUNT` | schemas | **PASS** | fifteen certificate schemas have fifteen scaffold examples |
| `SCHEMA-01-META` | schemas | **PASS** | ancestry_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-01-EXAMPLE` | schemas | **PASS** | ancestry_certificate.schema.json has one matching scaffold |
| `SCHEMA-01-VALID` | schemas | **PASS** | ancestry_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-01-NONCLAIM` | schemas | **PASS** | ancestry_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-02-META` | schemas | **PASS** | autonomy_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-02-EXAMPLE` | schemas | **PASS** | autonomy_certificate.schema.json has one matching scaffold |
| `SCHEMA-02-VALID` | schemas | **PASS** | autonomy_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-02-NONCLAIM` | schemas | **PASS** | autonomy_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-03-META` | schemas | **PASS** | countermodel_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-03-EXAMPLE` | schemas | **PASS** | countermodel_certificate.schema.json has one matching scaffold |
| `SCHEMA-03-VALID` | schemas | **PASS** | countermodel_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-03-NONCLAIM` | schemas | **PASS** | countermodel_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-04-META` | schemas | **PASS** | direct_successor.schema.json is valid Draft 2020-12 |
| `SCHEMA-04-EXAMPLE` | schemas | **PASS** | direct_successor.schema.json has one matching scaffold |
| `SCHEMA-04-VALID` | schemas | **PASS** | direct_successor.scaffold.json validates: no schema errors |
| `SCHEMA-04-NONCLAIM` | schemas | **PASS** | direct_successor.scaffold.json does not claim landed evidence |
| `SCHEMA-05-META` | schemas | **PASS** | memory_repair_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-05-EXAMPLE` | schemas | **PASS** | memory_repair_certificate.schema.json has one matching scaffold |
| `SCHEMA-05-VALID` | schemas | **PASS** | memory_repair_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-05-NONCLAIM` | schemas | **PASS** | memory_repair_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-06-META` | schemas | **PASS** | package_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-06-EXAMPLE` | schemas | **PASS** | package_certificate.schema.json has one matching scaffold |
| `SCHEMA-06-VALID` | schemas | **PASS** | package_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-06-NONCLAIM` | schemas | **PASS** | package_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-07-META` | schemas | **PASS** | package_control_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-07-EXAMPLE` | schemas | **PASS** | package_control_certificate.schema.json has one matching scaffold |
| `SCHEMA-07-VALID` | schemas | **PASS** | package_control_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-07-NONCLAIM` | schemas | **PASS** | package_control_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-08-META` | schemas | **PASS** | record_arrow_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-08-EXAMPLE` | schemas | **PASS** | record_arrow_certificate.schema.json has one matching scaffold |
| `SCHEMA-08-VALID` | schemas | **PASS** | record_arrow_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-08-NONCLAIM` | schemas | **PASS** | record_arrow_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-09-META` | schemas | **PASS** | route_discipline_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-09-EXAMPLE` | schemas | **PASS** | route_discipline_certificate.schema.json has one matching scaffold |
| `SCHEMA-09-VALID` | schemas | **PASS** | route_discipline_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-09-NONCLAIM` | schemas | **PASS** | route_discipline_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-10-META` | schemas | **PASS** | staged_package_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-10-EXAMPLE` | schemas | **PASS** | staged_package_certificate.schema.json has one matching scaffold |
| `SCHEMA-10-VALID` | schemas | **PASS** | staged_package_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-10-NONCLAIM` | schemas | **PASS** | staged_package_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-11-META` | schemas | **PASS** | temporal_corridor.schema.json is valid Draft 2020-12 |
| `SCHEMA-11-EXAMPLE` | schemas | **PASS** | temporal_corridor.schema.json has one matching scaffold |
| `SCHEMA-11-VALID` | schemas | **PASS** | temporal_corridor.scaffold.json validates: no schema errors |
| `SCHEMA-11-NONCLAIM` | schemas | **PASS** | temporal_corridor.scaffold.json does not claim landed evidence |
| `SCHEMA-12-META` | schemas | **PASS** | temporal_fiach_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-12-EXAMPLE` | schemas | **PASS** | temporal_fiach_certificate.schema.json has one matching scaffold |
| `SCHEMA-12-VALID` | schemas | **PASS** | temporal_fiach_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-12-NONCLAIM` | schemas | **PASS** | temporal_fiach_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-13-META` | schemas | **PASS** | temporal_signature.schema.json is valid Draft 2020-12 |
| `SCHEMA-13-EXAMPLE` | schemas | **PASS** | temporal_signature.schema.json has one matching scaffold |
| `SCHEMA-13-VALID` | schemas | **PASS** | temporal_signature.scaffold.json validates: no schema errors |
| `SCHEMA-13-NONCLAIM` | schemas | **PASS** | temporal_signature.scaffold.json does not claim landed evidence |
| `SCHEMA-14-META` | schemas | **PASS** | temporal_transport_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-14-EXAMPLE` | schemas | **PASS** | temporal_transport_certificate.schema.json has one matching scaffold |
| `SCHEMA-14-VALID` | schemas | **PASS** | temporal_transport_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-14-NONCLAIM` | schemas | **PASS** | temporal_transport_certificate.scaffold.json does not claim landed evidence |
| `SCHEMA-15-META` | schemas | **PASS** | transport_control_certificate.schema.json is valid Draft 2020-12 |
| `SCHEMA-15-EXAMPLE` | schemas | **PASS** | transport_control_certificate.schema.json has one matching scaffold |
| `SCHEMA-15-VALID` | schemas | **PASS** | transport_control_certificate.scaffold.json validates: no schema errors |
| `SCHEMA-15-NONCLAIM` | schemas | **PASS** | transport_control_certificate.scaffold.json does not claim landed evidence |
| `LEAN-01-EXISTS` | lean-static | **PASS** | CSTTT/Transport/FiniteTemporalTransport.lean exists |
| `LEAN-02-EXISTS` | lean-static | **PASS** | CSTTT/Transport/RecordArrow.lean exists |
| `LEAN-03-EXISTS` | lean-static | **PASS** | CSTTT/Transport/RouteDiscipline.lean exists |
| `LEAN-04-EXISTS` | lean-static | **PASS** | CSTTT/Transport/FiniteExamples.lean exists |
| `LEAN-DECL-01` | lean-static | **PASS** | Lean declaration RepresentativeIndependent is present |
| `LEAN-DECL-02` | lean-static | **PASS** | Lean declaration TemporalSignatureAgreement is present |
| `LEAN-DECL-03` | lean-static | **PASS** | Lean declaration FiniteTemporalTransportProof is present |
| `LEAN-DECL-04` | lean-static | **PASS** | Lean declaration bundledHeterogeneousTemporalTransport is present |
| `LEAN-DECL-05` | lean-static | **PASS** | Lean declaration StrictlyMonotoneOn is present |
| `LEAN-DECL-06` | lean-static | **PASS** | Lean declaration monotoneRecordDescentTransportsArrow is present |
| `LEAN-DECL-07` | lean-static | **PASS** | Lean declaration transportRecordArrowStep is present |
| `LEAN-DECL-08` | lean-static | **PASS** | Lean declaration noCurrentOnlyPredictor is present |
| `LEAN-DECL-09` | lean-static | **PASS** | Lean declaration memoryOrFlatness is present |
| `LEAN-DECL-10` | lean-static | **PASS** | Lean declaration noCanonicalGlobalNowOfTranslationHolonomy is present |
| `LEAN-DECL-11` | lean-static | **PASS** | Lean declaration noGlobalNowFactorization is present |
| `LEAN-DECL-12` | lean-static | **PASS** | Lean declaration NormalizationCertificate is present |
| `LEAN-DECL-13` | lean-static | **PASS** | Lean declaration routeIndependentEndpointUnderNormalization is present |
| `LEAN-DECL-14` | lean-static | **PASS** | Lean declaration exactHeterogeneousSignatureAgreement is present |
| `LEAN-DECL-15` | lean-static | **PASS** | Lean declaration exampleConfluentEndpoints is present |
| `LEAN-NOPLACE-001` | lean-static | **PASS** | CSTTT/Autonomy/System.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-002` | lean-static | **PASS** | CSTTT/Core/Carrier.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-003` | lean-static | **PASS** | CSTTT/Core/Episode.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-004` | lean-static | **PASS** | CSTTT/Core/Finite.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-005` | lean-static | **PASS** | CSTTT/Corridor/DirectSuccessor.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-006` | lean-static | **PASS** | CSTTT/Corridor/TemporalCorridor.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-007` | lean-static | **PASS** | CSTTT/Countermodels/Kernel.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-008` | lean-static | **PASS** | CSTTT/Fallback/Ancestry.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-009` | lean-static | **PASS** | CSTTT/Package/Clauses.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-010` | lean-static | **PASS** | CSTTT/Package/FiniteGluing.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-011` | lean-static | **PASS** | CSTTT/Package/Gluing.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-012` | lean-static | **PASS** | CSTTT/Package/TemporalPackage.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-013` | lean-static | **PASS** | CSTTT/Prospects/Statements.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-014` | lean-static | **PASS** | CSTTT/Targets/TemporalFIACH.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-015` | lean-static | **PASS** | CSTTT/Temporal/Clock.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-016` | lean-static | **PASS** | CSTTT/Temporal/Closure.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-017` | lean-static | **PASS** | CSTTT/Temporal/Signature.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-018` | lean-static | **PASS** | CSTTT/Transport/FiniteExamples.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-019` | lean-static | **PASS** | CSTTT/Transport/FiniteTemporalTransport.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-020` | lean-static | **PASS** | CSTTT/Transport/RecordArrow.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-021` | lean-static | **PASS** | CSTTT/Transport/RouteDiscipline.lean contains no unproved placeholder command |
| `LEAN-NOPLACE-022` | lean-static | **PASS** | CSTTT/Transport/TemporalBridge.lean contains no unproved placeholder command |
| `LEAN-CIRCULARITY` | lean-static | **PASS** | primitive Lean tree passes verdict-vocabulary circularity scan |
| `LEAN-LAYER-01` | lean-static | **PASS** | FiniteExamples.lean does not import later verdict layers |
| `LEAN-LAYER-02` | lean-static | **PASS** | FiniteTemporalTransport.lean does not import later verdict layers |
| `LEAN-LAYER-03` | lean-static | **PASS** | RecordArrow.lean does not import later verdict layers |
| `LEAN-LAYER-04` | lean-static | **PASS** | RouteDiscipline.lean does not import later verdict layers |
| `LEAN-LAYER-05` | lean-static | **PASS** | TemporalBridge.lean does not import later verdict layers |
| `LEAN-REG-01` | lean-static | **PASS** | registered theorem declaration acyclicLocalWitnessGluing is present |
| `LEAN-REG-02` | lean-static | **PASS** | registered theorem declaration stagedHeterogeneousPackageAssembly is present |
| `LEAN-REG-03` | lean-static | **PASS** | registered theorem declaration bundledHeterogeneousTemporalTransport is present |
| `LEAN-REG-04` | lean-static | **PASS** | registered theorem declaration TemporalCorridorComposition is present |
| `LEAN-REG-05` | lean-static | **PASS** | registered theorem declaration PostWithdrawalFiniteHorizonInvariance is present |
| `LEAN-REG-06` | lean-static | **PASS** | registered theorem declaration TemporalFIACHCertificateSoundness is present |
| `LEAN-REG-07` | lean-static | **PASS** | registered theorem declaration FullHandoffComposition is present |
| `LEAN-REG-08` | lean-static | **PASS** | registered theorem declaration RelationValuedTemporalFission is present |
| `LEAN-REG-09` | lean-static | **PASS** | registered theorem declaration routeIndependentEndpointUnderNormalization is present |
| `LEAN-REG-10` | lean-static | **PASS** | registered theorem declaration monotoneRecordDescentTransportsArrow is present |
| `LEAN-REG-11` | lean-static | **PASS** | registered theorem declaration DetachedCopyCountermodel is present |
| `LEAN-REG-12` | lean-static | **PASS** | registered theorem declaration PublicShadowCountermodel is present |
| `LEAN-REG-13` | lean-static | **PASS** | registered theorem declaration HolonomyWithoutArrowCountermodel is present |
| `LEAN-REG-14` | lean-static | **PASS** | registered theorem declaration noCurrentOnlyPredictor is present |
| `LEAN-REG-15` | lean-static | **PASS** | registered theorem declaration memoryOrFlatness is present |
| `LEAN-REG-16` | lean-static | **PASS** | registered theorem declaration noCanonicalGlobalNowOfTranslationHolonomy is present |
| `LEAN-REG-17` | lean-static | **PASS** | registered theorem declaration ExternalSupportAutonomyFailure is present |
| `LEAN-REG-18` | lean-static | **PASS** | registered theorem declaration StableTickWithoutProgress is present |
| `LEAN-REG-19` | lean-static | **PASS** | registered theorem declaration LocalGlobalObstruction is present |
| `LEAN-REG-20` | lean-static | **PASS** | registered theorem declaration GapResumeCountermodel is present |
| `LEAN-REG-21` | lean-static | **PASS** | registered theorem declaration ScalarResidualHardGateFailure is present |
| `LEAN-REG-22` | lean-static | **PASS** | registered theorem declaration SymmetryNoUniqueContinuer is present |
| `LEAN-REG-23` | lean-static | **PASS** | registered theorem declaration FiniteTraceNotUnboundedLiveness is present |
| `LEAN-REG-24` | lean-static | **PASS** | registered theorem declaration SameCarrierReencodingNotCrossCarrier is present |
| `LEAN-REG-25` | lean-static | **PASS** | registered theorem declaration BranchwiseRecombinationFailure is present |
| `LEAN-REG-26` | lean-static | **PASS** | registered theorem declaration DirectSuccessorValidity is present |
| `LEAN-REG-27` | lean-static | **PASS** | registered theorem declaration OverlapDirectSuccessorRelation is present |
| `LEAN-REG-28` | lean-static | **PASS** | registered theorem declaration DirectSuccessorDetachedCopyExclusion is present |
| `LEAN-REG-29` | lean-static | **PASS** | registered theorem declaration PredictiveBridgeDescent is present |
| `LEAN-REG-30` | lean-static | **PASS** | registered theorem declaration LeastOperationalAncestry is present |
| `LEAN-REG-31` | lean-static | **PASS** | registered theorem declaration IndependentTwinExclusion is present |
| `LEAN-REG-32` | lean-static | **PASS** | registered theorem declaration FallbackFissionFusionEmpty is present |
| `LEAN-REG-33` | lean-static | **PASS** | registered theorem declaration IntegratedTemporalIAPS is present |
| `LEAN-REG-34` | lean-static | **PASS** | registered theorem declaration DestructiveReconstructionTwinSeparation is present |
| `LEAN-REG-35` | lean-static | **PASS** | registered theorem declaration AncestryNoUniqueIdentity is present |
| `LEAN-REG-36` | lean-static | **PASS** | registered theorem declaration PredictiveAncestryPackageInsufficient is present |
| `LEAN-ROOT-01` | lean-static | **PASS** | root Lean module imports CSTTT.Transport.FiniteTemporalTransport |
| `LEAN-ROOT-02` | lean-static | **PASS** | root Lean module imports CSTTT.Transport.RecordArrow |
| `LEAN-ROOT-03` | lean-static | **PASS** | root Lean module imports CSTTT.Transport.RouteDiscipline |
| `LEAN-ROOT-04` | lean-static | **PASS** | root Lean module imports CSTTT.Transport.FiniteExamples |
| `BOUND-PROJECT-01` | boundaries | **PASS** | project registry phase='CST-TT-03' |
| `BOUND-PROJECT-02` | boundaries | **PASS** | project registry phase_base_tag='CST-TT-02-v1' |
| `BOUND-PROJECT-03` | boundaries | **PASS** | project registry phase_base_commit='3abf5b2406f754b43823b68987c7ea409e737fd0' |
| `BOUND-PROJECT-04` | boundaries | **PASS** | project registry checked_finite_countermodels=15 |
| `BOUND-PROJECT-05` | boundaries | **PASS** | project registry checked_finite_package_witnesses=2 |
| `BOUND-PROJECT-06` | boundaries | **PASS** | project registry checked_staged_package_assemblies=1 |
| `BOUND-PROJECT-07` | boundaries | **PASS** | project registry generic_theorem_proof_sources_landed=8 |
| `BOUND-PROJECT-08` | boundaries | **PASS** | project registry checked_temporal_transport_certificates=2 |
| `BOUND-PROJECT-09` | boundaries | **PASS** | project registry checked_route_certificates=2 |
| `BOUND-PROJECT-10` | boundaries | **PASS** | project registry checked_memory_or_flatness_certificates=2 |
| `BOUND-PROJECT-11` | boundaries | **PASS** | project registry checked_record_arrow_certificates=1 |
| `BOUND-PROJECT-12` | boundaries | **PASS** | project registry checked_transport_and_route_controls=28 |
| `BOUND-PROJECT-13` | boundaries | **PASS** | project registry generic_theorems_lean_compiled=0 |
| `BOUND-PROJECT-14` | boundaries | **PASS** | project registry positive_handoff_witnesses=0 |
| `BOUND-PROJECT-15` | boundaries | **PASS** | project registry fallback_unlocked=False |
| `BOUND-PROJECT-16` | boundaries | **PASS** | project registry next_phase='CST-TT-04' |
| `BOUND-PHASE-01` | boundaries | **PASS** | phase boundary contains 'exact finite C1-C8 package semantics' |
| `BOUND-PHASE-02` | boundaries | **PASS** | phase boundary contains 'substantive C6 temporal closure' |
| `BOUND-PHASE-03` | boundaries | **PASS** | phase boundary contains 'componentwise heterogeneous transport' |
| `BOUND-PHASE-04` | boundaries | **PASS** | phase boundary contains 'representative-independent predictive bridges' |
| `BOUND-PHASE-05` | boundaries | **PASS** | phase boundary contains 'strict record-arrow transport' |
| `BOUND-PHASE-06` | boundaries | **PASS** | phase boundary contains 'memory-or-flatness' |
| `BOUND-PHASE-07` | boundaries | **PASS** | phase boundary contains 'no-global-now factorization theorem' |
| `BOUND-PHASE-08` | boundaries | **PASS** | phase boundary contains 'Not landed' |
| `BOUND-PHASE-09` | boundaries | **PASS** | phase boundary contains 'strict temporal lineage' |
| `BOUND-PHASE-10` | boundaries | **PASS** | phase boundary contains 'post-withdrawal autonomy' |
| `BOUND-PHASE-11` | boundaries | **PASS** | phase boundary contains 'positive Temporal-FIACH or Temporal-IAPS witness' |
| `BOUND-PHASE-12` | boundaries | **PASS** | phase boundary contains 'CST-TT-04' |
| `BOUND-DOC-01-EXISTS` | documentation | **PASS** | docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md exists |
| `BOUND-DOC-01-01` | documentation | **PASS** | docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md contains 'S-T' |
| `BOUND-DOC-01-02` | documentation | **PASS** | docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md contains 'no episode lineage' |
| `BOUND-DOC-01-03` | documentation | **PASS** | docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md contains 'representative' |
| `BOUND-DOC-02-EXISTS` | documentation | **PASS** | docs/MEMORY_OR_FLATNESS_THEOREM.md exists |
| `BOUND-DOC-02-01` | documentation | **PASS** | docs/MEMORY_OR_FLATNESS_THEOREM.md contains 'same current representation' |
| `BOUND-DOC-02-02` | documentation | **PASS** | docs/MEMORY_OR_FLATNESS_THEOREM.md contains 'route residue' |
| `BOUND-DOC-02-03` | documentation | **PASS** | docs/MEMORY_OR_FLATNESS_THEOREM.md contains 'flat' |
| `BOUND-DOC-03-EXISTS` | documentation | **PASS** | docs/ROUTE_DISCIPLINE_AND_CONFLUENCE.md exists |
| `BOUND-DOC-03-01` | documentation | **PASS** | docs/ROUTE_DISCIPLINE_AND_CONFLUENCE.md contains 'holonomy' |
| `BOUND-DOC-03-02` | documentation | **PASS** | docs/ROUTE_DISCIPLINE_AND_CONFLUENCE.md contains 'normal form' |
| `BOUND-DOC-03-03` | documentation | **PASS** | docs/ROUTE_DISCIPLINE_AND_CONFLUENCE.md contains 'boundary-level' |
| `BOUND-DOC-04-EXISTS` | documentation | **PASS** | docs/RECORD_ARROW_TRANSPORT.md exists |
| `BOUND-DOC-04-01` | documentation | **PASS** | docs/RECORD_ARROW_TRANSPORT.md contains 'strict' |
| `BOUND-DOC-04-02` | documentation | **PASS** | docs/RECORD_ARROW_TRANSPORT.md contains 'constant map' |
| `BOUND-DOC-04-03` | documentation | **PASS** | docs/RECORD_ARROW_TRANSPORT.md contains 'arrow' |
| `BOUND-DOC-05-EXISTS` | documentation | **PASS** | docs/TRANSPORT_CONTROL_SUITE.md exists |
| `BOUND-DOC-05-01` | documentation | **PASS** | docs/TRANSPORT_CONTROL_SUITE.md contains '28' |
| `BOUND-DOC-05-02` | documentation | **PASS** | docs/TRANSPORT_CONTROL_SUITE.md contains 'controls' |
| `BOUND-DOC-05-03` | documentation | **PASS** | docs/TRANSPORT_CONTROL_SUITE.md contains 'hash-bound' |
| `BOUND-COMP-01` | boundaries | **PASS** | completion report contains boundary phrase 'No positive temporal corridor' |
| `BOUND-COMP-02` | boundaries | **PASS** | completion report contains boundary phrase 'No post-withdrawal autonomy' |
| `BOUND-COMP-03` | boundaries | **PASS** | completion report contains boundary phrase 'Temporal-IAPS remains locked' |
| `BOUND-COMP-04` | boundaries | **PASS** | completion report contains boundary phrase 'Lean compilation is not claimed' |
| `BOUND-COMP-05` | boundaries | **PASS** | completion report contains boundary phrase 'CST-TT-04' |
| `MAN-001` | manifest | **SKIP** | phase manifest not required before finalization |
