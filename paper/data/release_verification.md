# W19 release verification (generated)
Generated from static inputs and actual command receipts. Overall recorded status: **FAIL**.
A successful counts-generator check confirms reproducibility of the record; it does not turn failed commands into passes.
When a full log is present, the checker re-extracts its metrics and summary and checks the log hash. An exported archive normally omits ignored logs: its check uses the recorded summary only, and explicitly reports the summary-only receipt IDs. This fallback does not rerun the original commands.
| Count | Value | Classification / source |
|---|---|---|
| Registry | 39 rows: 25 proved / 14 checked finite countermodel / 0 open | static: `cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv` |
| Inventory declarations | 4628 entries; 4586 unique | static: `lean/row_inventory.json` |
| CSTTT modules | 562 under directory; 563 including root | static: `lean/CSTTT/**/*.lean` |
| Lean build jobs | 799 | run-recorded: `lean_build` receipt |
| Paper headline declarations | 82 | static: `paper/prewriting/lean_declaration_map.csv` |
| Headline axiom union | Classical.choice, Quot.sound, propext | static: fresh-probed declaration map |
| Model specification files | 15 | static: Distinct audit/proposed_models/*.model.json files named by model_files in either evidence map. This counts specification files, not distinct raw worlds; finite physical factors may have unbounded histories. |
| Lean toolchain | `leanprover/lean4:v4.28.0` | static: `lean/lean-toolchain` |
| cst_tt | 6 failed, 130 passed | run-recorded receipt |
| paper | 205 passed | run-recorded receipt |
| selftest_evaluate_fiach_pos04 | 0 failed, 37 passed | run-recorded receipt |
| selftest_evaluate_tth06_lanes | 0 failed, 46 passed | run-recorded receipt |
| selftest_evaluate_tth09_routes | 0 failed, 34 passed | run-recorded receipt |
| selftest_validate_lean | 17 passed | run-recorded receipt |

## Retained failed attempts

- `cst_tt`: the configured legacy CST-TT suite has 6 pre-existing failures, also reported at `ba3e5dd`. They concern raw-text vocabulary/placeholder scans, a historical import-layer restriction, two references to the retired countermodel kernel, and historical-builder idempotence. They are not all scaffold scans. Historical generated assets rewritten by that test were restored byte-for-byte.
- `cst_tt_initial_setup`: an unconfigured pytest invocation failed during collection because `tt07a_data` was not on `PYTHONPATH`. The configured `cst_tt` invocation supplies `PYTHONPATH=src:scripts` and is the test-count source. The initial collection attempt remains FAIL; it is not another suite of completed test cases.

## Exact verification commands

| ID | Command (cwd; environment) | Recorded UTC | Result | Log SHA256 |
|---|---|---|---|---|
| archive_reproduction | `python3 paper/tools/check_archive_reproduction.py` (cwd `.`; `{}`) | 2026-10-14T13:22:49+00:00 | PASS | `2ddb4cec9c943ab71fd71748f619285c2c1604d208acdd02173cc5641678506c` |
| check_corridor_transcription | `python3 scripts/check_corridor_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:33:59+00:00 | PASS | `ce59e3b339c3b2de4d8e99f0eeff1399b65bf719701dbcdea38c54bd98500908` |
| check_full_native_02_autonomy_transcription | `python3 scripts/check_full_native_02_autonomy_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:07+00:00 | PASS | `50a984c5c5b6040650f644ff79a71f59eda127c3f6e0481fc3021b4d8640b5ae` |
| check_full_native_02_fusion_transcription | `python3 scripts/check_full_native_02_fusion_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:09+00:00 | PASS | `b26186ab8a61568f1a7da5f6fa72b546fdf5169bd133df76c80665e7c621f483` |
| check_full_native_binding_transcription | `python3 scripts/check_full_native_binding_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:11+00:00 | PASS | `ea15883fd8efc77a307b02e39e6f944d1ac524aca4cf8197ee507799b3909ce1` |
| check_full_native_countermodels_transcription | `python3 scripts/check_full_native_countermodels_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:14+00:00 | PASS | `ac4d91a8e2512be3e62048e9a59c015fcb801b780fc5d369bac68979abb84205` |
| check_full_native_credit_transcription | `python3 scripts/check_full_native_credit_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:15+00:00 | PASS | `363dca2c47aa9d96ec235ce718b311769b6276e9338bdfd4e64dff5af8153fdc` |
| check_full_native_execution_transcription | `python3 scripts/check_full_native_execution_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:17+00:00 | PASS | `0975486d90ab0de36dc183429da8b6ab2b2ebd14cb8c274664b403da556c621a` |
| check_full_native_iaps_transcription | `python3 scripts/check_full_native_iaps_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:19+00:00 | PASS | `0652d27808a2a19a19bd3d3bd690c1452db6bafd76177318e0ed64e0460f17e1` |
| check_full_native_objecthood_transcription | `python3 scripts/check_full_native_objecthood_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:21+00:00 | PASS | `9bf70ca43b122b5a2b44a79fdb032bbd6265011b927d1419acebeb77e97cde38` |
| check_full_native_package_transcription | `python3 scripts/check_full_native_package_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:24+00:00 | PASS | `74a028519280f1e41ba0ba601521f4042d5fc87a4fa2547b66b7f877e0cd7012` |
| check_full_native_snapshot_transcription | `python3 scripts/check_full_native_snapshot_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:26+00:00 | PASS | `7a6c08b6343ed157e1d615ddefcfc63ce19fa4cb3d670ce7c77978ec4f061390` |
| check_full_native_transcription | `python3 scripts/check_full_native_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:28+00:00 | PASS | `67ca3f9169bf11c391c951ee230a81fcbeb3bd26367dc29f088fdf1951152a82` |
| check_full_native_viability_transcription | `python3 scripts/check_full_native_viability_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:30+00:00 | PASS | `0e383c358b8ef65d921a6464db856bacb78081feea87393da0ce540c3d3ccee4` |
| check_global_package_composition_transcription | `python3 scripts/check_global_package_composition_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:31+00:00 | PASS | `bf4d9849f9155ada919de180473beccf09f513cf06f626b4d522dd1a220f466c` |
| check_internalized_receipts_transcription | `python3 scripts/check_internalized_receipts_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:33+00:00 | PASS | `cb5618edb8268e2c32af7798e97cac45a10242e7c16b1b64766ece99c7b6bb18` |
| check_joint_temporal_transcription | `python3 scripts/check_joint_temporal_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:36+00:00 | PASS | `785b57d674c7f73cded998830b87a60b7b39759700d8c179f6413eea5848d0f3` |
| check_native_fission_transcription | `python3 scripts/check_native_fission_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:38+00:00 | PASS | `5cd52e3b3b439c3ae873fc618bd806fe9cb5029f259a813727e558e2372b9628` |
| check_native_publication_composition_transcription | `python3 scripts/check_native_publication_composition_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:40+00:00 | PASS | `501e446cb3dad9273a2cf46f1409f4ac8a4aafcbdce8318ae29058deb7de2f28` |
| check_pos04_transcription | `python3 scripts/check_pos04_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:41+00:00 | PASS | `3d1b03261aa0b8adacac0fe014125dcb900ad2ae9cffc8a17e42ae52742453d1` |
| check_raw_corridor_sequence_transcription | `python3 scripts/check_raw_corridor_sequence_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:43+00:00 | PASS | `c6c3ae2d8dc1f383fc9e42a9eaea32f016bddf1af0f430d43f537e6120a416c2` |
| check_raw_direct_bridge | `python3 scripts/check_raw_direct_bridge.py` (cwd `.`; `{}`) | 2026-10-13T11:34:47+00:00 | PASS | `f4cc0fdb3f7f01c0863c7b7321e103037e0d4f87185e68b3159cce205111cc89` |
| check_receiver_sequence_transcription | `python3 scripts/check_receiver_sequence_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:48+00:00 | PASS | `8ebbb82659c47e55bddf0065a50a9481a37c73ac42eeb89f0b5d28cd44c31da9` |
| check_register_bridge_composition_transcription | `python3 scripts/check_register_bridge_composition_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:50+00:00 | PASS | `9aab7dbfeeb967178c961110ee2aced0fde4ea45c8981cf79525f63536740ce0` |
| check_stage_composition_transcription | `python3 scripts/check_stage_composition_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:51+00:00 | PASS | `10b4f1e5846f7142a8f23e198ad2cfb673c8f546970fe18fc735c3496c6053d5` |
| check_staged_assignment_span_transcription | `python3 scripts/check_staged_assignment_span_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:52+00:00 | PASS | `a04bf771ff62a6e86d8ef6794c637e7a4506e9f75fe2214090ff29d68c8a405e` |
| check_supported_acquisition_sequence_transcription | `python3 scripts/check_supported_acquisition_sequence_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:34:54+00:00 | PASS | `67080a5e78cdd0e8f3e2dd9146e6086eebda6c3c0df410a55d6eb7f1a81ea463` |
| check_t1_transcription | `python3 scripts/check_t1_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:35:01+00:00 | PASS | `126553cca21d19d62a7dc3cae09808e6b8a0f192aef2e3b04bf6249521b506a2` |
| check_tth06_transcription | `python3 scripts/check_tth06_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:35:15+00:00 | PASS | `98fa9572a596ec528a05d54fc00fb9c5faaac98db56dbcf68aac49986eb70aff` |
| check_tth09_transcription | `python3 scripts/check_tth09_transcription.py` (cwd `.`; `{}`) | 2026-10-13T11:35:16+00:00 | PASS | `ae6ab0f60a93dc0db1a2a611ea787a83c1a50478cd573031c6a2f2e6e2052240` |
| corpus_doi_live | `python3 paper/tools/verify_corpus_dois.py` (cwd `.`; `{}`) | 2026-10-13T12:12:35+00:00 | PASS | `e441a7144ac56c7bb902a6f393f3dc68364848805fbaef88a9f41770e9636c4e` |
| correspondence | `python3 paper/tools/build_correspondence.py --check` (cwd `.`; `{}`) | 2026-10-14T10:58:11+00:00 | PASS | `35539874788aaae6e8c6bb3a786ac85a0ad36904beeae9f8fd0f8dc679fb1c66` |
| cst_tt | `python3 -m pytest -o addopts= -q -p no:cacheprovider` (cwd `cst-tt`; `{'PYTHONHASHSEED': '0', 'PYTHONPATH': 'src:scripts'}`) | 2026-10-13T11:37:34+00:00 | FAIL | `a0e701e24f488ccf2de334bd6600c4db0fc335aa164d1aca0dfd94b26fd03df8` |
| cst_tt_initial_setup | `python3 -m pytest -q` (cwd `cst-tt`; `{}`) | 2026-10-13T11:18:17+00:00 | FAIL | `4fc59bb7c9c0bba4f34d07c0ef9bd912f78975b95fb4919edce06587a40c5167` |
| evidence_map | `python3 paper/tools/build_evidence_map.py` (cwd `.`; `{}`) | 2026-10-14T10:29:26+00:00 | PASS | `0993f86dd2d83029b4413391a8d1c280fa67c29bc9125e01673b3d3684cac989` |
| figure_data | `python3 paper/tools/render_figure_data.py` (cwd `.`; `{}`) | 2026-10-14T10:35:54+00:00 | PASS | `03648d315502b8cef2c74478b02658af80607ae06d0d98cb27bfeda049552ab0` |
| import_map | `python3 paper/tools/build_import_map.py --check` (cwd `.`; `{}`) | 2026-10-13T13:09:01+00:00 | PASS | `fb9c4b9af11b0b28fcf2273c1859683f317a4e2770478f1b83e00ae7e0c32eb5` |
| import_map_live | `python3 paper/tools/build_import_map.py --live --check` (cwd `.`; `{}`) | 2026-10-13T13:09:15+00:00 | PASS | `fb9c4b9af11b0b28fcf2273c1859683f317a4e2770478f1b83e00ae7e0c32eb5` |
| index | `python3 paper/tools/render_index.py --check` (cwd `.`; `{}`) | 2026-10-14T10:57:30+00:00 | PASS | `6e5cd52e6886f0d5c647077227fc7c868eb475808764bff73fa04c74ee16cfd7` |
| lean_build | `lake build` (cwd `lean`; `{}`) | 2026-10-13T11:33:58+00:00 | PASS | `0b8f3fa33c97639c5f37db472b7f7bbbf27a600fe9c3b440db388e4040fdd5bb` |
| lean_clean | `lake clean` (cwd `lean`; `{}`) | 2026-10-13T11:33:58+00:00 | PASS | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| lean_validation | `scripts/validate_lean.sh` (cwd `.`; `{}`) | 2026-10-13T11:36:11+00:00 | PASS | `77d41eb81a035fe0d93476ca4f3b04a57886c49c394dbce360ba66bcd51d825a` |
| manuscript_build | `latexmk` (cwd `paper`; `{}`) | 2026-10-13T11:59:05+00:00 | PASS | `e8f30721e50dac0decbb9e5ac9678679d80006f0a4ba159b1d02e09aa6a131c0` |
| manuscript_build_final | `latexmk` (cwd `paper`; `{}`) | 2026-10-14T12:19:48+00:00 | PASS | `d62997f9a70878557c43646b7b6aed03f40fdde510369b7b7470dc83b7c263a7` |
| manuscript_check | `python3 paper/tools/check_manuscript.py` (cwd `.`; `{}`) | 2026-10-14T13:22:49+00:00 | PASS | `cc383554a84d57a6365fdec716b00e4d9935bb22941a60033143f0a43eb3a2cd` |
| manuscript_clean | `latexmk -C` (cwd `paper`; `{}`) | 2026-10-13T11:58:59+00:00 | PASS | `a7f1bfc37e500a6c01479c278ac2b269d75bee7d2a9e482e94e5f995d1be6ec6` |
| package_validator | `python3 paper/prewriting/validate_package.py` (cwd `.`; `{}`) | 2026-10-14T13:22:49+00:00 | PASS | `c9c698f276f14109c8e9a1deeb157bfd0a00b457fa6c3ff7cfd75a5f935337ec` |
| paper | `python3 -m pytest -q paper/tests` (cwd `.`; `{}`) | 2026-10-14T13:26:15+00:00 | PASS | `5d55edbd8ea0cc4dd0a1eb1a83c43dd56e08faf597f6f74301649be78e225ac3` |
| pdf_readout | `python3 -c import hashlib,json,re,subprocess; from pathlib import Path; paths=('paper/build/main.pdf','paper/main.pdf'); hashes={p:hashlib.md5(Path(p).read_bytes()).hexdigest() for p in paths}; pages=int(re.search(r'^Pages:\s+(\d+)',subprocess.check_output(['pdfinfo',paths[1]],text=True),re.M)[1]); print(json.dumps({'pages':pages,'md5':hashes},sort_keys=True)); assert len(set(hashes.values()))==1` (cwd `.`; `{}`) | 2026-10-14T12:23:35+00:00 | PASS | `7396154c76bf53b8811e314618fb693cdd2bc597e287a3c3b9cb45539801b061` |
| result_snapshot | `python3 paper/tools/export_results.py` (cwd `.`; `{}`) | 2026-10-14T10:35:54+00:00 | PASS | `66261b389ba59f1ef55bdd4bf3d929db79ccdeb3fa6efe91ea29c27dcdf00ef8` |
| selftest_evaluate_fiach_pos04 | `python3 scripts/selftest_evaluate_fiach_pos04.py` (cwd `.`; `{}`) | 2026-10-13T11:35:19+00:00 | PASS | `acc6e330ec9c9138dd1b1a032963c2efa2dfa5b2f5d56a17275b7e1338ad4c1e` |
| selftest_evaluate_tth06_lanes | `python3 scripts/selftest_evaluate_tth06_lanes.py` (cwd `.`; `{}`) | 2026-10-13T11:35:26+00:00 | PASS | `0f67e7d2ba9a048c30380cb890c937b733ba3a811de7b96b2669110262009c7d` |
| selftest_evaluate_tth09_routes | `python3 scripts/selftest_evaluate_tth09_routes.py` (cwd `.`; `{}`) | 2026-10-13T11:35:26+00:00 | PASS | `2ad8ec6913dcde9c1d21a8e6fb303c6b54fd3708891f5fd996b87ce5035fb3a9` |
| selftest_validate_lean | `python3 scripts/selftest_validate_lean.py` (cwd `.`; `{}`) | 2026-10-13T11:58:46+00:00 | PASS | `1dd49ac9ca86da894f7ae5b272365e3f27f3941384eed054e893d34b13685d4c` |
| style_lint | `python3 paper/tools/style_lint.py --strict` (cwd `.`; `{}`) | 2026-10-14T12:19:46+00:00 | PASS | `7affb4685f97559ea918249a392e2af7ce11ab02562bf9eefe5e00d77546a9c6` |

## Reported failing test cases

- `FAILED tests/test_circularity_and_lean_surface.py::test_primitive_lean_tree_passes_verdict_vocabulary_scan`
- `FAILED tests/test_circularity_and_lean_surface.py::test_lean_scaffold_has_no_unproved_placeholder_commands`
- `FAILED tests/test_circularity_and_lean_surface.py::test_primitive_import_graph_does_not_reverse_layers`
- `FAILED tests/test_circularity_and_lean_surface.py::test_countermodel_kernel_has_all_certificate_declarations_and_no_verdict_primitives`
- `FAILED tests/test_countermodel_certificates.py::test_every_countermodel_certificate_validates_and_binds_exact_model`
- `FAILED tests/test_generated_assets.py::test_builder_is_idempotent_in_place - ...`
