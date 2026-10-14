# Reproducibility and artifact-release plan

Packet W7, 2026-10-13; counts refreshed in W19 from the fresh run of 2026-10-13, and in W20 (2026-10-14) after the Figure 1 redesign. The authoritative
counts are generated in `paper/data/release_counts.json` (macros in `paper/includes/release_counts.tex`),
and `paper/data/release_verification.md` lists every command run, its result, date and log hash.

## What a reader must be able to rerun

| Check | Command (from the repository root) | Expected |
|---|---|---|
| Lean build | `cd lean && lake build` | success; Lean 4.28.0; core only |
| Lean validation | `scripts/validate_lean.sh` | 39 rows; exact inventory; 0 issues, 0 placeholders, 0 untrusted axioms |
| TTH-06 transcription | `python3 scripts/check_tth06_transcription.py` | pass |
| Paper evidence map | `python3 paper/tools/build_evidence_map.py --check` | no drift; 0 unresolved names |
| Paper snapshot | `python3 paper/tools/export_results.py --check` | no drift; every value pinned |
| Corpus import map | `python3 paper/tools/build_import_map.py --check` | no drift |
| Paper tests | `python3 -m pytest -q paper/tests` | all pass (204 at W20) |
| Release counts | `python3 paper/tools/build_release_counts.py --check` | no drift |
| Archive reproduction | `python3 paper/tools/check_archive_reproduction.py` | the checks and paper tests pass in a `.git`-free export with no sibling repositories (record: `paper/data/archive_reproduction.json`) |
| Corpus DOIs (network) | `python3 paper/tools/verify_corpus_dois.py` | 7 published records |
| Package validator | `python3 paper/prewriting/validate_package.py` (W7/W8) | 0 errors |
| Manuscript | `cd paper && latexmk` | 0 errors, 0 undefined references, 0 overfull boxes |

Python 3.12.3 with pytest 9.0.3 and jsonschema 4.10.3: these are the versions present and verified on 2026-10-13. A reproducer should create a local virtual environment with exactly these versions (`python3 -m venv .venv && .venv/bin/pip install pytest==9.0.3 jsonschema==4.10.3`). Nothing is installed globally. The Lean toolchain is pinned by `lean/lean-toolchain`.

## Superseded scaffold suite

`cst-tt/` keeps the test suite of the Python scaffold that preceded the Lean development
(`cd cst-tt && PYTHONHASHSEED=0 PYTHONPATH=src:scripts python3 -m pytest -o addopts= -q -p no:cacheprovider`).
At W19, 130 pass and 6 fail, and the same holds on an export of the public tree (W20). The same 6 fail at the Lean-close commit `ba3e5dd`, checked in a scratch
worktree on 2026-10-13. They scan the superseded `cst-tt/CSTTT` scaffold (vocabulary and placeholder
scans, an import-layer rule, the retired countermodel kernel) and test a historical builder's
idempotence. No paper result depends on that scaffold. Running the suite rewrites five historical files
in place, so restore those five paths afterwards (`git status` lists them). The availability statement discloses
the failures.

## Trust boundary

- The kernel checks the Lean statements. Standard axioms only (`lean/trust_base.txt`).
- CSTTT imports only `Init`, `Lean` and `Std`. The vendored Six Birds tree is not imported. That
  tree contains the non-standard axiom `hiddenness_pending`, and no CSTTT declaration depends on
  it.
- Agreement between the paper's prose and the Lean statements is not a kernel fact. It is checked
  by the W18 mathematics pass, a review by the reviewer model (AI assistance, disclosed in the paper), and
  recorded in `statement_correspondence.md` and the W18 commit.
- Every computed value in figures and tables comes from the snapshot, and each value is pinned to a
  named theorem. The stage and callout numbers of the schematic Figure 1 are labels, not values; the
  manuscript checker admits only those four ordinals, only in that figure.

## Release bundle (W19)

The release bundle includes:
- a `git archive` of the release commit;
- the built PDF, checked to be identical to `paper/build/main.pdf` (md5 and page count);
- the external review request, sent to reviewers separately (it is not in the public repository).
- refreshed counts in the availability statement and here.

Publication of the Zenodo record and any push are the author's actions.

The public repository leaves out files a reader does not need. The root `README.md` lists them.
No check in the table above needs any of them.
