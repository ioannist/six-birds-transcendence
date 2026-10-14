# When a Copy Is Not a Continuation

This repository holds the paper *When a Copy Is Not a Continuation* (Ioannis Tsiokos, 2026) and
the Lean 4 development behind it. The paper is archived on Zenodo:
[doi:10.5281/zenodo.23233188](https://doi.org/10.5281/zenodo.23233188).

- `paper/` holds the manuscript (`paper/main.tex`, built PDF `paper/main.pdf`), its generated data
  and figures, the tools that check it, and the claim and nonclaim ledgers under `paper/prewriting/`.
- `lean/` holds the Lean development (`lean/CSTTT`). It uses Lean 4.28.0 and the core library only.
  The vendored Six Birds tree under `lean/` is not imported.
- `audit/` holds the model specifications, predictions, results and review records of the Lean
  campaign.
- `cst-tt/` holds the registries, design inputs and the superseded Python scaffold that preceded
  the Lean development.
- `scripts/` holds the Lean validator and transcription checks.

Commands and expected results are in `paper/prewriting/reproducibility.md`. The paper's
availability statement lists what was verified and discloses AI assistance; the full account is
`paper/prewriting/ai_assistance_ledger.md`.

## How to cite

Please cite the paper; see `CITATION.cff`.

> Tsiokos, I. (2026). *When a Copy Is Not a Continuation*. Zenodo. https://doi.org/10.5281/zenodo.23233188

## License

Code is under the MIT License, and the manuscript, text, data and figures are under CC BY 4.0.
See `LICENSE` and `LICENSE-CC-BY-4.0`.

## Not in the public release

The public repository is a single commit. It leaves out files a reader does not need. Leaving
them out does not hide how the work was done: AI agents did much of it, as the paper and the
AI-assistance ledger state. The omitted files are:

- agent configuration, prompts, playbooks, memories and session logs;
- review requests sent to reviewers, and their bundles;
- notes addressed to other repositories, and release-state files for the archival record;
- the writing-phase planning files `paper/prewriting/README.md`, `paper_plan.md`,
  `open_issues.md`, `research_brief.md`, `audience_style_study.md`, `related_work.md` and
  `submission_checklist.md`, and the drafting templates under `paper/notes/`;
- two incident notes from the Lean campaign (`audit/CAMPAIGN_RECOVERY_*.md`);
- an exploration bundle that preceded this repository (`prework/`);
- copies of another repository's planning files among the design references;
- two archives used only by the early exploration scripts: a snapshot of another repository and a
  dump of a 60-paper corpus (`cst-tt/inputs/source_archives/six-birds-consciousness_v41.zip`
  and `six_birds_papers_tex.zip`).

Some files still name these as history. The ledgers and planning documents cite the planning
files, and the historical manifests list the two archives. Generated notes that say the
archives are kept under `cst-tt/inputs/source_archives/` describe the working repository. The
scripts that rebuild or validate the early exploration assets (`cst-tt/scripts/rebuild_exp01.sh`,
`validate_exp01.py` and `validate_exp02.py`) need those archives and cannot run from the public
tree. No check listed in `paper/prewriting/reproducibility.md` needs any omitted file.
