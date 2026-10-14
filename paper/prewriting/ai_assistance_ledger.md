# Computational and AI assistance ledger

This is an internal disclosure record, in the format of the consciousness papers' ledger. The
author must adapt the disclosure to the target venue's policy. An AI system is not an author and
bears no responsibility for the paper.

## Entries

| Date | System or tool class | Purpose | Material output | Verification and limits | Disclosure treatment |
|---|---|---|---|---|---|
| 2026-09/10 | OpenAI Codex coding assistants, as implementer and as independent reviewer | Lean 4 formalization of the CST-TT results (CST-TT-09), finite models, transcription checks | `lean/CSTTT` (561+ modules), registries and audits | Lean kernel (standard axioms only); a separate reviewer pass for each packet; the validator; transcription scripts. The kernel checks the Lean statements, not their correspondence to the prose (W18 mathematics pass) | Disclose substantive AI assistance in formalization, if the venue asks or permits |
| 2026-10-13 onward | Claude (Anthropic) as manager and writer; Codex as implementer (tooling, figures) and as independent reviewer | Paper preparation: plan, style rules, claim ledger, reconciliation, literature verification, outline; later drafting of prose | `paper/prewriting/*`, `paper/tools/*`, manuscript | Each packet is reviewed by an independent reviewer model. The author decides the title and approves the readings. Literature metadata is checked against Crossref and publishers; full text was read where recorded in `citation_ledger.csv` | Disclose AI assistance in literature organization, drafting and tooling, as venue policy requires |
| 2026-10-13 | Research sub-agents (Claude) with web, Crossref and the paperclip CLI | Literature verification and corpus provenance relocation | Research notes in `lean/.validate-logs/W5_*` | Reading statuses are recorded honestly; third-party scans are used for verification only and never linked | As above |
| 2026-10-13 | Lean/Lake, Python/pytest | Kernel checking; snapshot export and tests | Build logs, snapshot, tests | Deterministic; counts refreshed at release | Report in the availability statement |

## Prohibited representations

- AI review is not peer review, replication or independent source verification by another
  researcher.
- Reviewer models and sub-agents are not coauthors or multiple independent reviewers.
- Passing Lean checks does not verify any philosophical interpretation.
- This ledger does not by itself satisfy a venue's disclosure policy.
