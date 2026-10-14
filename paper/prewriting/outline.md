# Outline: the continuation paper

Packet W7, 2026-10-13. Section contracts, budgets, claim rows, figures, citations and nonclaim
destinations. This file contains no paper prose. Presentation rules come from
`audience_style_guide.md`; claim ceilings from `claim_ledger.csv`; limits from
`nonclaim_survival.csv`; citations from `literature_claim_crosswalk.csv`.

**Genre.** A formal paper in mathematical consciousness science with one spine and its
boundaries, in the manner of the forcing paper. It is longer, because the spine has three parts
and the boundaries are results too. Model texts are Kleiner and Ludwig 2024 (a formal argument
about substrate questions) and Kleiner and Hoel 2021 (formal argument with an informal version
first). For the identity material, the model is the SEP's even-handed survey style.

**Target length.** 12,000–15,000 words of main text, excluding references, captions and
appendices. Recheck after the first full draft (W17). Substance limits the length; nothing is
padded.

**Venue.** See `open_issues.md` D-06. The default is arXiv (archival), primary q-bio.NC with a
cs.LO cross-list. A journal version is optional later.

## Title (decided by the author, 2026-10-13; D-04)

**When a Copy Is Not a Continuation**

It has the same "When ..." form as the forcing paper. It leads with the question readers already
bring, and names the three checks. The "when" scopes it: a copy fails to be a continuation under
the paper's lineage criterion, which is not a verdict about persons. The subtitle may be adjusted
later. The reserved Zenodo working title ("Structural continuation across carriers: ...") is
superseded; the Zenodo draft has no metadata yet.

## Names fixed for the paper

These are the paper's names. The style guide maps the dialect to them.

| Repository | Paper name |
|---|---|
| Temporal-FIACH certificate soundness (TTH-06-GEN, TTH-06-INST) | **the continuation theorem** (strict continuation) |
| a valid Temporal-FIACH certificate | a continuation certificate |
| F version (package-preserving autonomy) / O version (operational autonomy) | the realization-preserving version / the operational version |
| live overlap handoff; strict temporal corridor | a handoff; a strict handoff chain |
| Temporal-IAPS (TTF-05) | **continuation by ancestry** (the ancestry theorem) |
| POS-04 | the two-copy deadline model |
| G7 native model | the three-system chain model, and its fork |
| FULL-NATIVE-02 | the fusion model |
| target package / integrated package | "the target realizes the eight conditions (as adopted, at stated grades)" |
| temporal signature | the temporal signature (eight fields), defined once |
| route residue | route memory |
| direct successor | direct succession |
| hard gate | a required condition |

## Claim rows by section

### Abstract (200–250 words, written last)
The question; the three questions; the continuation theorem in one sentence; one model computes all
eight conditions jointly under the ancestry criterion; boundaries (copy, gap, fork, route memory,
finite success); what is not claimed (consciousness, identity, survival, Substrate Indifference);
Lean, core library, standard axioms, in one clause.
- **Rows:** DEF-THREE-QUESTIONS, TTH-06-GEN, TTF-05, TTN-01, TTH-08, SCOPE-NO-JOINT-MODEL, HYP-*,
  POST-*.

### 1. Introduction (1,200–1,500)
- **Opening.** Thought experiments about copying, teleporting and gradual replacement ask whether
  the result is the same subject (Parfit 1984; Chalmers 2010; Cerullo 2015). We ask a prior,
  structural question that can be settled exactly. When the organization described by the closure
  architecture (companion paper) is moved to a different finite system:
  - what has to hold for the target to realize it;
  - what has to hold for the episode to be a continuation rather than a copy;
  - what has to hold for the target to carry on alone?
- **The main result in plain words.** The three questions are checked separately. Each question gets its own check. In the operational version of the theorem the three conclusions are logically independent. In the package-preserving version, autonomy includes realization by construction, so it implies realization. A certificate that
  checks them separately is sound. Finite models pass it, and finite countermodels show that each
  part is needed.
- **Informal argument,** numbered (P1)…(C), for why endpoint similarity cannot decide continuation:
  the detached copy and the gap.
- **Scope paragraph** (all of `intro-scope` in `nonclaim_survival.csv`): finite systems with
  unbounded histories; structural only; no consciousness, identity, survival or substrate claim;
  no single model has both strict lineage and all eight conditions at design grade.
- **Contributions** (four):
  - the three questions as checked predicates and the continuation theorem;
  - the boundaries as finite countermodels;
  - relation-valued branching and the no-selector result;
  - one model computing all eight conditions jointly, with continuation by ancestry.
- **Roadmap.**
- **Rows:** DEF-THREE-QUESTIONS, TTH-06-GEN, TTN-01, TTN-09, TTH-08, TTF-05, SCOPE-CLOSURE,
  SCOPE-NO-JOINT-MODEL, HYP-FELT, HYP-CONT, POST-*.
- **Figure:** F1 (the three questions, schematic).

### 2. Setting, and how to read our claims (800–1,000)
- Finite physical factors, unbounded histories (DEF-FINITE).
- The eight conditions recalled in one table, citing the companion, with the grade vocabulary:
  design grade and simplified form (DEF-CONDITIONS).
- The temporal signature (DEF-SIGNATURE).
- The claim-reading convention, stated once (DEF-READING).
- The informal-word policy: transfer, upload, survival.
- Lean and the trust base, in two sentences (ART-LEAN).
- **Table:** T1 (the eight conditions and the grade at which each holds on each model).

### 3. A copy that is not a continuation: a worked example (800–1,000)
- The two-copy deadline model in pictures: source, target, the handoff, withdrawal.
- The detached copy (TTN-01), the gap (TTN-09), same-system re-encoding (TTN-13) and the public
  shadow (TTN-02), each as a small variation of the same picture.
- **Rows:** TTN-01, TTN-09, TTN-13, TTN-02.
- **Figure:** F2 (handoff versus detached copy versus gap, side by side).

### 4. Three questions, three checks (1,600–2,000)
- **4.1 Realization on the target.**
  - Acyclic gluing (TTH-01; Beeri et al. Theorem 3.4 as precursor).
  - Staged assembly (TTH-02).
  - The cyclic obstruction (TTN-08), worded as a running-intersection failure.
- **4.2 Lineage.**
  - Handoffs and strict chains (TTH-04).
  - Signature transport, in its two statements (TTH-03).
  - The record arrow (TTH-10).
- **4.3 Autonomy after withdrawal.**
  - The finite-horizon theorem and its derived instance (TTH-05).
  - An essential withdrawn resource (TTN-06).
  - Finite success is not unbounded maintenance (TTN-12; Bertsekas as a methodological comparison; Alpern and Schneider for the safety/liveness terms).
- **Rows:** TTH-01, TTH-02, TTN-08, TTH-04, TTH-03, TTH-10, TTH-05, TTN-06, TTN-12, TTN-07,
  TTN-10.
- **Figure:** F3 (acyclic cover versus the cycle with a non-adjacent shared cell).

### 5. The continuation theorem (1,400–1,700)
- Informal statement, then the formal statement with hypotheses and conclusion only (TTH-06-GEN).
- The F and O versions explained after the theorem.
- The instance on the two-copy model (TTH-06-INST).
- The three-system chain (TTH-07).
- What the theorem does not give: realization is not lineage; strict lineage is not identity.
- **Rows:** TTH-06-GEN, TTH-06-INST, TTH-07, plus nonclaims `at-result:strict`.
- **Figure:** F4 (the three-system chain 17→55→101 with its handoffs, values from the snapshot).

### 6. Which route? Memory, holonomy and the present (700–900)
- Current-equal but predictively unequal histories (TTN-04).
- Licences that let route memory be dropped (TTH-09, sufficiency only; Newman; Baader and
  Nipkow).
- Holonomy without an arrow (TTN-03).
- No canonical global present (TTN-05).
- **Rows:** TTN-04, TTH-09, TTN-03, TTN-05.
- **Figure:** F5 (the mod-2 clock loop).

### 7. One source, two continuers (1,100–1,400)
- Relation-valued fission on the chain model's fork (TTH-08).
- Exact symmetry and no invariant unique continuer (TTN-11).
- Ancestry underdetermines identity (TTF-07, repaired form).
- Branchwise preservation is not recombination (TTN-14).
- Comparison with closest-continuer theory, multiple occupancy and Cerullo, from the crosswalk
  only.
- **Rows:** TTH-08, TTN-11, TTF-07, TTN-14.
- **Figure:** F6 (the fork 17→{201, 202} and the swap).

### 8. Continuation by ancestry, on a model that computes all eight conditions (1,200–1,500)
- **Ancestry.** Predictive descent (TTF-01); least ancestry with no ancestry from nothing (TTF-02);
  the independent twin (TTF-03); reconstruction versus twin (TTF-06); ancestry does not give
  realization (TTF-08).
- **The fusion model.** Guarded fusion and empty outcomes (TTF-04). The ancestry theorem (TTF-05),
  with the two adopted readings stated plainly where they apply, the acquisition boundary, and the
  checkpoint caveat.
- The memo's ruling 1 sentence, verbatim in substance (`overlap_memo.md` §1.2).
- **Rows:** TTF-01, TTF-02, TTF-03, TTF-06, TTF-08, TTF-04, TTF-05, SCOPE-NO-JOINT-MODEL.
- **Figure:** F7 (fission, acquisition, guarded fusion, with checkpoints marked).

### 9. Other modes, and how far the results reach (700–900)
- Direct succession as a separate, incomparable mode (TTD-01, TTD-02, TTD-03, TTS-01).
- Unbounded maintenance on a finite factor with event registers (TTS-04).
- Exact defect semantics and the rational box (TTS-02, TTS-03).
- **Rows:** TTD-01, TTD-02, TTD-03, TTS-01, TTS-04, TTS-02, TTS-03.

### 10. Objections and replies (1,000–1,300)
Each objection is stated in the objector's terms; destinations are `objections` in the nonclaim
file. Candidate objections:
1. "This is just Parfit's fission case in new notation." Reply: the comparison per the crosswalk;
   what is proved, and what is not.
2. "A perfect copy is a continuation." Reply: under which predicate; endpoint versus lineage; no
   identity verdict.
3. "Your models are tiny; nothing scales." Reply: the finite and unbounded split; Lean; scope.
4. "You have shown consciousness can be uploaded." Reply: no. HYP and POST rows; Substrate
   Indifference stays a postulate.
5. "The adopted readings make the ancestry result easy." Reply: what each reading replaces and
   why; the obstruction that motivated it.
6. "Certificate passing is not soundness." Reply: agreed; AS-30 is open.
7. "Identity is what matters, not structure." Reply: we do not claim otherwise.

### 11. Related work (900–1,100)
Positioning contract from `related_work.md` §1–4. A one-sentence pointer to the Six Birds
appendix.

### 12. Conclusion and limitations (500–700)
All `limitations` rows, stated once, plus open problems:
- a model with strict lineage and all eight conditions at design grade;
- certificate soundness;
- robustness beyond the declared disturbance classes.

### Data and code availability (back matter)
Repository, snapshot, commit and DOI placeholders; Lean scope and counts (W19); `ART-LEAN`.

### Appendices (not counted)
- **A. The Six Birds framework behind this paper.** Marked as a Six Birds section. Corpus
  provenance from `sibling_import_map.csv` (W6), with scope warnings.
- **B. The finite models in full:** the two-copy deadline model, the three-system chain model,
  the fusion model, and the small controls.
- **C. Result-to-Lean index:** every result name, its registry row, its declarations and axioms.
  The only place for TTH/TTN/TTF/TTD/TTS labels.
- **D. Proof sketches and supplementary results:** JOINT-COND, the repairs table from
  `source_reconciliation.md` §3, and the F/O detail.
- **E. Reproducibility:** commands and counts.

## Figure and table summary

Details are in `figure_table_plan.md`. F1 (three questions), F2 (handoff/copy/gap), F3
(gluing), F4 (chain), F5 (clock loop), F6 (fork), F7 (fusion model), and T1 (conditions by
model). Values in F4–F7 and T1 come from `paper/data/current_results.json` through generated
macros.

## Budget check

Section budgets (abstract excluded):

| Section | Words |
|---|---|
| 1 | 1,200–1,500 |
| 2 | 800–1,000 |
| 3 | 800–1,000 |
| 4 | 1,600–2,000 |
| 5 | 1,400–1,700 |
| 6 | 700–900 |
| 7 | 1,100–1,400 |
| 8 | 1,200–1,500 |
| 9 | 700–900 |
| 10 | 1,000–1,300 |
| 11 | 900–1,100 |
| 12 | 500–700 |
| **Total** | **11,900–15,000** |

The target is 12,000–15,000. That is close to the architecture paper's 12,000–16,000, and it fits
an archival arXiv paper with no word limit. Sections 4 and 9 give way first if the draft runs long.
The figure for the first draft is rechecked in W17.
