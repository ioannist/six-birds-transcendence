# Audience style guide

Adopted 2026-10-13 for this paper (`paper_plan.md`, W1).

**Where it comes from.** This guide is the consciousness project's `audience_style_guide.md`
(sibling commit 41de532), carried over for the same readers, mathematical and theoretical
consciousness science. The evidence for it is `audience_style_study.md`, copied unchanged; that study is a working file and is not in the public release. The
audience analysis is not repeated. Sections 1 and 3 to 9 keep the sibling's rules. Section 2 keeps
the sibling's vocabulary table and adds this repository's dialect. Section 10 adds the words that
carry philosophical weight in this paper, and Section 11 lists the rules that stay in force.

**Intentional adaptations of the sibling guide:**
- The sibling's "both papers" and "Paper A / Paper B" rules apply here to one paper.
- The claim-reading convention is stated once in the setting section. The sibling used one
  paragraph in Paper A and one subsection in Paper B.
- The linter also measures abstracts and captions. The sibling added abstracts only in its final
  pass.
- Section 10 is new.
- Section 11 adds one narrow exception to the sibling's scope ban, for the literature's thought
  experiments.

The sibling's rows that name its own results (T-labels, "certificate for T17") are replaced by
this paper's equivalents.

**What it governs.** This guide covers presentation only. Claim strength is governed by
`claim_ledger.csv` (W2) and the claim-verb rules recorded with it. No sentence may be stronger than
its ledger row. Where this guide and the ledger conflict on claim strength, the ledger wins.

## 1. Voice

- Write in the first person plural: "we prove", "we show", "we propose", "we conjecture", "we do not
  know". The authors make the argument, and the paper is never the grammatical agent.
- Allowed: "In this paper we…", "Here we show…". Not allowed: "This paper presents…", "The paper
  establishes…".
- Address the reader directly when it helps: "the reader may object that…", "note that…".
- State the limit of a result once, in plain words, where it matters most. Do not repeat it.

## 2. Vocabulary

Use the field's words. Repository dialect belongs in the result-to-Lean appendix only.

**Inherited from the consciousness papers:**

| Repository dialect | Write instead |
|---|---|
| carrier; source carrier; target carrier | the system; the source system; the target system; a different system |
| declared (as an adjective on every object) | drop it, or use "specified", "given" or "fixed" once where it carries meaning |
| landed; lands | proved; computed; established |
| exact finite study | exact computation; exhaustive enumeration; a finite check in Lean |
| audit; audited | check; verified (keep "audit" only for a named audit the paper defines, such as a credit audit, if one is retained) |
| audit contract | specification |
| C-package; clause C1…C8 | the closure architecture; the eight conditions; condition (1)…(8) or its name |
| T1…T18 and the consciousness papers' result labels | the result's name in the companion paper, cited |
| Tier S / R / O; grade; lane; lane markers | stated once as the claim-reading convention in the setting section |
| witness (for an example) | example; instance; pair of states |
| split pair | pair of states the public description cannot tell apart |
| CORE | define once or avoid |
| nonclaim; packet; ledger; verdict; registry | never in prose |
| promotion; theory package; gate panel | Six Birds sections only (see below) |

**Added for this repository.** Replacing a word must never strengthen a claim. Where the dialect
encodes a grade or a distinction, the replacement must keep it.

| Repository dialect | Write instead |
|---|---|
| package; integrated package; C1–C8-shaped package | Wording follows the claim ledger's grade for each condition. Say "the target meets the eight conditions" or "realizes the architecture" only for rows whose ledger entry licenses all eight at full grade. Where some conditions hold only in a weaker, stand-in form (repository: "C4–C7 surrogate grades"), say so in words, for example "meets conditions (1)–(3) and (8) as stated, and conditions (4)–(7) in the simplified form of Section X". Never let the shorter phrase cover the weaker grade. |
| Temporal-FIACH; FIACH | The strict result: realization on a distinct target, continuation through live-overlap handoffs with no gap, and autonomy after withdrawal. It gets its own name, fixed in the outline (W7), and is never merged with the ancestry-based result below. |
| Temporal-IAPS; IAPS | The ancestry-based result: predictive ancestry in place of strict live-overlap lineage, plus realization and autonomy. It gets a separate name (W7). The prose must say that its lineage requirement is weaker than the strict result's. |
| TTH-, TTN-, TTF-, TTD-, TTS-, TTM- labels; AS-, PKG-, CM- labels | the result's name; labels appear only in the result-to-Lean appendix |
| CST-TT-0x; G-numbers; FULL-NATIVE; FULL-NATIVE-02; POS-04; ROM; Accept02 | the model's plain description ("the finite handoff model"); appendix only |
| corridor | a chain of handoffs; an overlap chain |
| toy; toy model | a small example; a finite example; the model |
| hard gate; gate | a required condition; a test |
| certificate | prefer the theorem's conditions in words; if a finite check object is meant, define "certificate" once and use it consistently |
| lane; claim ceiling; surrogate grade; row; receipt | never in prose; the claim-reading convention is stated once in the setting |
| target-native; target-owned; owned | "maintained by the target itself"; "the target's own" |
| route residue | route memory; "which route the system came by" |
| A2-P | Substrate Indifference (a postulate of the architecture paper), named in words |
| H-FELT-TIME; H-CONT-TIME | the two interpretive hypotheses, named in words and marked as hypotheses |
| SBT; Six Birds law labels; corpus acronyms | Six Birds sections only |

**Six Birds placement (author rule carried from the consciousness papers).**
- Six Birds stays in the paper, but only in dedicated Six Birds sections.
- Each such section is marked by the comment `% style-lint: six-birds-section` as its first line.
- Inside those sections, corpus vocabulary may be used with the corpus's own definitions. That
  covers the six roles, promotion, theory packages, gate panels, closure deficits, and corpus paper
  names and acronyms.
- Everywhere else, the primary audience must be able to read the paper without that vocabulary. A
  plain pointer sentence naming the framework and pointing to the dedicated section is allowed.
- The denylist does not apply inside marked sections.

**Kept, because the audience already uses these words:**
- finite system, state, lens (observation map), quotient, partition, refinement, policy;
- viability kernel, controlled invariance, observational and predictive equivalence, factorization,
  fixed point, gluing, cover;
- simulation, path dependence, holonomy (defined at first use);
- handoff, overlap, withdrawal, lineage, branching, fission, fusion.

## 3. Theorems, definitions, proofs

- A theorem environment contains hypotheses and conclusion only. It holds no grade marker, scope
  clause, control list, assumptions label, or nonclaim.
- Put the informal version first ("In words: …"), then the formal statement, then what it means.
- Connect results with narrative, for example "This is shown by the following lemma" or "The force
  of the argument comes from…".
- Proofs are proofs or proof sketches. A sketch carries a pointer to the Lean declaration in the
  appendix index.
- A finite check is described by what was checked, how, and in what arithmetic.
- Number theorems conventionally (Theorem 1, Lemma 2). Give the main theorem a name.

## 4. Scope, limits, objections

- The claim-reading convention is explained once, in the setting section. It separates structural
  results proved in Lean, finite countermodels, and interpretive hypotheses.
- Every sentence that passes from a structural result to an interpretive reading carries a
  plain-language qualifier in the same sentence or the next. Examples: "we propose, as a reading
  and not a result, that…"; "if one grants the hypothesis that…, then…".
- A question-led heading never answers its question by itself. The text says which parts of the
  answer are theorems and which are proposals.
- One scope paragraph in the introduction says what the paper shows and does not show.
- One section titled "Objections and replies", near the end, states the strongest objections in
  the objector's own terms and answers each one.
- Limitations appear once, in the conclusion or in a short section just before it.
- Captions describe the figure. A caption has at most one scope sentence, and only when the figure
  could otherwise be misread.
- Every nonclaim in `nonclaim_survival.csv` (W2) must land at the destination recorded there.

## 5. Teaching

- Each main result gets an informal statement and, where possible, a numbered informal argument
  (premises, then conclusion) before the formal version.
- Each main result gets at least one worked example on a small case, in prose or in a figure.
- Prefer one concrete picture over three abstract sentences.

## 6. Structure and headings

- Introductions open with the scientific question, not with methodology. State the main result in
  plain words within the first page.
- Headings are descriptive, or questions, for example "Is a perfect copy a continuation?",
  "Objections and replies".
- No meta-headings, such as "Contribution map", "Reader's map", or "Result blocks".
- A short roadmap paragraph at the end of the introduction is fine.

## 7. Sentences and punctuation

- Mean sentence length is at most 26 words per section.
- Use at most about one semicolon per paragraph. Otherwise use two sentences or a list.
- Colons introduce lists or definitions, not clauses.
- Hedge honestly. "We conjecture", "it may be" and "we expect" are allowed for things that are
  genuinely uncertain and are not claims. They never replace a proved statement or weaken a ledger
  claim.

## 8. Front and back matter

- **Front matter:** title, author, abstract, keywords. No artifact note, repository paths, test
  counts, or build details.
- **Back matter:** a "Data and code availability" statement. It gives the repository, the
  snapshot, a commit and DOI placeholder, the Lean scope, and the counts of declarations, models,
  tests and Lean build jobs. Test and build counts appear only there. Acknowledgments, disclosures
  and references follow.
- **Citations:** author-year (natbib `authoryear`, `\citet` and `\citep`).

## 9. Measurable targets (enforced by the style linter)

These are per 1,000 words of prose, measured per section and for the whole paper. Abstracts and
captions are measured too. One exception: captions are exempt from the first-person minimum,
because they describe figures (decided 2026-10-13, W14). Every other target and the denylist
still apply to captions.

| Measure | Target |
|---|---|
| we / our / us | at least 6 |
| "this paper / the paper / this article" as subject | at most 0.7 |
| semicolons | at most 9 |
| colons (outside math and lists) | at most 12 |
| mean words per sentence | at most 26 |
| result labels, model codes, and denylisted dialect terms in prose | 0 |

The denylist lives in `style_denylist.txt`: one regular expression per line, with a comment giving
the replacement. The result-to-Lean appendix and the marked Six Birds sections are exempt.

## 10. Words with philosophical weight

The paper's subject sits next to personal identity and survival, so these words are rationed.

- **"identity", "numerical identity", "survival", "the same subject", "the same person".** Use them
  only in three places: when stating what the results do not show, in Objections and replies, and
  in related work when reporting others' views. Never use them as, or inside, the conclusion of a
  result.
- **"transcend", "transcendence".** These are the project's name, not the audience's word. Use them
  in the Six Birds section only. The title and body use "continuation" or "continuing onto a
  different system". The denylist enforces this.
- **"consciousness", "experience", "felt continuity".** These are the subject matter. They may name
  the question the paper is about. A sentence may never say that a result establishes them. Any
  link from a structural result to experience goes through a named, marked hypothesis.
- **"copy", "upload", "transfer".** Use these for the scenarios the paper discusses. Say "copy" only
  where the detached-copy contrast is meant.

## 11. Unchanged rules

- No biological mechanism, and no engineered system, AI or LLM offered as an example or as subject
  matter of our results. No "neural" or "neurophenomenal".
- One narrow exception for this paper's topic. When related work or Objections and replies reports
  the literature's thought experiments, we may describe them in their authors' terms: gradual
  replacement, uploading, teleportation, branching. Examples are Parfit's teletransporter and
  Chalmers' gradual uploading. We never claim that our finite models represent a brain, a machine,
  or any physical substrate.
- `To_Chat_a_Stone` is never cited.
- No hand-typed numbers in computed figures or tables. Every value is traceable to the snapshot or
  to a Lean declaration.
