# Overlap and cross-paper consistency memo

Packet W6, 2026-10-13. This is a control memo, not paper prose. It fixes what this paper (the
continuation paper) owns and what it borrows. It also states what the paper says about two open
items in its companions, and lists the companion sentences it makes stale or sharper. Those
sentences go to the author in an untracked update note at the root of `../six-birds-consciousness`.
The sibling repository is not edited from here.

## Governing rule

- Each result belongs to the paper that proves it. This paper proves the CST-TT-09 rows
  (`claim_ledger.csv`).
- It borrows two things:
  - **From the architecture paper** (`TsiokosArchitecture2026`): the eight conditions and the
    realization postulates.
  - **From the forcing paper** (`TsiokosForcing2026`): the deadline system from which the two-copy
    handoff model is built.
- Borrowed objects are cited and recalled briefly, not re-proved.
- Six Birds corpus sources (`sibling_import_map.csv`) are provenance. They are cited only in the
  dedicated Six Birds section and are never evidence for a result here.

## 1. The architecture paper

### 1.1 What it says that this paper touches

| Architecture paper (sibling `paper/`, build/paper at 754f83f) | Location |
|---|---|
| Definition: a candidate satisfies the architecture when it meets the eight conditions "jointly and on one system, together with coherence data ... and a full panel of the checks that each condition requires." | `sections/sec_03_architecture.tex`, Definition `def:cpackage` |
| "The evidence for different conditions comes from different small systems, and no integrated instance that meets all eight has been exhibited." | Table `tbl:cpackage` caption; also intro l. 63, l. 76; Fig. F2 caption |
| Condition (4) is relative to the given channels: "Hiddenness is relative to the channels by construction." | `def:cpackage` (4) |
| Substrate Indifference (A2) is a postulate, with "no transport or invariance theorem for it". Open problem: "Formalize Substrate Indifference as a transport theorem over systems, or retire it to a purely philosophical status." | `sec_06_realization.tex` l. 22–31, l. 106; `sec_10_conclusion.tex` l. 39, l. 56 |
| The open integrated instance (T17-I): "Future integrated finite instance satisfying a full design/02 C-package certificate together with a proved certificate-soundness theorem." | `formalization/inventory/t17_claim_registry.yml`, T17-I |
| Identity as predictive lineage (T14), on one specified memory wheel. Continuation maps classify as fiber-splitting or fiber-merging. | `sec_05d_persistence.tex`, `thm:t14` |
| Two gates for combination (T15): joint strict recombination and joint reflexivity. Aggregation fails binding. | `sec_05d_persistence.tex`, `thm:t15` |

### 1.2 Ruling on the integrated instance

**Facts** (`source_reconciliation.md` §4; ledger TTF-05; `audit/G27_full_native_package.md:9-50`;
`audit/G30_full_native_02_preregistration.md:115-125`):

- On FULL-NATIVE-02, all eight conditions are computed from **one installed execution** of one
  designed model. The model has a finite physical factor (32 states; 64 with charge) and unbounded
  execution histories and registers. Cross-clause coherence comes from that execution. No clause gets an independently
  supplied witness. They are computed at the design interfaces fixed in advance by the G17/G30
  preregistrations, the "original P05 prose C1–C8 design contract". P05 is the corpus version of
  the architecture paper. The disclosed differences are:
  - **(4)** is non-exposure for the current family of observations on maintained support. The
    architecture's own definition makes (4) channel-relative, so this is a stated channel choice,
    not a weakening of the definition. It is not privacy against future public observations.
  - **(5) and (6)** use the first reading the author approved on 2026-10-12: completed local
    directional cycles with continuously authenticated residency. This is a designed successor,
    not the original admission rule.
  - **(1)** has its stationarity, retention and defect checks on the finite physical matrix.
    Growing history records are excluded from stationarity, and a stronger two-step uniqueness gate
    fails, with a period-two counterexample kept on record.
- FULL-NATIVE-01 (G27) is the earlier **checkpoint** package on the same physical rows. Its
  successors fail the old admission rule (G29). It is not the persistent-admission construction of
  G30/G31b, which carries TTF-05.
- Nothing in either repository checks these instances against the sibling's **full design/02
  FIII gate panel** (`design/02_ARCHITECTURE.md`, the C-package definition). Shared provenance
  across clauses does not discharge that panel. No certificate-soundness theorem exists anywhere
  (AS-30 is open).

**Ruling:**

1. This paper may say: *"We exhibit one designed model, with a finite physical factor and unbounded
   execution histories, on which the eight conditions, as adopted at interfaces fixed in advance,
   are computed jointly from a single execution, with the stated choices for conditions (1), (4),
   (5) and (6). This is not a certificate for the full architecture, whose complete panel of checks
   we do not verify."* The ledger row is TTF-05. The phrase "meets the architecture" is never used.
2. This paper may **not** say that the architecture's integrated instance in the sense of T17-I
   exists. T17-I also requires the full design/02 certificate and a certificate-soundness theorem,
   and neither is supplied. It may not say "an integrated instance has been exhibited" without the
   qualifications in (1).
3. The strict-continuation instances (POS-04, G7 native) meet conditions (4)–(7) only in simplified
   form. They are never described as instances of the architecture.
4. **Consequence for the architecture paper.** Its sentence "the evidence for different conditions
   comes from different small systems" is now incomplete. Its sentence "no integrated instance that
   meets all eight has been exhibited" is still true in its own T17-I sense, but needs a pointer to
   (1). See the update note.

### 1.3 Ruling on Substrate Indifference

- This paper proves structural transport between distinct finite systems:
  - typed, value-preserving maps assemble a realization on the target (TTH-02);
  - the eight frozen fields of the temporal signature are transported exactly on the declared
    checked frontier, and the transported readouts are sufficient for futures of every length
    (TTH-03; two separate statements);
  - a certificate yields realization, lineage and autonomy (TTH-06).
- These are theorems about **finite systems of different types**, not about substrates. The
  charter forbids presenting them as A2 or formalizing A2 by quantifying over system types
  (`cst-tt/charter/PROJECT_CHARTER.md:61,69`; `NONGOALS_AND_SCOPE_GUARDS.md` §1.8, G10-A2).
- **Ruling.** Substrate Indifference remains a postulate, and this paper says so (ledger POST-A2).
  The structural transport results are separate results about finite systems. The architecture
  paper's open problem, formalizing Substrate Indifference as a transport theorem or retiring it,
  remains unresolved. This paper must not say or imply that the problem is addressed, partly
  addressed, or made more plausible.

### 1.4 Identity and combination

- **T14 (identity as predictive lineage)** concerns one specified memory wheel. Fiber-splitting
  with duplicated support is its own classification. This paper's results sharpen it across systems
  and do not contradict it:
  - continuation is relation-valued under symmetric fission (TTH-08, TTN-11);
  - ancestry alone underdetermines identity (TTF-07, repaired form).

  The update note proposes one sentence for the architecture paper: under fission, lineage is a
  relation, so lineage alone gives no unique identity verdict.
- **T15 (two gates for combination)** and this paper's guarded fusion (TTF-04) and recombination
  countermodel (TTN-14) are consistent. TTN-14, where branchwise preservation does not preserve the
  joint coupling, is the across-systems analogue of "aggregation fails binding". The guarded fusion
  is relation-valued and claims nothing about a joint subject.

## 2. The forcing paper

The two-copy handoff model (POS-04) uses two tagged copies of the forcing paper's ten-state
deadline system. This paper cites the forcing paper for that system and for the substantive grade
of conditions (1)–(3) on it. No forcing claim is restated or re-proved. Nothing in the forcing
paper becomes stale.

## 3. The Six Birds corpus

- The 19 statement-level sources in `cst-tt/registries/FINAL_SBT_PROVENANCE.csv` are mapped,
  version-pinned and line-checked in `sibling_import_map.csv` (Cody, W6).
- They appear only in the dedicated Six Birds section, with their own scope warnings. Each scope
  warning says that the source is fixed-support, conditional, or an analogy, and that it does not
  prove transfer or identity.
- **The corpus has been revised since the design froze** (`import_relocation.csv`, W6 follow-up,
  2026-10-13). Each statement was compared text to text between the snapshot the design read
  (`cst-tt/inputs/reference_surfaces/`, sha256-matched) and the current files. The result: 4 are
  the same, 5 are reworded with the same content, 10 changed, and none was removed. Three changes
  are material:
  - **P53-M001 (time):** the arrow is redefined as path-reversal divergence. A stationary monotone
    ledger is now called trivial, and arrows are credited to the dynamics, not to packaging.
  - **P57-M003 (agents):** zero defect is no longer credited to repair; objecthood evidence comes
    from viability.
  - **P14-S006 (holonomy):** the clause "current transport iff flat" is removed.

  **Ruling:**
  - The Six Birds appendix cites what the design drew on, the snapshot versions with hashes, and
    states which statements later changed.
  - No result in this paper depends on any corpus statement; each stands on its own Lean proof.
  - Because of P53-M001, the body must say that our record arrow (TTH-10, condition (6)'s arrow
    on the simplified-grade models) is a structural ordering by record growth, not a
    path-reversal or thermodynamic arrow. A nonclaim is added.
- The corpus version of the architecture paper (P05) is distinct from the companion
  `TsiokosArchitecture2026`. The Six Birds section cites P05 only for the design contract the
  preregistrations froze, and the body cites the companion.

## 4. What the update note contains

The note is a file at `../six-birds-consciousness/UPDATE_NOTE_from_continuation_paper.md`,
untracked. For each item it gives the sibling location, the current wording, the proposed wording,
the evidence (claim-ledger row and Lean declaration), and whether the change is required, meaning
the sentence is now incomplete or misleading, or optional. It covers §1.2(4), §1.3, §1.4, and a
citation to the continuation paper. It also covers the sibling's `paper/sections/sec_09_related_work.tex:106-109`.
There, "cannot until a transport theorem exists on our side" is ambiguous beside this paper's
structural transport theorems. The proposed wording is "until a substrate-invariance theorem
establishing the required realization bridge exists", without suggesting that this paper supplies
one. It is written after this memo is reviewed, so it carries the
reviewed rulings.
