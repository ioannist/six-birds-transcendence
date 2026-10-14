# Claim-Type System

## 1. Why a project-specific system is needed

The attached consciousness work separates structural (`S`), recognition (`R`), ontological (`O`), and open claims. CST-EXP retains that discipline but refines structural claims into transport, target-package, lineage, and autonomy lanes. This prevents a mathematically valid transport result from being paraphrased as target realization or personal survival.

## 2. Primary claim tags

| Tag | Claim object | Licensed form | Does not license |
|---|---|---|---|
| `S-T` | structural transport | a typed object/invariant maps or is preserved across declared carriers under a bridge | target C-package, lineage, consciousness, autonomy |
| `S-R` | target realization structure | the target carrier satisfies declared structural clauses/coherence gates | source-target identity, empirical recognition, phenomenal realization |
| `S-L` | lineage/continuity structure | a declared relation classifies the source-target historical relation | uniqueness, target package, ontological identity unless separately proved |
| `A` | post-handoff autonomy | the target maintains declared structure after a specified intervention for a horizon/closure condition | total environmental independence, consciousness, lineage |
| `R` | recognition/empirical correspondence | observations are proposed as evidence for a structural predicate | derivation of the predicate or ontological conclusion |
| `O` | ontological/phenomenal reading | a conclusion follows after explicitly named assumptions | detaching the conclusion from certificate soundness/A1/A2 or other premises |
| `M` | methodology or analogy | a source supplies a design pattern, warning, or engineering analogy | proof of any S/R/O claim |

An `OPEN` marker is a **result status**, not a claim tag. Machine-readable records may use the namespaced aliases `CST:S-T`, `CST:S-R`, `CST:S-L`, `CST:A`, `CST:R`, `CST:O`, and `CST:M`; the unprefixed forms are canonical in prose.

## 3. Claim atomization rule

Every claim record has exactly one primary tag. Secondary tags are permitted only when the statement explicitly asserts and supports a cross-lane implication. In prose, prefer separate sentences and separate records.

Bad:

> The bridge preserves the mind, so the target is the same conscious person and survives independently.

Required decomposition:

1. `S-T`: the bridge preserves named predictive/closure structures.
2. `S-R`: the target satisfies named C-package clauses and gates.
3. `S-L`: under criterion `κ`, the target is a successor/branch/etc.
4. `A`: after intervention `J`, the target maintains the package.
5. `O`: assuming the named soundness and ontological premises, the structural package receives a phenomenal reading.

No record may hide steps 2–5 inside the verb “preserves.”

## 4. Result status

| Status | Meaning | Minimum support |
|---|---|---|
| `DEFINITION` | stipulated typed object or predicate | noncircularity and compatibility audit |
| `EXACT_THEOREM` | proved result on declared hypotheses/carriers | proof with scoped dependencies |
| `FINITE_ENUMERATION` | exhaustive exact computation on declared finite carrier | reproducible enumeration and controls |
| `CONDITIONAL_SCHEMA` | implication with hypotheses not all discharged | visible assumptions and no unconditional wording |
| `CONJECTURE` | candidate proposition | motivating examples, falsifier, dependencies |
| `COUNTEREXAMPLE` | witness refuting a stated candidate/generalization | explicit construction and violated conclusion |
| `OPEN_TARGET` | desired but unlanded object/result | explicit missing obligations |
| `ANALOGY` | structural comparison | similarities and disanalogies |
| `METHODOLOGICAL_RULE` | workflow/typing constraint | rationale and enforcement location |
| `REJECTED_CANDIDATE` | candidate removed from contention | preserved reason and scope of rejection |

## 5. Evidence fields

Every claim record must state:

- exact statement;
- primary tag and status;
- carrier/interface/route scope;
- assumptions;
- evidence type;
- source provenance;
- bridge from premises to conclusion;
- falsifier or failure condition;
- blocked inferences; and
- nonclaims.

The authoritative schema is `ledgers/claim_register_template.csv`.

## 6. Cross-tag implication rules

| Proposed implication | Default | What would be needed |
|---|---|---|
| `S-T → S-R` | blocked | theorem that preserved object suffices for every named target clause/gate |
| `S-T → S-L` | blocked | declared lineage criterion and theorem connecting transport to it |
| `S-R → S-L` | blocked | historical/source relation; independent target realization is possible |
| `S-L → S-R` | blocked | theorem that the lineage criterion preserves or entails package realization |
| `S-R → A` | blocked | intervention and maintenance theorem |
| `A → S-L` | blocked | autonomy concerns target maintenance, not ancestry |
| `S-* → R` | blocked | empirical bridge with identifiability/error analysis |
| `S-* → O` | blocked | certificate soundness and named ontological premises |
| `R → O` | blocked | recognition evidence does not itself settle ontology |
| `M → S-*` | blocked | analogy must be converted into definitions and proof obligations |

## 7. Multi-tag permission

A record may carry a secondary tag only when all of the following are present:

1. the premise and conclusion are individually stateable;
2. the connecting implication is the object of the claim;
3. the evidence supports the implication rather than merely both endpoints;
4. assumptions are listed at the implication boundary; and
5. the record states which reverse implication is not claimed.

Example: an exact theorem that a particular recovery-assisted bridge preserves all C1–C8 predicates could be primary `S-T`, secondary `S-R`. It still would not receive `S-L`, `A`, or `O` automatically.

## 8. Licensed and prohibited verbs

### Licensed with declared scope

- `S-T`: maps, transports, preserves, intertwines, factors, simulates, isomorphic with respect to `F`.
- `S-R`: satisfies, structurally instantiates, passes gate, maintains clause.
- `S-L`: is a `κ`-successor, branches to, fuses from, has no successor, is underdetermined.
- `A`: remains, maintains, repairs endogenously after intervention `J` for horizon `h`.
- `R`: proposes, operationalizes, estimates, treats as evidence, recognizes conditionally.
- `O`: implies after assuming, is interpreted as under `Ω`, purchases.
- `M`: suggests, supplies an analogy, warns, offers a template.

### Prohibited unqualified verbs

`is the same consciousness`, `survives`, `moves`, `uploads`, `awakens`, `transcends`, `is merely a copy`, `dies`, `resurrects`, `becomes conscious`, `proves substrate independence`.

They may be used only after translation into tagged claims, or in clearly marked informal framing.

## 9. Claim decision tree

1. Is the conclusion only about declared mathematical objects? If no, go to 5.
2. Does it compare source and target carriers? Use `S-T`.
3. Does it concern target clause/gate satisfaction? Use `S-R`.
4. Does it classify source-target ancestry/history or target maintenance after removal? Use `S-L` or `A` respectively.
5. Does it map observations or familiar categories to structure? Use `R`.
6. Does it state what the structure would be phenomenally/ontologically? Use `O` and list premises.
7. Is it only a design lesson or analogy? Use `M`.
8. Is the result unlanded? Add status `OPEN_TARGET`; do not change its tag.

## 10. Minimal examples

| Claim | Tag | Status |
|---|---|---|
| “Under bridge `B`, predictive quotient transitions commute exactly.” | S-T | conjecture or exact theorem, depending support |
| “The target passes C1, C3, C6, and C8 but not C4.” | S-R | finite enumeration |
| “Symmetric duplication yields two equal `κ`-successors and no unique successor.” | S-L | conjecture/counterexample/theorem |
| “After removing the source and decoder, the target maintains the viability kernel for all admissible continuations.” | A | conjecture/theorem |
| “Perturbational responsiveness is proposed as evidence for endogenous target maintenance.” | R | conditional schema |
| “Assuming certificate soundness and A1, full certificate satisfaction counts as realization.” | O | conditional schema |
| “Logical error correction is an engineering analogy for higher-layer persistence.” | M | analogy |
