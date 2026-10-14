# Execution Plan: Temporal Substrate Transcendence Theorems and Toy Models

**Project code:** `CST-TT`  
**Starting state:** frozen `CST-EXP-06-v1` repository plus the temporal-transcendence audit  
**Primary target:** Temporal-FIACH, interpreted as continuous realization of an integrated package's internally generated time across distinct carriers  
**Fallback target:** Temporal-IAPS, interpreted as source-derived temporal successorship when uninterrupted temporal realization cannot be established  
**Mandatory companion:** exact finite no-go and boundary suite  
**Scope:** theorem development, Lean formalization, exact finite toy programs, certificates, countermodels, and reproducibility assets. No manuscript drafting and no full Six Birds simulation.

## 1. Program objective

Land the strongest noncircular finite result supported by the exploration:

```text
TemporalFIACH_e(s,t) :=
  DistinctCarrier(S,T)
  ∧ SourcePkg(S,s)
  ∧ IntegratedPkg(T,t,e)
  ∧ TemporalCorridor(S,T,e,s,t)
  ∧ Autonomous(T,e,D,K)
```

where `TemporalCorridor` is defined independently of the final handoff verdict and audits:

- future-sufficient `PredictiveNow`;
- an internally represented successor/order relation;
- tick phase **and progress**, so stalling cannot masquerade as stability;
- an endogenous monotone record/arrow;
- route memory or a proved flatness/confluence condition;
- transfer of clock, ledger, drive, memory, and repair ownership;
- no externally narrated or externally scheduled temporal step;
- a declared no-gap continuity condition for the strong class.

The result must return target realization (`S-R`), lineage (`S-L`), autonomy (`A`), and route status as separate fields. It must not prove or assume consciousness, phenomenal continuity, personal survival, numerical identity, A1, A2-P, certificate soundness, or empirical recognition.

## 2. Execution and snapshot protocol

Every phase is executed from the ZIP returned by the immediately preceding phase. Each phase must:

1. restore and verify the previous Git tag and repository checksum;
2. work inside the inherited repository, preserving history;
3. commit all source, theorem, model, test, certificate, and status changes;
4. run the phase validator, all inherited tests, Python tests, and the available Lean build;
5. record every failure or unproved target honestly in a theorem-status ledger;
6. create a deterministic manifest and SHA-256 list;
7. tag the result `CST-TT-XX-v1` or the applicable branch tag;
8. return a full portable repository ZIP, including `.git`, but excluding disposable build caches;
9. return a completion report and validation report alongside the ZIP.

Canonical ZIP naming:

```text
CST-TT-XX_cst-temporal-transcendence_repo.zip
```

The repository must always include `RESTORE_AND_VERIFY.md`, the exact toolchain lockfiles, fixed random/enumeration seeds, and one-command rebuild/test scripts. Python may discover witnesses and emit certificates; Lean defines the semantics and checks the certificates. Python output alone is never called a proof.

## 3. Phase sequence

### CST-TT-00 — Repository bootstrap and temporal target freeze

**Purpose:** convert the exploratory target into an executable, noncircular formal contract before proving anything positive.

**Work:**

- Restore `CST-EXP-06-v1` and import the temporal audit as frozen provenance.
- Create the theorem/toy source layout, for example:

```text
formal/lean/CST/...
toy/cst_tt/...
models/{positive,negative,boundary}/...
certificates/...
theorems/...
docs/science/...
manifests/...
```

- Pin Lean, Lake/Mathlib if used, Python, and package versions; land smoke builds.
- Freeze exact finite types for carriers, local states, histories, episodes, support ownership, events, routes, clocks, records, disturbances, and certificates.
- Freeze independent predicates for:
  - the eight C-shaped package clauses;
  - `TemporalClosure`;
  - `PredictiveNow`;
  - target ownership;
  - withdrawal and autonomy;
  - overlap-based `TemporalCorridor`;
  - a separately named provisional direct-successor predicate;
  - fallback ancestry, without implementing it yet.
- Reconcile the frozen FIACH theorem family with the temporal amendments. Preserve the existing PTH/FTH provenance IDs and create an explicit temporal amendment map.
- Freeze the complete primary/common toy registry: the ten temporal models plus local/global, public-shadow, and scalar-hard-gate controls.
- Freeze theorem dependencies, certificate schemas, kill criteria, claim ceilings, and the primary/fallback/no-go branch policy.
- Add circularity linting: no field or premise may mention FIACH, continuation, same subject, survival, or the desired final verdict.

**Exit gate:** the definitions and theorem statements type-check at scaffold level; every theorem and toy has a machine-readable contract; no positive witness has yet been tuned to make the target pass.

**ZIP:** `CST-TT-00_cst-temporal-transcendence_repo.zip`.

---

### CST-TT-01 — Negative kernel and minimal countermodels

**Purpose:** freeze the ways a proposed theory can fail before optimizing the positive construction.

**Required exact countermodels and boundaries:**

1. endpoint/snapshot equality without temporal continuation;
2. detached exact temporal copy;
3. holonomy without an endogenous arrow;
4. externally scheduled or decoder-maintained temporal shadow;
5. tick stability without progress;
6. current-equal but predictively different routes: memory-or-flatness boundary;
7. nonzero time-translation holonomy: no global canonical `now`;
8. local clause success without one global package witness;
9. public/report-perfect collision with hidden predictive or package mismatch;
10. small aggregate residual hiding a failed hard gate;
11. exact symmetric fork with no invariant unique selector;
12. temporal gap followed by an equivalent resumed stream;
13. finite successful trace without an indefinite-liveness conclusion;
14. same-carrier re-encoding as a negative cross-carrier control.

**Programs and proofs:**

- Build the deterministic bounded counterexample enumerator first.
- Emit canonical JSON or equivalent model certificates with minimality data.
- Define small Lean checkers and prove/check each explicit witness.
- Prove generic nonidentifiability or insufficiency lemmas where the finite model class supports them; otherwise retain exact checked countermodels with precise scope.
- Freeze the countermodels so later definitions may not be post hoc altered merely to erase them.

**Exit gate:** every required negative model is reproducible and Lean-checkable; bounded search has established the stated minimality claim or recorded the exact search bound; no positive FIACH theorem has been attempted.

**ZIP:** `CST-TT-01_cst-temporal-transcendence_repo.zip`.

---

### CST-TT-02 — Integrated C-package, temporal closure, and gluing

**Purpose:** land target realization independently of lineage and autonomy.

**Work:**

- Formalize finite surrogate witnesses for C1–C8, keeping the clauses separate and independently checkable.
- Give C6 real content through order, viable/progressing tick, endogenous record/arrow, and target-local temporal ownership; do not make C6 sufficient for the other clauses.
- Define clause scopes, overlap compatibility, hard gates, join trees/running-intersection covers, and a global package witness.
- Prove the acyclic local-witness gluing theorem (`PTH-01`).
- Prove staged heterogeneous package assembly/preservation (`PTH-02`) without using lineage or autonomy as premises.
- Prove or check the local/global obstruction and recombination boundary (`PTH-10`).
- Build `package_gluing_auditor` and the package part of the certificate format.
- Land at least one nontrivial integrated target witness and one countermodel for each indispensable package obligation.

**Circularity control:** `IntegratedPkg` must be definable and testable for an independent target twin; it cannot contain source ancestry, live-corridor, FIACH, or personal-identity fields.

**Exit gate:** target-package realization is a landed theorem/certificate layer, independent of source-target lineage and withdrawal autonomy.

**ZIP:** `CST-TT-02_cst-temporal-transcendence_repo.zip`.

---

### CST-TT-03 — Heterogeneous temporal transport and route discipline

**Purpose:** define what temporal structure crosses the carrier boundary before calling any episode a continuing process.

**Work:**

- Formalize `TemporalSig` as a bundle of:
  - `PredictiveNow`;
  - successor/order data;
  - tick phase and progress;
  - record quotient and arrow order;
  - route residue;
  - ownership/maintenance metadata.
- Formalize representative-independent predictive bridges on the declared reachable image.
- Formalize clock/tick translation, monotone record descent, arrow preservation, and ownership-interface maps.
- Prove the bundled heterogeneous temporal-transport theorem.
- Formalize route words, composition, direct-versus-factored transport, holonomy, and retained memory.
- Prove/check:
  - memory-or-flatness;
  - holonomy-not-arrow;
  - route-memory composition boundary (`PTH-11`);
  - no canonical global `now` under nonzero translation holonomy;
  - route-independent temporal endpoint under explicit normalization/confluence hypotheses.
- Build `temporal_transport_checker` and `holonomy_confluence_checker`.
- Implement replacement-order holonomy and confluent-completion controls.

**Exit gate:** temporal transport is independently checkable and does not contain a lineage verdict. Route dependence is either carried explicitly in the certificate or discharged by a proved confluence/flatness condition.

**ZIP:** `CST-TT-03_cst-temporal-transcendence_repo.zip`.

---

### CST-TT-04 — Temporal corridor, composition, and the overlap/direct-successor fork

**Purpose:** land the lineage engine and test whether continuous temporal realization genuinely distinguishes a handoff from a reconstruction.

**Strict primary definition:** an overlap-based corridor with no realized-time gap, mixed source/target support, independently testable nonredundancy, temporal-signature transport, and exact takeover frontiers.

**Separate research fork:** a direct cross-carrier successor with no extended mixed stage, admitted only under stronger predictive, tick, record, provenance, and ownership-interface certificates. It remains separately named and must not silently broaden the strict relation.

**Work:**

- Formalize the episode graph, active support, local successor steps, mixed stages, frontier compatibility, nonredundancy, and no-gap conditions.
- Build `corridor_and_branch_checker` and `bridge_composition_checker`.
- Prove temporal-corridor composition (`PTH-03`) or identify the exact missing frontier condition.
- Prove detached-copy separation (`PTH-08`).
- Prove the strong gap classification: an interval with no realized package time fails strict temporal continuity even when an equivalent target later resumes.
- Compare overlap and direct-successor predicates on the fixed toy battery.
- Attempt direct-successor composition and detached-copy exclusion without verdict-loaded provenance.
- Run bounded searches for:
  - accidental admission of detached copies;
  - universalization;
  - noncompositionality;
  - definitions whose nonredundancy clauses merely restate the conclusion.

**Decision gate:**

- If the overlap corridor is noncircular and compositional, it remains the primary lineage engine.
- If the direct-successor predicate also survives, it becomes a separately reported strengthening, not a redefinition of the strict result.
- If the overlap corridor triggers a frozen kill criterion, record the kill and authorize the conditional IAPS branch later. Do not switch merely because the proof is difficult.

**Exit gate:** a lineage predicate is either landed with exact positive/negative discriminators or formally killed with a reproducible counterexample.

**ZIP:** `CST-TT-04_cst-temporal-transcendence_repo.zip`.

---

### CST-TT-05 — Withdrawal autonomy and integrated Temporal-FIACH

**Purpose:** establish that the target owns and maintains its temporal package after the source and transfer machinery are removed, then combine the three independent lanes.

**Work:**

- Formalize the target boundary, named dependencies, withdrawal intervention, retained environment, disturbance class, repair/control actions, budget state, and controlled invariant region.
- Prove post-withdrawal controlled invariance (`PTH-04`) by finite induction/invariant arguments.
- Prove external-support autonomy failure (`PTH-09`).
- Formalize anti-stall and budget-solvency conditions; keep finite-horizon success distinct from unbounded liveness.
- Build `withdrawal_autonomy_checker`, returning invariant sets or shortest collapse traces.
- Implement the positive live temporal handoff:

```text
source-owned -> mixed/nonredundant -> target takeover -> withdrawal -> target-owned invariant region
```

- Implement the external-scheduler/decoder shadow and long-run budget failure controls.
- Define `TemporalFIACHCertificate` with separate fields for `S-R`, `S-L`, `A`, and route status.
- Prove the integrated certificate theorem (`PTH-05`) solely by composing independently established package, corridor, and autonomy results.
- Include one-obligation-removed countermodels: package-only, lineage-only, autonomy-only, and every two-of-three combination.

**Exit gate:** the primary Temporal-FIACH theorem is Lean-checked with at least one exact positive witness and the mandatory counterfeits, or a kill criterion is formally recorded.

**ZIP:** `CST-TT-05_cst-temporal-transcendence_repo.zip`.

---

### CST-TT-06 — Composition, branching, route completion, and full toy closure

**Purpose:** turn the core theorem into a coherent relation rather than a single bespoke witness.

**Work:**

- Prove full Temporal-FIACH episode composition (`PTH-06`) under explicit temporal-frontier, route-memory, and ownership-interface compatibility.
- Prove relation-valued temporal fission (`PTH-07`) and target-swap symmetry nonselection.
- Add the fusion/recombination boundary: process merger or ancestry may exist while the integrated target package fails a joint provenance/credit/gluing condition.
- Complete the route-independent strengthening under confluence/normalization and retain the holonomic route-indexed form when those premises fail.
- Run the complete primary/common toy suite:
  1. live temporal handoff;
  2. detached exact temporal copy;
  3. direct-successor handoff;
  4. external-scheduler shadow;
  5. replacement-order holonomy;
  6. confluent completion;
  7. temporal fission;
  8. gap and resume;
  9. anti-stall;
  10. long-run budget failure;
  11. local/global obstruction;
  12. public-shadow collision;
  13. scalar hard-gate failure.
- Use bounded enumeration to search for smaller witnesses, hidden equivalences, failed compositions, and missing assumptions.
- Freeze exact theorem/witness minimality and independence results.

**Exit gate:** all primary/common theorem and toy obligations are complete, reproducible, and cross-linked; remaining unproved statements are explicitly separated from landed results.

**ZIP:** `CST-TT-06_cst-temporal-transcendence_repo.zip`.

---

### CST-TT-07A — Primary strengthening branch

**Run only if the Temporal-FIACH primary survives.**

**Purpose:** add only strengthenings that improve the paper without weakening the exact claim.

**Possible work, in priority order:**

1. land the direct-successor theorem as a separately named broader temporal-continuity class, if it passed CST-TT-04;
2. prove its exact relation to overlap Temporal-FIACH, such as an implication, incomparability, or strict inclusion;
3. add exact vector-valued defect and hard-gate semantics, without replacing exact failures by an average score;
4. add bounded robustness/stability results for perturbations that preserve all hard gates and temporal progress;
5. strengthen the finite-versus-unbounded boundary, possibly with a coinductive or invariant formulation if tractable;
6. complete any scientifically useful composition or confluence corollaries deferred from CST-TT-06.

Approximation may be added only after the exact theorem is stable. It may not rescue a failed exact target.

**Exit gate:** every strengthening is either proved with explicit assumptions or rejected with a recorded countermodel; the primary theorem remains unchanged and auditable.

**ZIP:** `CST-TT-07A_cst-temporal-transcendence_repo.zip`.

---

### CST-TT-07B — Conditional Temporal-IAPS fallback branch

**Run only after a documented primary kill condition.**

**Purpose:** land source-derived temporal successorship without claiming an uninterrupted stream.

**Work:**

- Formalize finite predictive partitions and representative-independent bridges.
- Define an operational provenance seed that cannot mention ancestry or successorhood.
- Define monotone no-ex-nihilo closure and prove existence, stabilization, leastness, and derivation ranks.
- Prove independent-twin exclusion.
- Prove relation-valued fission, guarded fusion, and empty-target behavior.
- Combine ancestry with the already landed package and autonomy layers to prove the integrated IAPS theorem.
- Implement the fallback toys:
  - source-derived destructive successor;
  - independent structural twin;
  - symmetric source-derived duplication;
  - fusion with recombination conflict.
- Prove destructive-reconstruction/twin separation, no unique identity from ancestry, and predictive-ancestry/package insufficiency.
- If operational seeds universalize, admit stale/adversarial records, or encode the conclusion, stop at the no-go-only result.

**Exit gate:** Temporal-IAPS is landed as a relation-valued structural-successorship theorem, or the repository freezes the terminal no-go result with the failed constructive attempts preserved.

**ZIP:** `CST-TT-07B_cst-temporal-transcendence_repo.zip`.

---

### CST-TT-08 — Final science closure and theorem/toy handoff

**Purpose:** produce the complete science asset bank needed to write the paper, without writing the paper itself.

**Work:**

- Run the full Lean build, all Python tests, all certificate checks, and all deterministic rebuilds from a clean extraction.
- Audit every theorem statement against the final proof term or checked countermodel.
- Freeze a theorem status table with only `proved`, `checked finite countermodel`, `conditional`, `killed`, or `open`; never use vague success labels.
- Freeze the complete model catalog, canonical certificates, minimality bounds, and expected outputs.
- Produce a machine-readable dependency DAG from definitions to lemmas to main theorems and no-gos.
- Produce a claim/assumption/nonclaim ledger separating:
  - structural realization;
  - continuous temporal lineage;
  - temporal successorship;
  - autonomy;
  - route dependence;
  - recognition;
  - ontology and identity.
- Produce a paper-facing **science handoff**, not manuscript prose, containing exact theorem statements, proof dependencies, model descriptions, result tables, failed alternatives, citation provenance to the SBT corpus, and the precise claim ceiling.
- Remove dead exploratory code only after preserving rejected definitions and counterexamples in an archive directory.
- Verify the final ZIP after extraction and record the clean Git commit/tag.

**Final branch outcomes:**

1. **Preferred:** Temporal-FIACH + mandatory no-go kernel, with optional direct-successor strengthening.
2. **Fallback:** Temporal-IAPS + mandatory no-go kernel, with FIACH kill documented.
3. **Honest terminal result:** no-go/boundary suite only, if both constructive lineage engines fail.

**Exit gate:** another agent can restore the ZIP, reproduce every theorem and toy result, and write the paper without relying on this conversation.

**ZIP:** `CST-TT-08_cst-temporal-transcendence_repo.zip`.

## 4. Required theorem coverage at program end

### Constructive primary/core

- acyclic local-witness gluing;
- staged heterogeneous package assembly;
- bundled temporal transport;
- temporal-corridor composition;
- target-native post-withdrawal invariance;
- Temporal-FIACH certificate theorem with separate result lanes;
- full handoff composition under route/ownership compatibility;
- relation-valued temporal fission;
- route-independent endpoint under explicit confluence/flatness assumptions.

### Required no-go and boundary results

- snapshot/detached-copy insufficiency;
- public-shadow insufficiency;
- holonomy-not-arrow;
- memory-or-flatness;
- no canonical global `now` under translation holonomy;
- external scheduler/decoder support defeats target autonomy;
- tick stability without progress;
- local/global and recombination obstruction;
- temporal gap versus resumed stream;
- scalar aggregate residual versus hard-gate failure;
- exact symmetry supplies no invariant unique continuer;
- finite successful traces do not imply indefinite liveness.

### Conditional fallback

- predictive quotient and bridge descent;
- least operational ancestry and leastness;
- independent-twin exclusion;
- relation-valued fission/fusion/empty targets;
- integrated Temporal-IAPS theorem;
- destructive-reconstruction/twin separation;
- no unique identity from ancestry;
- predictive ancestry is package-insufficient.

## 5. Nonnegotiable scientific controls

- The temporal signature is defined before the corridor.
- The package is auditable independently of lineage.
- Autonomy is evaluated by named withdrawal intervention, not ordinary runtime behavior.
- Route dependence is retained unless a theorem removes it.
- Exact copying never selects a unique branch by itself.
- A direct successor is never silently equated with an overlap continuation.
- H-FELT-TIME and H-CONT-TIME remain interpretive hypotheses, not theorem conclusions.
- Fixed-support SBT results are explicitly retyped before cross-carrier use.
- A1, A2-P, certificate soundness, recognition, consciousness, survival, and numerical identity cannot repair a failed structural antecedent.
- A failed constructive target is preserved as a scientifically useful no-go result rather than hidden or redefined away.

## 6. Recommended execution order

Execute in this order:

```text
CST-TT-00
CST-TT-01
CST-TT-02
CST-TT-03
CST-TT-04
CST-TT-05
CST-TT-06
then exactly one of CST-TT-07A or CST-TT-07B
CST-TT-08
```

The branch decision is made from the recorded kill gates, not preference or proof difficulty.
