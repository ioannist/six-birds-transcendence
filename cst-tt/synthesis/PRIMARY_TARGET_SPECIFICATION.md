
# Primary Target Specification — FIACH

**Target ID:** `FT-01`
**Name:** **Finite Integrated Autonomous Causal Handoff**
**Status:** frozen conjecture-grade target for a later theorem-and-toy project
**Claim lanes:** `S-R`, `S-L`, and `A`, returned as separate fields
**Result ceiling:** structural precursor only

## 1. Motivation

The explored corpus does not justify treating endpoint equality, behavioral copying, target package realization, source ancestry, or target autonomy as interchangeable. The primary target therefore asks for the strongest small finite result that still resembles a system *moving* rather than merely being reconstructed: a heterogeneous episode must build one coherent target-native package, maintain one live causally connected process through a support transition, and leave a target that continues after the source and migration support are withdrawn.

## 2. Typed finite data

All sets below are finite and all carrier tokens are individuated before the verdict.

```text
CarrierId                         finite type
S T : CarrierId                  source and target, with DistinctCarrier(S,T)
Stage := Fin (n+1)               finite ordered handoff stages
State(c)                         carrier-local state type
Event                            finite event type
owner : Event -> CarrierId
stage : Event -> Stage
parents : Event -> Finset Event  acyclic operational dependency graph
Support : Stage -> Finset CarrierId

ClauseId                         finite clause index; first toy uses eight C-shaped proxies
Coord                            finite package-coordinate type
Scope : ClauseId -> Finset Coord
LocalWitness(c,i)                independently defined local witness relation
restrict(i,j)                    overlap restriction maps
JoinTree                         running-intersection witness for the clause cover
HardGate                         independently declared package gate
Ownership                        dependency/resource ownership graph

ProcessSig                       finite process-signature type fixed before evaluation
sig : Event -> ProcessSig
counterfactualInfluence          finite intervention-based nonredundancy predicate
ClockRel                         explicit local-clock/order compatibility

withdraw : Episode -> TargetSystem
Disturbance                      declared finite disturbance alphabet/class
PackageValid : TargetState -> Prop
K : Finset TargetState           proposed target-owned controlled invariant region
```

The first theorem layer may be parametric over `ClauseId` and `LocalWitness`. The first concrete toy must instantiate eight independently falsifiable proxies corresponding to objecthood, strict promotion, reflexive self-coordinate, interface-relative nonexposure, action credit, target-local temporal organization, joint binding/recombination, and viability/repair. This is a finite structural surrogate, not an empirical consciousness certificate.

## 3. Independently defined predicates

### 3.1 Integrated target package

`IntegratedPkg(T,e)` holds only when:

1. every target-local clause relation has a witness;
2. witnesses agree under all declared overlap restrictions;
3. a running-intersection join tree or another proved gluing condition supplies one global witness;
4. every hard gate passes;
5. every final witness and essential dependency is owned by the target boundary after takeover.

No clause may mention `FIACH`, successful transfer, consciousness, sameness of subject, or the final verdict.

### 3.2 Live causal-overlap corridor

`LiveCorridor(S,T,e)` holds only when:

1. `Support(0)` is source-only and the final support is target-only;
2. every process stage is nonempty—there is no undeclared gap or dormant token;
3. at least one stage is genuinely mixed;
4. at least one mixed update has independently checkable nonredundant source and target contributions to a later declared process signature;
5. the admitted process signature and local clock/order relation are preserved according to predeclared rules;
6. a takeover frontier exists after which source-owned process contributions are absent;
7. route memory is retained unless a flatness/confluence theorem proves it irrelevant.

A mere source-to-record-to-target data edge is not a live corridor. A detached exact copy therefore does not satisfy this predicate.

### 3.3 Post-withdrawal autonomy

`Autonomous(T,e,D,K)` holds only when:

1. withdrawal removes the source, migration bridge/controller, external decoder, scheduler, and repair resources not declared inside the target boundary;
2. `K` contains the handoff endpoint and every state in `K` satisfies the target package predicate;
3. for every allowed disturbance from a state in `K`, a target-owned response keeps all successors in `K`;
4. the target boundary and disturbance class were fixed before evaluating the candidate.

The exact theorem should prove controlled invariance for every finite horizon. It does not claim indefinite physical persistence outside the model.

## 4. Frozen relation

For source history node `s`, target history node `t`, and episode `e`:

```text
FIACH_e(s,t) : Prop :=
  DistinctCarrier(S,T)
  ∧ SourcePkg(S,s)                  -- explicit toy stipulation or independent premise
  ∧ StagedClausePreservation(e,s,t)
  ∧ IntegratedPkg(T,t,e)
  ∧ LiveCorridor(S,T,e,s,t)
  ∧ Autonomous(T,e,D,K)
```

`FIACH` is a binary relation, not a function and not an identity predicate. If a common live prefix branches into two separately valid target corridors, both source-target pairs may belong to the relation.

The relation returns a record with separately checkable fields:

```text
{ package_realized : S-R,
   live_lineage     : S-L,
   autonomous       : A,
   route_status     : flat | route-indexed | unresolved,
   recognition      : R-status }
```

No field inherits another.

## 5. Core theorem family

| ID | Frozen theorem/no-go target | Kind | Reconnaissance source | Exact intended content |
|---|---|---|---|---|
| PTH-01 | Acyclic local-witness gluing | constructive | TH-04 | Prove a global target package witness from independently satisfiable local clause relations on a running-intersection cover. |
| PTH-02 | Staged heterogeneous package preservation | constructive | TH-05 | Assemble target-local clause witnesses, hard gates, and ownership into the declared finite integrated package. |
| PTH-03 | Live corridor composition | constructive | TH-07 | Prove composition/transitivity of no-gap mixed-support corridors under exact frontier, clock, and signature compatibility. |
| PTH-04 | Post-withdrawal controlled invariance | constructive_boundary | TH-06 | Prove target package persistence over all finite horizons inside a target-owned controlled invariant region. |
| PTH-05 | FIACH certificate soundness | constructive | new_synthesis_of_TH-04_05_06_07 | A checked certificate entails S-R target package, S-L live structural lineage, and A autonomy as separate fields of one handoff record. |
| PTH-06 | FIACH composition | constructive | new_synthesis | Composable FIACH episodes yield a FIACH relation from the first source to the final target, subject to route-memory and ownership-interface compatibility. |
| PTH-07 | Relation-valued fission | constructive_boundary | TH-08;TH-14 | A symmetric valid fork relates the source to both targets and cannot be invariantly reduced to one target. |
| PTH-08 | Detached-copy separation | no_go_boundary | TH-22 | Endpoint-isomorphic package-bearing autonomous reconstruction need not satisfy live-corridor lineage. |
| PTH-09 | External-support autonomy failure | no_go | TH-17 | A decoder/scheduler/repair-dependent target fails the declared withdrawal autonomy predicate. |
| PTH-10 | Local/global package obstruction | no_go | TH-20;TH-16 | Local or branchwise certificates need not form one globally coherent package or preserve recombination. |
| PTH-11 | Route-memory composition boundary | no_go_boundary | TH-23 | Endpoint/public bridge equivalence is not a congruence when retained route memory differs. |
| PTH-12 | Public-shadow insufficiency | no_go | TH-13 | Public/report-perfect matching cannot decide hidden package or process predicates on a model class containing shadow-colliding alternatives. |

The central theorem is `PTH-05`, but it is intentionally decomposed. The proof is scientifically useful only if `PTH-01` through `PTH-04` are stated independently and the certificate checker does not define success by reusing `FIACH`.

## 6. Exact finite witness suite

| ID | Role | Witness/control | Source model(s) | Required exact discrimination |
|---|---|---|---|---|
| PW-01 | positive | Live integrated handoff | MF-02 × MF-07 × MF-10 | Four-stage source/mixed/target support sequence; eight finite package proxies; target-owned invariant region after withdrawal. |
| PW-02 | negative | Detached exact copy | MF-03 with MF-07 target | Same endpoint package and autonomy but no mixed/no-gap corridor; S-L fails under FT-01. |
| PW-03 | negative | Decoder shadow | MF-07 shadow | Supported public/package fields match before withdrawal; target collapses after decoder/scheduler/repair removal. |
| PW-04 | negative | Local-global obstruction | MF-06/MF-07 | Every local clause check passes while parity/gluing prevents one global package. |
| PW-05 | branch | Symmetric live fission | MF-04 with duplicated valid corridor suffix | Both branches satisfy corridor/package/autonomy; target-swap symmetry blocks unique selection. |
| PW-06 | route | Replacement-order holonomy | MF-08 | Two locally valid routes agree publicly but differ on retained route memory; composition needs flatness/confluence. |
| CW-01 | negative | Public-shadow collision | MF-01/MF-05 | Same public/report input, different hidden predictive/package fact. |
| CW-02 | negative | Scalar residual false positive | MF-09 | Small aggregate score hides a viability hard-gate failure. |

### Primary positive witness shape

The first positive model should combine the finite skeletons without simulating the full Six Birds system:

```text
stage 0: active support {S0,S1}
stage 1: active support {S1,T0}; both contributions counterfactually nonredundant
stage 2: active support {T0,T1}; target takeover
stage 3: source/bridge withdrawn; target remains in package-valid invariant K
```

The target state carries exact finite coordinates `(q,h,a,k,z,v,self=T)` and eight clause records. The clause cover must have an explicit join tree. The negative shadow produces the same finite public trace before withdrawal but obtains hidden update, clock, or repair from removed external tokens and then reaches a sink.

## 7. Toy-program contracts

The later project should build only the following exact tools for the primary:

1. **TP-10 bounded witness/counterexample enumerator** — establish minimal examples and prevent definitions from being rescued after counterexamples appear.
2. **TP-07 package/gluing auditor** — emit per-clause, overlap, join-tree, ownership, and global-witness certificates.
3. **TP-03 continuation/branch classifier** — compute `LiveCorridor` separately from any ancestry relation and return branch-valued results.
4. **TP-08 withdrawal/autonomy checker** — remove named dependencies and compute controlled-invariant sets or shortest collapse traces.
5. **TP-04 bridge-composition checker** — test frontier compatibility, direct-versus-factored agreement, and replacement-order critical pairs.
6. **TP-05/TP-06/TP-09 controls as needed** — holonomy, recombination, and vector hard-gate audits.

Python may search and emit explicit certificates. Lean must define the semantics and check the certificates; enumeration is not a proof oracle.

## 8. Lean kernel targets

A small first kernel can be organized as:

```text
CST/Finite/Carrier.lean
CST/Package/Scope.lean
CST/Package/JoinTree.lean
CST/Package/Gluing.lean
CST/Process/EventGraph.lean
CST/Process/Corridor.lean
CST/Process/CorridorComposition.lean
CST/Autonomy/Ownership.lean
CST/Autonomy/Withdrawal.lean
CST/Autonomy/ControlledInvariant.lean
CST/Handoff/FIACH.lean
CST/Handoff/Fission.lean
CST/Countermodels/{Copy,Decoder,Gluing,Symmetry,Holonomy}.lean
```

The first kernel need not import category theory, quotient types, continuous dynamics, neuroscience, or a full Six Birds simulator.

## 9. Corpus dependency map

- `A-CT-01 / P05` supplies the C-package target and the explicit warning that no integrated instance or A2 transport theorem currently exists.
- `A-PR-01` and `A-EX-01` supply promotion/exactification motifs but retain fixed-support retyping debt.
- `A-EV-01` and `A-LG-01` motivate typed event records and the local/global gluing gate.
- `A-AG-01` and `A-VI-01` supply agency, viability, maintenance, and withdrawal-sensitive autonomy machinery.
- `A-TM-01`, `A-CF-01`, `A-RT-01`, and `A-HO-01` motivate local clocks, route memory, critical-pair/confluence, and holonomy controls.
- `A-RE-01` motivates branch/recombination distinctions.
- `A-FS-01` supplies finite semantics and no-smuggling discipline.

Every cross-carrier use is new or heterogeneously retyped; no fixed-support theorem is silently relabeled.

## 10. Assumptions and claim tiers

### Structural theorem premises

`D-CARRIER`, `H-DISTINCT`, `H-BRIDGE-ADM`, a stipulated/checkable finite `H-SOURCE-FULL` surrogate, object-specific `H-PRESERVE-O`, `H-GLOBAL-GLUE`, the criterion choice `H-LINEAGE`, and `H-AUTONOMY`. `H-ROUTE-FLAT` is required only for route-independent strengthenings; otherwise results remain route-indexed.

### Not used by the structural theorem

`H-CERT-SOUND`, `H-RECOG`, `A1`, `A2-P`, and `H-IDENTITY-O` are not proof premises. They cannot repair a failed corridor, gluing, ownership, or autonomy antecedent.

### Claim ceiling

A proved FIACH theorem would establish only:

- one finite target package surrogate exists;
- one declared live structural lineage relation connects source and target histories;
- the target is autonomous under the declared withdrawal and disturbance model.

It would not establish that either system is conscious, that consciousness literally moved, that the source survived, that the source and target are numerically identical, or that substrate indifference is true.

## 11. Copy and fission policy

- **Independent twin:** may satisfy target package and autonomy; fails FIACH lineage.
- **Nondestructive detached exact copy:** fails FIACH unless created along a valid live corridor; source persistence does not change that.
- **Later deletion of source:** does not retroactively create a corridor or unique selection.
- **Symmetric live fission:** both valid branches are related; no unique identity claim.
- **Fusion:** requires actual coupled process merger plus package/recombination gluing; endpoint state fusion is insufficient.
- **Destructive reconstruction/gap:** fails the primary corridor predicate and is routed to the fallback audit.

## 12. Kill and downgrade criteria

Switch away from the primary if any of the following occurs:

1. every viable process signature or nonredundancy predicate mentions the desired continuation verdict;
2. two individually valid corridors fail composition despite all stated frontier conditions;
3. a detached reconstruction satisfies every declared corridor condition;
4. no nontrivial finite integrated target package survives an independent clause/gluing/ownership audit;
5. target autonomy requires an undeclared or post hoc enlarged boundary;
6. route-memory omissions make direct and factored results noncongruent and cannot be repaired without making the target unwieldy.

Items 1–3 trigger the FT-02 fallback. Items 4–5 also threaten FT-02 and may force the terminal no-go landing. Approximation is deferred rather than used to rescue a failed exact target.

## 13. Excluded claims

No result in this target is a theorem about empirical human uploading, biological necessity, phenomenal continuity, moral status, legal identity, numerical identity, A1, A2-P, or certificate soundness. “Causal handoff” is the name of a finite structural relation, not a synonym for personal survival.
