# Typed Neutral Problem Statement

## 1. Purpose of the typing discipline

Ordinary phrases such as “the mind moves,” “the same consciousness appears,” or “the target is an exact copy” combine several distinct mathematical and interpretive claims. This scaffold forces each noun, map, and conclusion to have a declared type before candidate generation begins.

It is a **problem grammar**, not a proposed theory.

## 2. Carrier-indexed primitives

A carrier specification is provisionally written

```text
Σ = (id, X, H, D, U, I_pub, I_pred, Res, Adm)
```

where:

- `id` is a carrier identity tag;
- `X` is the declared state carrier;
- `H` is a declared history/process space over `X`;
- `D` is the transition or continuation structure;
- `U` is the action/control family, if any;
- `I_pub` is the declared current/public interface;
- `I_pred` is the declared predictive interface or continuation family;
- `Res` is the resource/viability structure; and
- `Adm` is the admissibility predicate for states, histories, actions, interfaces, and interventions.

Not every candidate must use every component, but omitted components must be marked `not_applicable`, not silently ignored.

The source and target are separately typed:

```text
Σ_S : CarrierSpec
Σ_T : CarrierSpec
P_S : Package(Σ_S)
P_T : Package(Σ_T)
```

A label change is not enough to establish distinctness. A candidate claiming cross-carrier scope must pass the carrier-distinctness audit in Section 8.

### Cross-carrier versus cross-substrate

`Cross-carrier` is the default structural term in this repository: it requires separately typed carrier specifications and a bridge that genuinely crosses them. `Cross-substrate` is a stronger implementation-level claim. It additionally requires implementation maps `ι_S` and `ι_T` and a substrate/medium classifier `σ` fixed independently of the desired continuation verdict, such that the declared change satisfies the project’s criterion (for example `σ(ι_S) ≠ σ(ι_T)`).

Changing labels, encodings, hardware components, or material constituents is not enough by itself. Conversely, two isomorphic formal state carriers may be distinct implementation tokens or media. Until implementation and classifier data are present, formal results should say `cross-carrier`, not `cross-substrate`.

## 3. Cross-carrier data

The project does not choose one bridge type in advance. Candidate bridge data may have one of the following declared forms, or a new explicitly typed form:

```text
b_X   : X_S → X_T                         state map
B_X   : Relation(X_S, X_T)               state relation
b_H   : H_S → H_T                         history map
B_H   : Relation(H_S, H_T)               history relation
Z     : common mediator
s     : Z → X_S,  t : Z → X_T            span/common refinement
Sim   : Simulation(Σ_S, Σ_T)
BiSim : Bisimulation(Σ_S, Σ_T)
Γ     : CoupledProcess(Σ_S, Σ_T)          overlap/live-handoff process
Rec   : RecoveryAssistedBridge(Σ_S, Σ_T)
```

A bridge record must state its direction, domain, codomain, totality/partiality, causal role, external dependencies, admissible histories, and composition law. The word `bridge` alone proves nothing.

A route is an ordered composite of bridge stages:

```text
ρ = B_n ∘ ... ∘ B_2 ∘ B_1
```

Composition is not presumed well-defined, associative, or path-independent. Those are candidate obligations.

## 4. Independent predicates

The following are distinct proposition families.

### Structural transport

```text
Transport[O, B, ε](P_S, P_T)
```

`O` names the transported object or invariant family; `B` names the bridge; `ε` is `0` for exact preservation or a typed defect budget for approximate preservation.

### Target package structure

```text
TargetPackage[C, G](Σ_T, P_T)
```

`C` names the clause set (for example C1–C8 or a declared subset); `G` names coherence and audit gates. Satisfaction is carrier-indexed and does not imply consciousness.

### Lineage

```text
Lineage[κ, ρ](P_S, P_T)
```

`κ` is the declared lineage criterion and `ρ` the route/history data. `κ` may be partial or relation-valued. It must classify or explicitly leave underdetermined duplicate, fission, fusion, deletion, and source-persistence cases.

### Autonomy

```text
Autonomous[J, h](Σ_T, P_T)
```

`J` is a declared intervention removing some combination of source, bridge, decoder, supervisor, or protocol support; `h` is a time horizon or closure condition. Environment dependence is allowed if declared. “Autonomous” never means metaphysically isolated.

### Recognition

```text
Recognition[E](observations, structural_predicate)
```

`E` is an empirical/interpretive bridge with error and identifiability conditions. Recognition is not derivation.

### Ontological interpretation

```text
Ontic[Ω](structural_predicates)
```

`Ω` is a named assumption set. At minimum, any use of certificate soundness, A1, or A2 must be listed separately.

## 5. No default implications

The base theory contains no default arrow among:

```text
Transport
TargetPackage
Lineage
Autonomous
Recognition
Ontic
```

Examples of jointly possible statuses that the exploration must allow:

- transport succeeds while target-package gates fail;
- a target independently instantiates the package without any source lineage;
- endpoint structures match while route-dependent lineage is underdetermined;
- target package and lineage hold only while a decoder remains attached;
- structural predicates hold while recognition is empirically unavailable;
- all structural predicates hold while ontological interpretation is declined.

## 6. Equality and equivalence discipline

Bare expressions such as `x_S = x_T` or `P_S = P_T` are ill-typed when source and target live on distinct carriers. A valid comparison must declare one of:

- an embedding into a common type;
- an isomorphism of specified structures;
- equality of named invariants;
- a simulation/bisimulation relation;
- a span through a common abstract package;
- a lineage relation; or
- another explicit comparison object.

“Same” must always be followed by the relation and scope: same public class, same predictive class, isomorphic package, same lineage fiber, same token under a declared identity rule, and so on.

## 7. State, history, and process separation

A state map does not automatically induce a history map. A history map does not automatically preserve causal generation. Endpoint isomorphism does not automatically preserve the handoff process. Every candidate must say whether its criterion lives on:

- current states;
- finite or infinite histories;
- controlled continuation laws;
- coupled source-target processes;
- quotient classes;
- certificates; or
- closure/viability fixed points.

## 8. Carrier-distinctness audit

A candidate counts as genuinely cross-carrier only if it answers all of the following:

1. Are `Σ_S` and `Σ_T` separately declared and separately typed?
2. Does the bridge cross those types rather than act only within one fixed support?
3. Is the claimed result invariant under mere renaming of states and components?
4. Would the construction collapse to a fixed-support promotion/refinement theorem after erasing carrier labels? If yes, what additional fact makes it cross-carrier?
5. Are source and target implementation maps separately specified?
6. Is support overlap, if present, represented as an overlap process rather than hidden inside one carrier?
7. Are resource, interface, and dynamics changes declared rather than absorbed into notation?

Failure does not make the model useless; it reclassifies it as a fixed-support or same-carrier model.

## 9. Ill-typed language and required repairs

| Informal sentence | Defect | Minimum repair |
|---|---|---|
| “The consciousness moved to T.” | combines transport, realization, lineage, and ontology | split into S-T, S-R, S-L, A, and O claims |
| “T is identical to S.” | relation and type missing | name token identity, isomorphism, predictive equivalence, or lineage relation |
| “The upload is exact.” | preserved object and metric missing | declare object family, commuting law, and defect `ε=0` |
| “The target behaves the same.” | interface and horizon missing | declare public lens, interventions, and trajectory class |
| “The source was destroyed, so the target survived.” | deletion does not entail lineage | state deletion separately and prove/classify lineage |
| “The model is substrate-independent.” | may mean polymorphic syntax only | state a carrier-transport or invariance theorem with hypotheses |
| “The bridge transfers the package.” | bridge type and preservation law missing | type bridge, package components, and preservation diagram |
| “The copy is a new person.” | ontological verdict hidden in terminology | classify structural duplicate first; price O assumptions separately |
| “The target is autonomous.” | intervention and horizon missing | specify what is removed and what maintenance condition is tested |
| “The certificate proves consciousness.” | certificate soundness and ontic premise omitted | separate S-R, soundness hypothesis, and O implication |

## 10. Candidate record schema

Every candidate developed in later phases must supply:

```text
candidate_id
source_carrier_spec
target_carrier_spec
carrier_distinctness_argument
transported_object_type
bridge_type
route_type
exact_preservation_predicates
approximate_defect_and_metric
c_package_scope
lineage_criterion
branch_fusion_duplicate_policy
autonomy_intervention_and_horizon
recognition_bridge
ontological_assumptions
positive_witnesses
negative_controls
route_composition_status
falsifiers
claim_tags
result_status
source_provenance
nonclaims
```

The YAML question bank is the authoritative checklist for filling this record.
