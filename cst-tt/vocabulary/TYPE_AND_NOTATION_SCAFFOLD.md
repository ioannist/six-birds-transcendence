# Type and Notation Scaffold

## 1. Status

This notation is deliberately permissive. It makes candidate theories comparable without choosing which object, bridge, or identity criterion is correct.

## 2. Base symbols

| Symbol | Type | Meaning |
|---|---|---|
| `Σ_S`, `Σ_T` | `CarrierSpec` | separately declared source and target carrier specifications |
| `X_S`, `X_T` | finite or otherwise declared state carriers | carrier states; never equated across types without a comparison map |
| `H_S`, `H_T` | history/process spaces | admissible histories over each carrier |
| `D_S`, `D_T` | dynamics/continuation structures | deterministic maps, kernels, transition systems, or another declared law |
| `I^pub_S`, `I^pub_T` | public interfaces | current admissible observations/readouts |
| `I^pred_S`, `I^pred_T` | predictive interfaces | admissible continuations and future observations |
| `M_S`, `M_T` | predictive quotients, when defined | future-sufficient equivalence classes relative to declared continuations |
| `Q_S`, `Q_T` | current/public quotients, when defined | current-observation equivalence classes |
| `P_S`, `P_T` | `Package(Σ)` | source package and target candidate package |
| `C[P]` | clause vector | declared C1–C8 or subset satisfaction profile |
| `K[P]` | viability object | declared viability kernel or maintained feasible region |
| `B` | `Bridge(Σ_S, Σ_T)` | typed cross-carrier bridge data |
| `ρ` | `Route` | ordered bridge composition or overlap trajectory |
| `κ` | `LineageCriterion` | rule/relation used to classify source-target lineage |
| `J` | `Intervention` | removal of source, bridge, decoder, controller, or protocol support |
| `ε` | `DefectBudget` | exact zero or typed approximation bound |
| `Ω` | `AssumptionSet` | certificate soundness, A1, A2, or narrower premises |

## 3. Package status is separate from package data

A package record does not inherit a realization status. Later candidate cards must select one explicit status, such as:

```text
candidate_only
component_witnesses_only
simplified_certificate_satisfied
full_C_package_satisfied
full_C_package_plus_soundness
ontologically_realized_conditional_on_named_premises
```

No source or target in this repository receives one of the stronger statuses by default.

## 4. Package-level notation

Use the following predicates only with declared parameters:

```text
Transport[O, B, ε](P_S, P_T)
TargetPackage[C, G](Σ_T, P_T)
Lineage[κ, ρ](P_S, P_T)
Autonomous[J, h](Σ_T, P_T)
Recognized[E](P_T)
Ontic[Ω](P_T)
```

`O` may be a state relation, predictive quotient, transition algebra, closure operator, viability object, temporal structure, recombination structure, action-credit structure, whole certificate, or another candidate object. The notation does not privilege any choice.

## 5. Comparison vocabulary

Use one of these explicit forms instead of bare “same”:

```text
x_S ~pub x_T              public-interface equivalence
x_S ~pred x_T             predictive equivalence under declared continuations
P_S ≅F P_T                isomorphism preserving structure family F
P_S ≈ε,F P_T              approximate F-equivalence at defect ε
P_S Lκ,ρ P_T              lineage relation under κ and route ρ
Inv_F(P_S) = Inv_F(P_T)   equality of named invariants only
```

None of these relations is token identity unless token identity is separately defined and defended.

## 6. Bridge signatures

A bridge candidate must instantiate a signature such as:

```text
StateMapBridge:
  b : X_S → X_T
  obligations: admissibility, dynamics compatibility, interface compatibility

HistoryRelationBridge:
  B_H ⊆ H_S × H_T
  obligations: prefix/continuation closure, causal direction, composition

SpanBridge:
  X_S ← Z → X_T
  obligations: common-mediator semantics, loss/defect on each leg

SimulationBridge:
  R ⊆ X_S × X_T
  obligations: forward-step matching under declared actions/observations

OverlapBridge:
  Γ on X_S × X_T × X_shared
  obligations: contribution schedule, handoff criterion, source/target responsibility

RecoveryBridge:
  encode, noise/translation, recover
  obligations: code/object definition, error model, decoder dependence, autonomy after recovery
```

Candidates may combine signatures, but each composition must be typed.

## 7. Structural result shapes

Potential later theorem shapes include, without endorsement:

```text
Transport[O,B,0] → Inv_F(P_S)=Inv_F(P_T)
Transport[O,B,0] ∧ GateConditions → TargetPackage[C,G](Σ_T,P_T)
Flat(ρ) ∧ LocalTransport(ρ) → RouteIndependentTransport(ρ)
SymmetricDuplicate(B) ∧ NoExtraAsymmetry → ¬UniqueLineage(κ)
Autonomous[J,h](Σ_T,P_T) → ¬BridgeDependent_h(P_T)
Defect(B2∘B1) ≤ Φ(Defect(B1), Defect(B2))
```

These are grammar examples, not conjectures selected by the project.

## 8. Result-status modifiers

Attach one status to each claim record:

- `DEFINITION`
- `EXACT_THEOREM`
- `FINITE_ENUMERATION`
- `CONDITIONAL_SCHEMA`
- `CONJECTURE`
- `COUNTEREXAMPLE`
- `OPEN_TARGET`
- `ANALOGY`
- `METHODOLOGICAL_RULE`
- `REJECTED_CANDIDATE`

Claim type and result status are orthogonal. For example, an `S-L` statement may be a `DEFINITION`, `CONJECTURE`, or `COUNTEREXAMPLE`.

## 9. Null and failure values

Do not force every relation to return a positive label. Candidate classifiers must allow:

```text
no_transport
no_target_package
no_lineage_successor
multiple_successors
fusion_result
extinction
bridge_dependent
route_dependent
underdetermined
not_applicable
```

The empty or underdetermined outcome is a legitimate result, not a failure of the exploration.
