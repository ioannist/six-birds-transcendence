
# Fallback Target Specification — IAPS

**Target ID:** `FT-02`
**Name:** **Integrated Autonomous Predictive Successorship**
**Status:** frozen fallback for a later theorem-and-toy project
**Activation condition:** the primary live-corridor relation is circular, noncompositional, or scientifically too restrictive, while a noncircular operational ancestry relation remains viable

## 1. Motivation

The primary deliberately excludes detached destructive reconstruction. The fallback asks what can still be said when the source is scanned, recorded, erased, and reconstructed on a distinct target carrier. It does not call such a target the uniquely identical continuer. Instead it seeks a finite, source-derived, relation-valued **successorship** result joined to the same independent target-package and autonomy gates used by the primary.

## 2. Typed finite data

The target package, gluing, ownership, withdrawal, disturbance, and invariant-region types are inherited from FIACH. The lineage engine is replaced by:

```text
HistNode                         finite history/event node type
H : FiniteOperationalGraph
srcNodes tgtNodes : Finset HistNode
reachable_H : HistNode -> HistNode -> Prop

Probe                           declared finite predictive probe family
PredSig(node)                   canonical bounded predictive signature
PredCompat : HistNode -> HistNode -> Prop

Seed : HistNode -> HistNode -> Prop
Gamma : Relation HistNode -> Relation HistNode
Anc := leastFixedPoint(Gamma, Seed)
```

`Seed(s,t)` may hold only when a predeclared operational provenance path connects `s` to `t`, the typed record/bridge is admissible, and the selected predictive/transition obligations hold. It may not mention ancestry, continuation, same subject, survival, or the final IAPS verdict.

`Gamma` must be monotone and may add only declared transition-matched descendants and guarded fission/fusion consequences. Every nonseed rule requires an already related predecessor; no target pair is created ex nihilo.

## 3. Frozen relation

```text
IAPS_e(s,t) : Prop :=
  DistinctCarrier(S,T)
  ∧ SourcePkg(S,s)
  ∧ Anc_e(s,t)
  ∧ IntegratedPkg(T,t,e)
  ∧ Autonomous(T,e,D,K)
```

`IAPS` is relation-valued. A source-derived destructive reconstruction can satisfy it. An independently constructed but structurally identical twin with no source-reachable operational path cannot. Symmetric copies may both be successors.

The result remains a conjunction of separate lanes; ancestry does not prove package realization and package realization does not prove ancestry.

## 4. Core theorem family

| ID | Frozen theorem/no-go target | Kind | Reconnaissance source | Exact intended content |
|---|---|---|---|---|
| FTH-01 | Predictive quotient and bridge descent | constructive | TH-01 | Define finite predictive partitions and a representative-independent cross-carrier bridge. |
| FTH-02 | Least operational ancestry relation | constructive | TH-09 | Prove finite monotone closure stabilizes at a unique least relation. |
| FTH-03 | Independent-twin exclusion | constructive_boundary | TH-11 | A disconnected structural twin cannot enter the least relation under no-ex-nihilo rules. |
| FTH-04 | Fission, fusion, and empty targets | constructive_boundary | TH-10;TH-14;TH-16 | Derive relation-valued branch/fusion forms and retain a conflict/gluing guard. |
| FTH-05 | IAPS integrated target theorem | constructive | TH-04;TH-05;TH-06;TH-09 | An ancestral target with a glued target package and post-withdrawal invariant region is an integrated autonomous structural successor. |
| FTH-06 | Destructive-reconstruction/twin separation | constructive_boundary | TH-11;TH-21 | A source-record-target path may qualify while an identical independent twin does not; without seed/dormancy semantics the gap case remains underdetermined. |
| FTH-07 | No unique identity from ancestry | no_go_boundary | TH-14 | Relation membership under exact symmetry supplies no invariant unique successor or numerical-identity conclusion. |
| FTH-08 | Predictive ancestry is package-insufficient | no_go | TH-15 | Predictive equivalence/ancestry alone does not establish the independent C-package obligations. |

The fallback's central scientific burden is not fixed-point existence; that part is elementary. The burden is specifying `Seed` and `Gamma` operationally enough to exclude independent twins and stale/adversarial records without encoding the desired conclusion.

## 5. Exact finite witness suite

| ID | Role | Witness/control | Source model(s) | Required exact discrimination |
|---|---|---|---|---|
| FW-01 | positive | Source-derived destructive successor | MF-03 + MF-07 target | Operational source-record-target path, predictive bridge, target package, and autonomy; no live overlap required. |
| FW-02 | negative | Independent structural twin | MF-03 twin/MF-05 | Isomorphic target with no source-reachable provenance path is excluded by no-ex-nihilo ancestry. |
| FW-03 | branch | Symmetric duplication | MF-04 | Both source-derived copies enter Anc; no invariant singleton selector. |
| FW-04 | fusion | Fusion with recombination conflict | MF-06 | Many-to-one ancestry may exist while integrated target package fails the conflict/gluing guard. |
| CW-01 | negative | Public-shadow collision | MF-01/MF-05 | Same public/report input, different hidden predictive/package fact. |
| CW-02 | negative | Scalar residual false positive | MF-09 | Small aggregate score hides a viability hard-gate failure. |

### Destructive reconstruction positive shape

```text
source active q
  --snapshot--> record r with typed provenance and predictive certificate
  --erase-->    no active source token
  --activate--> target q := decode(r)
  --withdraw--> target package remains autonomous
```

The gap is represented explicitly. The ancestry result comes from the declared source-record-target operational path and closure rules, not from endpoint equality. A twin initialized to the same `q` without a source-reachable path is excluded.

## 6. Toy-program contracts

1. **TP-01 predictive quotient calculator** — compute finite predictive signatures and bridge saturation.
2. **TP-03 continuation/branch classifier** — compute `Anc`, derivation ranks, fission/fusion shapes, and the disagreement with `LiveCorridor`.
3. **TP-07 package/gluing auditor** — establish the target package independently of ancestry.
4. **TP-08 withdrawal/autonomy checker** — establish target-native maintenance independently of ancestry.
5. **TP-06 recombination tester** — block fusion claims that preserve branch marginals but lose joint provenance or credit.
6. **TP-10 bounded enumerator** — search for universalization, independent-twin entry, or smaller countermodels.

## 7. Lean kernel targets

```text
CST/Predictive/Signature.lean
CST/Predictive/Partition.lean
CST/Predictive/Bridge.lean
CST/Ancestry/OperationalGraph.lean
CST/Ancestry/Seed.lean
CST/Ancestry/Closure.lean
CST/Ancestry/Leastness.lean
CST/Ancestry/FissionFusion.lean
CST/Ancestry/TwinExclusion.lean
CST/Successor/IAPS.lean
CST/Countermodels/{Symmetry,Gap,PackageInsufficiency}.lean
```

The package/gluing/autonomy modules are shared with the primary.

## 8. Assumptions and claim tiers

Structural premises include `D-CARRIER`, `H-DISTINCT`, `H-BRIDGE-ADM`, a finite source package premise, object-specific `H-PRESERVE-O`, `H-GLOBAL-GLUE`, the operational `Seed`, monotone no-ex-nihilo `Gamma`, criterion choice `H-LINEAGE`, and `H-AUTONOMY`.

`A2-P` does not create a provenance path or predictive bridge. `A1`, certificate soundness, recognition, and personal-identity interpretation remain outside the theorem.

## 9. Copy, fission, fusion, and gap policy

- **Source-derived destructive reconstruction:** may be an IAPS successor when its seed and all target gates pass.
- **Independent exact twin:** excluded under no-ex-nihilo reachability.
- **Nondestructive exact copies:** each qualifying source-derived target may enter the relation; no exclusive selector.
- **Later deletion:** does not retroactively select one branch.
- **Fission:** one-to-many relation.
- **Fusion:** many-to-one relation only under declared predecessor and conflict/gluing rules; ancestry may hold while package realization fails.
- **Undeclared temporal gap/dormancy semantics:** underdetermined rather than automatically accepted or rejected.

## 10. Kill and downgrade criteria

Abandon or downgrade IAPS if:

1. `Seed` contains continuation-equivalent vocabulary or every data edge qualifies;
2. the least relation includes a disconnected independent twin;
3. repeated fission/fusion makes the relation universal;
4. stale or adversarial records cannot be distinguished without post hoc conditions;
5. predictive ancestry is used to infer package realization rather than paired with an independent audit;
6. no finite source-derived destructive positive survives all target package/autonomy gates.

If these occur, the terminal target is the common no-go suite: symmetry, public-shadow, temporal-gap underdetermination, predictive-package insufficiency, and independent-twin nonidentifiability under restricted interfaces.

## 11. Explicit nonclaims

IAPS does not establish that destructive uploading preserves consciousness, that every source-derived copy is the same person, that operational ancestry is metaphysically sufficient, or that a relation-valued successor has any particular moral/legal status. It is a finite structural successorship theorem target only.
