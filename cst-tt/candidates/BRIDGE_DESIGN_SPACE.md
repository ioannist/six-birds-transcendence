# Cross-Carrier Bridge Design Space

A bridge is typed data and admissibility conditions. It is never the proposition that transfer succeeded. Source and target carrier tokens are independently individuated before any bridge is evaluated.

| ID | Morphology | Signature | Best suited to | Composition | Primary risk | Schemas |
|---|---|---|---|---|---|---|
| BR-01 | Direct state map | `b: X_S -> X_T` | simple exact snapshots | ordinary function composition | state-only; can erase history and branching | atlas control |
| BR-02 | History relation | `B subset Hist(X_S) x Hist(X_T)` | lineage, gaps, fission, fusion | relational composition with witness retention | too permissive without tests | TS-03;TS-10 |
| BR-03 | Forward simulation | `b x_S -> x_T and steps_S matched by steps_T` | one-way predictive or controlled preservation | simulations compose under interface alignment | target may have unmatched behavior | TS-04;TS-09 |
| BR-04 | Bisimulation/conjugacy | `R steps both directions` | exact predictive dynamics | requires compatibility/totality | still endpoint/token neutral | TS-01 |
| BR-05 | Span through common abstraction | `X_S <- A -> X_T or X_S -> A <- X_T` | quotients, logical codes, closure algebras | pullback/pushout conditions | common abstraction is not causal handoff | TS-01;TS-05;TS-06 |
| BR-06 | Cospan into common completion | `X_S -> C <- X_T` | gluing and joint distributed packages | pushout-like completion | completion can add protocol structure | TS-06 |
| BR-07 | Moving-boundary overlap process | `{X_r(t), support(t), coupling(t)}` | gradual/live replacement | concatenation with boundary compatibility | graduality can be smuggled as continuity | TS-03 |
| BR-08 | Continuation functor | `F: HistCat_S -> HistCat_T` | routes, branches, recombination, holonomy | functor composition | category choice may encode verdicts | TS-07 |
| BR-09 | Encode–recover migration channel | `decode_T o recover o encode_S` | logical-object persistence under noise | channel composition with error budget | external recovery can masquerade as autonomy | TS-05 |
| BR-10 | Staged exactification/promotion/audit bridge | `B = audit_T o promote o exactify o transfer` | full package and strict gates | only when stage contracts align | passing local gates may not yield one package | TS-02 |
| BR-11 | Residual-bounded approximate bridge | `B_epsilon with Delta(B)<=epsilon` | noisy and approximate cases | specified defect law, not assumed additivity | threshold can be tuned to preferred labels | TS-09 |
| BR-12 | Branch-valued bridge relation | `B: Hist_S -> P(Hist_T)` | copying, fission, fusion, empty target | Kleisli/relational composition with merge rules | may classify too many successors | TS-07;TS-10 |

## Morphology cards

### BR-01 — Direct state map

- **Typed signature:** `b: X_S -> X_T`
- **Use case:** simple exact snapshots.
- **Admissibility:** must be cross-typed and invariant-respecting.
- **Composition:** ordinary function composition.
- **Failure/circularity risk:** state-only; can erase history and branching.
- **Candidate schemas:** atlas control.

### BR-02 — History relation

- **Typed signature:** `B subset Hist(X_S) x Hist(X_T)`
- **Use case:** lineage, gaps, fission, fusion.
- **Admissibility:** route and causal provenance constraints.
- **Composition:** relational composition with witness retention.
- **Failure/circularity risk:** too permissive without tests.
- **Candidate schemas:** TS-03;TS-10.

### BR-03 — Forward simulation

- **Typed signature:** `b x_S -> x_T and steps_S matched by steps_T`
- **Use case:** one-way predictive or controlled preservation.
- **Admissibility:** totality on reachable source states.
- **Composition:** simulations compose under interface alignment.
- **Failure/circularity risk:** target may have unmatched behavior.
- **Candidate schemas:** TS-04;TS-09.

### BR-04 — Bisimulation/conjugacy

- **Typed signature:** `R steps both directions`
- **Use case:** exact predictive dynamics.
- **Admissibility:** preserve admissible continuation alphabets.
- **Composition:** requires compatibility/totality.
- **Failure/circularity risk:** still endpoint/token neutral.
- **Candidate schemas:** TS-01.

### BR-05 — Span through common abstraction

- **Typed signature:** `X_S <- A -> X_T or X_S -> A <- X_T`
- **Use case:** quotients, logical codes, closure algebras.
- **Admissibility:** legs must preserve named structure.
- **Composition:** pullback/pushout conditions.
- **Failure/circularity risk:** common abstraction is not causal handoff.
- **Candidate schemas:** TS-01;TS-05;TS-06.

### BR-06 — Cospan into common completion

- **Typed signature:** `X_S -> C <- X_T`
- **Use case:** gluing and joint distributed packages.
- **Admissibility:** descent and compatibility conditions.
- **Composition:** pushout-like completion.
- **Failure/circularity risk:** completion can add protocol structure.
- **Candidate schemas:** TS-06.

### BR-07 — Moving-boundary overlap process

- **Typed signature:** `{X_r(t), support(t), coupling(t)}`
- **Use case:** gradual/live replacement.
- **Admissibility:** continuous causal coupling and package-support audit.
- **Composition:** concatenation with boundary compatibility.
- **Failure/circularity risk:** graduality can be smuggled as continuity.
- **Candidate schemas:** TS-03.

### BR-08 — Continuation functor

- **Typed signature:** `F: HistCat_S -> HistCat_T`
- **Use case:** routes, branches, recombination, holonomy.
- **Admissibility:** preserve identities, composition, and selected limits/joins.
- **Composition:** functor composition.
- **Failure/circularity risk:** category choice may encode verdicts.
- **Candidate schemas:** TS-07.

### BR-09 — Encode–recover migration channel

- **Typed signature:** `decode_T o recover o encode_S`
- **Use case:** logical-object persistence under noise.
- **Admissibility:** declared code/noise/recovery family.
- **Composition:** channel composition with error budget.
- **Failure/circularity risk:** external recovery can masquerade as autonomy.
- **Candidate schemas:** TS-05.

### BR-10 — Staged exactification/promotion/audit bridge

- **Typed signature:** `B = audit_T o promote o exactify o transfer`
- **Use case:** full package and strict gates.
- **Admissibility:** all stage certificates and global glue pass.
- **Composition:** only when stage contracts align.
- **Failure/circularity risk:** passing local gates may not yield one package.
- **Candidate schemas:** TS-02.

### BR-11 — Residual-bounded approximate bridge

- **Typed signature:** `B_epsilon with Delta(B)<=epsilon`
- **Use case:** noisy and approximate cases.
- **Admissibility:** metric, thresholds, horizons, margins.
- **Composition:** specified defect law, not assumed additivity.
- **Failure/circularity risk:** threshold can be tuned to preferred labels.
- **Candidate schemas:** TS-09.

### BR-12 — Branch-valued bridge relation

- **Typed signature:** `B: Hist_S -> P(Hist_T)`
- **Use case:** copying, fission, fusion, empty target.
- **Admissibility:** symmetry-respecting and nonretroactive.
- **Composition:** Kleisli/relational composition with merge rules.
- **Failure/circularity risk:** may classify too many successors.
- **Candidate schemas:** TS-07;TS-10.

## Bridge-selection rules

1. State maps cannot be promoted to history bridges without additional route data.
2. Spans/cospans supply comparison or gluing, not causal ancestry.
3. Overlap processes are not continuity by name; they must preserve a declared process organization.
4. Recovery channels can preserve a logical object while failing target autonomy.
5. Branch-valued bridges are allowed and may be required by symmetry; they do not imply one token is numerically identical to every branch.
6. Approximate bridges require a metric, hard gates, thresholds, horizon, and a composition law before they can support any stability claim.
