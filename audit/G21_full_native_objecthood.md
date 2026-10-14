# G21: full physical C1 and exact closure audits

This packet evaluates the C1 family frozen before evaluation in
`audit/proposed_models/G17-full-native-package.model.json`. The matrix P is
computed from actual maintenance rows on all 32 physical states, including
replica and phase. The actual source execution and both installed autonomous
successors have precisely these projected matrices when their funded sectors
hold. Increasing histories, environmental cursors and receipt lists are kept
in the execution bridge; stationarity is asserted only on the finite physical
sector with fixed owner, owned token, installed program and rooted route.

C and U are derived from the computed terminal profile. Prototypes are the
first state in each actual class, not a supplied prototype table. There are
16 distinct prototypes with computed codes 0 through 15; each fiber has two
states. The prototype index is a proved in-range finite index. C is the
actual class indicator and U is uniform on its actual fiber. Their product
forgets exactly replica and retains outside, both kernel bits and phase.
No missing index has a default value.

Perturbation is applied before taking the power: P_e=(1-e)P+eJ, with
J uniform on all 32 states, e in {0,1/16}, and E=(P_e)^tau C U with tau in
{1,2}. A proved raw-matrix equation shows P_e C U=P_e, so these exposures
are precisely the one- and two-step matrices of the perturbed physical
process. The generic positive-matrix uniqueness proof uses a maximum ratio
against a strictly positive stationary law and exact finite sums. It introduces
no spectral or linear-algebra axiom.

The unperturbed one-step probability fixed point is unique: outside mass is
zero, and destination-column symmetry reduces the exact stationary equations
to four phase/type values. Both perturbed closures have the same unique,
strictly positive, nonuniform probability fixed point. The unperturbed two-step
closure is genuinely nonunique: two distinct normalized phase laws are fixed.
The physical clock is never marginalized to hide this counterexample.

| Perturbation | Staging | Fixed-point return | Core retention | Defect |
| --- | --- | --- | --- | --- |
| 0 | 1 | Unique probability fixed point | 1 | 1 |
| 0 | 2 | Same fixed point plus two distinct phase laws; nonunique | 1 for these laws | 195/2048 |
| 1/16 | 1 | Unique positive probability fixed point | 31/32 | 465/512 |
| 1/16 | 2 | Same unique positive probability fixed point | 31/32 | 30675375/268435456 |

Retention is checked against the preregistered 15/16 threshold on the entire
16-state inside core. The core is closed under unperturbed maintenance.
Perturbation allows outside leakage and the stationary mass is measured rather
than assumed supported inside. Total variation from the uniform inside-core
law is 1/22 unperturbed and 319/5536 perturbed. No defect acceptance threshold
was preregistered; the exact values are reported without inventing one.
The existing stronger `ObjecthoodRules.Gate` and its uniqueness requirement
are unchanged; its acceptance is not asserted for the nonunique staging.

| Argument | Independent basis | Exact return |
| --- | --- | --- |
| Raw C1 carrier | Frozen actual rows and funded execution sectors | Source and both target physical matrices, with phase retained |
| Coarse/lift pair | Actual terminal classes, first-occurrence prototypes and fiber counts | C, U and C U equations with no free derived input |
| Fixed points | Exact stationary equations; generic positive-matrix law | Baseline one-step and both perturbed uniqueness, explicit two-step nonuniqueness |
| Quantitative readouts | Kernel-proved two-/four-step matrix formulas | Exact retention, TV and max-row idempotence defects |
| Independent transcription | Python rebuilds raw rows/classes/C/U, powers before exposure, exact Gaussian solve | Every matrix entry and all reported readouts; planted drift controls |

| Change | Classification | Boundary |
| --- | --- | --- |
| Positive finite-matrix calculus | (b), derived mathematical proof | Standard axioms only; no external spectral theorem |
| Physical C1 realization and audits | (b), preregistered construction | Exact finite parameter family, not an interval or complete history stationary law |
| Registry and inventory | (a), evidence accounting | Open TTF-05 evidence only; status and ceilings unchanged |

This is a C1 component, not an integrated C1-C8 certificate. The all-eight-role
history interface remains G18/G19, and literal activation/joint funding remain
G20. Temporal transport between source and successor frames, C4-C8 assembly,
directional generator credit, historical joint observer/gluing laws, TTN/POS04
restoration and TTF-04/05 final adjudication remain required. A stronger history
closure lift is still required if the exact original endpoint demands a
stationary law on strictly increasing history registers.

Fresh main-worktree build, full validator, TTH06 and all full-native
transcriptions plus a fresh independent review are required before commit.
