# Hard-gate-preserving bounded temporal robustness

`ROB-POS-01` assigns independent exact margins to predictive, order, tick, progress, and record advancement. A symmetric integer perturbation box is certified only when its worst case remains above each declared minimum. Six nonnumeric hard gates remain exact and cannot be averaged away.

| Dimension | Base | Minimum | Radius | Worst case |
|---|---|---|---|---|
| predictive-step | 4 | 1 | 2 | 2 |
| order-step | 3 | 1 | 1 | 2 |
| tick-step | 3 | 1 | 1 | 2 |
| progress-step | 2 | 1 | 1 | 1 |
| record-step | 5 | 1 | 3 | 2 |

The deterministic enumeration checks all 945 points in the declared box and finds 0 violations. Six controls show that leaving the box or failing route, ownership, package, or autonomy hard gates is rejected.

The box is a sufficient exact neighborhood, not a claim of maximal radius and not a real-world noise distribution. Approximation does not rescue an exact failure.
