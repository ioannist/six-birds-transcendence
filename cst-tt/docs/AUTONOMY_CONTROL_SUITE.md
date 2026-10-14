# Autonomy control suite

| ID | Control | Primary failure | Invariant size | Collapse length |
|---|---|---|---|---|
| AUT-C01 | external decoder/scheduler/repair shadow collapses after withdrawal | AUT-O11-target-owned-total-response-law | 0 | 1 |
| AUT-C02 | withdrawal leaves the scheduler in place | AUT-O04-withdrawal-shape-and-completeness | 4 | 0 |
| AUT-C03 | removed and retained resources overlap | AUT-O04-withdrawal-shape-and-completeness | 4 | 0 |
| AUT-C04 | one response action is owned by the migration controller | AUT-O11-target-owned-total-response-law | 0 | 1 |
| AUT-C05 | stable self-loop has no tick or record progress | AUT-O12-anti-stall-progress-and-arrow | 0 | 1 |
| AUT-C06 | finite prefix followed by target-budget insolvency | AUT-O08-endpoint-in-computed-controlled-invariant | 0 | 2 |
| AUT-C07 | declared invariant includes a package-invalid state | AUT-O09-declared-invariant-is-maximal-fixed-point | 4 | 0 |
| AUT-C08 | allowed hit disturbance has no response from one invariant state | AUT-O08-endpoint-in-computed-controlled-invariant | 0 | 1 |
| AUT-C09 | disturbance class chosen after evaluating the target | AUT-O03-disturbance-class-fixed-before-evaluation | 4 | 0 |
| AUT-C10 | maintenance ownership remains external | AUT-O10-package-and-resource-closure | 0 | 1 |
| AUT-C11 | retained maintenance resource is external-owned | AUT-O05-target-owned-retained-resources | 4 | 0 |
| AUT-C12 | verdict-loaded autonomy record | AUT-O15-verdict-field-separation | 4 | 0 |

The controls separately expose external support, incomplete withdrawal, resource overlap, external action ownership, temporal stalling, budget insolvency, invalid safe-set declarations, missing disturbance responses, post-hoc disturbance classes, external maintenance ownership, external retained resources, and verdict smuggling.
