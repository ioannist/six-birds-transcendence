# Post-withdrawal autonomy

CST-TT-05 defines autonomy as a target-owned controlled invariant after an explicit withdrawal intervention. The removed set includes the source, migration bridge, controller, external decoder, external scheduler, and undeclared repair support. The retained environment is separately declared and every retained resource is target-owned.

The checker computes the greatest finite controlled invariant rather than accepting a user-supplied safe set. A state survives only when, for every declared disturbance, a target-owned action reaches another surviving state while preserving the integrated package, retained-resource closure, positive tick progress, strict record advance, and budget solvency.

## Positive witness

| Field | Value |
|---|---|
| Target carrier | 101 |
| Finite states | 4 |
| Disturbances | 2 |
| Computed invariant | T-SAFE-0, T-SAFE-1, T-WARNING-0, T-WARNING-1 |
| Finite horizon | 6 |
| Disturbance words checked | 127 |
| Target-owned responses | True |
| Anti-stall | True |
| Budget solvent | True |

The finite certificate establishes model-relative autonomy for the declared disturbance alphabet and horizon. It does not establish indefinite physical persistence, consciousness, felt flow, lineage, survival, or identity.

## Proof architecture

The Python fixed-point implementation emits a canonical policy and collapse traces. Lean proof sources define finite controlled runs and show that a certificate with total safe responses constructs a run of every declared finite length. Python enumeration is corroboration, not a proof oracle.
