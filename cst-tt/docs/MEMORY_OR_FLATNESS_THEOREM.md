# Memory-or-Flatness and the Predictive Present

## Generic no-factorization result

`CSTTT.RouteTheory.noCurrentOnlyPredictor` proves:

> If two routes have the same current representation but different future-sufficient values, no deterministic predictor defined only on the current representation can represent both histories.

This is stronger than merely exhibiting a collision. It identifies the exact current-only representational failure.

## Two legitimate repairs

1. **Retain route memory.** `MEM-POS-01` refines `current` to `(current, route residue)`. The refined predictor becomes total and correct.
2. **Prove flatness.** `MEM-FLAT-01` makes the predictive outcomes equal after completion, so the current representation suffices and route residue can be erased at the certified normal form.

The disjunction is structural and route-scoped. It does not say that every physical history must be remembered forever, nor that all admissible route systems are flat.

The two-route binary exhaustion checks 64 assignments, of which 56 satisfy the future-sufficiency premise, and finds zero violations. This bounded run corroborates rather than replaces the generic Lean proof source.

## Composition boundary

Pairwise endpoint agreement is not assumed. When a direct route and a factored route retain different predictive or clock residue, composition remains route-indexed. Route-independent composition is deferred unless a normalization/confluence certificate discharges the residue.
