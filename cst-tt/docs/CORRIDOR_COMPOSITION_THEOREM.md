# Strict Temporal-Corridor Composition

The original scaffold required one stage containing the ultimate source and ultimate target. That rule is valid for one atomic handoff but is not closed under composition.

For a two-hop episode

```text
S -> mixed(S,M) -> M -> mixed(M,T) -> T
```

there need not be a stage containing both `S` and `T`. Nevertheless every substrate change is realized through an audited overlap, the intermediate frontier is exact, and package time has no gap.

CST-TT-04 therefore freezes:

- **atomic endpoint overlap** for each carrier change;
- **carrier-chain composition** for multi-hop corridors;
- exact equality of the shared carrier, temporal signature, route residue, and boundary ownership;
- one merged boundary stage rather than duplication or omission.

`COR-COMP-01` composes `COR-POS-02A` and `COR-POS-02B`. The result has two atomic legs, five realized stages, and one intermediate-carrier boundary. The old ultimate-endpoint mixedness rule is false; the strict carrier-chain rule is true.

The bounded summary search examined **16** compatible two-leg shapes. All composed under the carrier-chain rule, while all failed ultimate-endpoint mixedness.

The Lean proof-source construction is `CSTTT.CorridorTheory.strictTemporalCorridorComposition`. Actual Lean-kernel compilation remains separately pending.
