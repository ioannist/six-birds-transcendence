# CST-TT-03 Transport and Route Control Suite

| Control family | Count |
|---|---|
| memory | 1 |
| record-arrow | 4 |
| route | 8 |
| transport | 15 |

The 28 controls remove or falsify one registered obligation at a time where possible. Cascading failures are retained when an earlier typing defect necessarily invalidates dependent checks.

Principal controls include:

- same-carrier and same-alphabet pseudo-transport;
- incomplete component maps;
- representative-dependent predictive bridges;
- lost successors, tick progress, record arrows, collapsed or erased route residue, or maintenance state;
- target signatures still owned by the source;
- a transport record containing a lineage verdict;
- false flatness under an unjoined critical pair, retained residue, or nonzero clock holonomy;
- a route-invalid transition and a direct/factored mismatch;
- erased route memory under predictive divergence;
- a constant record map that is monotone but not strictly arrow-preserving;
- `TR-C15`, which rejects a route-indexed map that collapses distinct retained route residues.

Every control is a checked finite countermodel, hash-bound to an exact JSON artifact and independently recomputed by the phase validator.
