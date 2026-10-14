# Lexical source-dependency audit method

For each non-quarantined theorem-like environment, the audit scans the environment body and an immediately following `proof` environment, when present. It records explicit `ref`/`cref`/`eqref`/`autoref`/`hyperref` labels and citation keys, resolves local labels to statement IDs or source lines, and preserves unresolved labels rather than guessing.

This audit answers a narrow provenance question: **which dependencies are explicitly named in the source text?** It does not reconstruct implicit mathematics, validate proofs, or certify that a theorem is independent when no reference appears. P46 is entirely absent under quarantine.
