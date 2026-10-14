# CST-TT-00 Validation Report

**Overall:** PASS
**Checks:** 828 passed; 0 failed; 1 skipped

## Category summary

| Category | PASS | FAIL | SKIP |
|---|---:|---:|---:|
| baseline | 5 | 0 | 0 |
| circularity | 1 | 0 | 0 |
| claim-ceiling | 55 | 0 | 0 |
| documentation | 36 | 0 | 0 |
| kill-policy | 14 | 0 | 0 |
| lean-static | 176 | 0 | 0 |
| no-results | 75 | 0 | 0 |
| provenance | 141 | 0 | 0 |
| python | 15 | 0 | 0 |
| registry | 247 | 0 | 0 |
| reproducibility | 4 | 0 | 0 |
| schema | 32 | 0 | 0 |
| toolchain | 8 | 0 | 1 |
| typing | 19 | 0 | 0 |

## Environment-dependent check

`lean` and `lake` were unavailable in the execution container. No Lean compilation pass is claimed. The repository pins Lean 4.28.0, contains an external `lake build` command, and passed the static source, import-layer, circularity, schema, Python, and registry checks.

## Skipped checks

- `TOOL-LEAN-BUILD` — lean/lake unavailable in execution container; external build remains required

## Exit assessment

All environment-independent CST-TT-00 gates pass. The only unperformed gate is actual Lean compilation because the executable was unavailable; this is explicitly deferred and not counted as a pass.
