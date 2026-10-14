# CST-TT-04 Validation Report

**Status:** PASS
**Total checks:** 765
**Passed:** 762
**Failed:** 0
**Skipped:** 3

## Coverage

- **baseline:** 6
- **boundaries:** 18
- **composition:** 16
- **controls:** 248
- **corridor:** 84
- **direct:** 37
- **inherited:** 40
- **lean:** 20
- **manifest:** 1
- **provenance:** 19
- **python:** 97
- **registries:** 64
- **schemas:** 82
- **search:** 22
- **toolchain:** 11

The sole expected skip in this environment is the Lean compilation check when `lean` and `lake` are absent. Static source checks, executable finite certificates, and Python tests do not substitute for Lean-kernel compilation.
