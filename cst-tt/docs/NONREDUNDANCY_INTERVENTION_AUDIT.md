# Two-Sided Intervention Audit

A mixed stage is not sufficient merely because both carriers are present. Each local carrier must perform independently detectable work in the later temporal projection.

For declared projection fields `predictive_rank`, `tick_index`, and `record_value`, the checker computes:

```text
full           = base + source contribution + target contribution
source removed = base + target contribution
target removed = base + source contribution
```

The leg passes only when the computed full projection equals the actual later-stage signature and differs from both removal projections. The event graph must also contain a source-owned and target-owned mixed-stage event feeding the audited later event.

This avoids defining nonredundancy through the corridor result. The evidence uses only update contributions, event ownership, stage order, and temporal signatures. The Boolean search found masks `[6, 7, 8, 9]` as the jointly nonredundant two-input tables; the ordinary AND table is one witness.

Controls `COR-C03`, `COR-C04`, `COR-C16`, and `COR-C17` separately remove source contribution, target contribution, source event influence, and target event influence.
