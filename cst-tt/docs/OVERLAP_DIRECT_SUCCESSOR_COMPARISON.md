# Overlap and Direct-Successor Comparison

The fixed finite battery shows that the two classes are not interchangeable.

| Case | Scenario | Strict overlap chain | Atomic direct | Direct path | Classification |
|---|---|---|---|---|---|
| CMP-01 | atomic live overlap | pass | fail | fail | strict overlap only |
| CMP-02 | two-leg live overlap through intermediate carrier | pass | fail | fail | composed strict overlap chain |
| CMP-03 | atomic direct event successor | fail | pass | pass | direct class only |
| CMP-04 | two-edge direct path | fail | fail | pass | composed direct path; not one atomic edge |
| CMP-05 | detached exact temporal copy | fail | fail | fail | endpoint reconstruction only |
| CMP-06 | temporal gap and resumed stream | fail | fail | fail | resumed equivalent stream |
| CMP-07 | same-carrier re-encoding | fail | fail | fail | typing control |
| CMP-08 | mixed but source-redundant stage | fail | fail | fail | mere coexistence without two-sided causal work |
| CMP-09 | arbitrary archival data edge | fail | fail | fail | data reachability only |

The battery contains a strict-overlap witness that is not direct and a direct witness that is not strict-overlap. This is finite discriminator evidence for incomparability; the full `TTD-02` theorem remains assigned to CST-TT-07A.

Detached copies, temporal gaps, same-carrier re-encodings, redundant mixed stages, and archival data edges satisfy neither class.
