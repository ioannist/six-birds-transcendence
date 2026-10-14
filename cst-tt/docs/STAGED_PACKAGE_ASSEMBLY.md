# Staged Heterogeneous Package Assembly

`STG-POS-01` uses distinct carrier vocabularies, separately named on carriers 17 and 101. It supplies exactly eight typed clause maps. Every source coordinate has one target coordinate, and each stored source/target value is checked against the corresponding local assignments.

The staged auditor passes all ten obligations:

| Field | Pass |
|---|---|
| source package valid | True |
| target package valid | True |
| carriers distinct | True |
| exactly eight maps | True |
| separately typed vocabularies | True |
| coordinate maps total | True |
| value maps sound | True |
| hard gates never averaged | True |
| target globally assembled | True |
| no verdict fields | True |

`SC-01` alters one attested target value while leaving both endpoint packages intact. The staged assembly then fails value-translation soundness. This shows that target realization alone does not prove staged preservation.

The result is structural transport plus target assembly only and does not establish temporal lineage. It contains no operational episode, causal ancestry, temporal-lineage verdict, withdrawal intervention, or autonomy claim.
