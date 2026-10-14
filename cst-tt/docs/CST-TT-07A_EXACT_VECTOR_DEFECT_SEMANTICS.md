# Exact vector-valued defect semantics

The strengthening replaces no exact predicate with an average. A defect profile consists of named components, each marked hard or soft. Hard gates require exactly zero defect; soft dimensions must satisfy their own exact rational tolerance. The scalar mean is retained only as a diagnostic.

`DEF-POS-01` contains twelve hard gates and five soft dimensions and is accepted. Six one-obligation controls are rejected. The bounded twelve-bit adversarial family examines 4096 profiles: 256 pass, while 4 have a mean defect no larger than one component out of twelve yet fail a hard gate. There are 32 equal-scalar accepted/rejected singleton pairs.

The exact downward-closure count covers 531441 ordered binary profile pairs, including 6561 accepted-upper premise pairs, with zero violations.

This is a finite structural audit semantics, not an empirical error model.
