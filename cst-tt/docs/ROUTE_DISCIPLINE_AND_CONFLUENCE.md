# Route Discipline, Holonomy, and Confluent Completion

## Positive finite control

`ROUTE-POS-01` is the smallest acyclic two-branch diamond in the declared family:

```text
        replace-left       complete-right
x -----------------> a --------------------> z
 \
  \ replace-right       complete-left
   ----------------> b --------------------> z
```

Both replacement orders reach one certified normal form `z`, with the same predictive endpoint, route residue, and clock translation. `TTH-09` follows from `CSTTT.RouteTheory.routeIndependentEndpointUnderNormalization` and endpoint factorization through that normal form.

The bounded shape search examined 354 candidates and first found a witness at four nodes. This is relative minimality under distinct start/branch/join nodes and an acyclic rank condition.

## Negative route-indexed control

`ROUTE-NEG-01` has the same current projection on two same-boundary routes but different predictive values, retained route residues, local-now values, and clock translations. It therefore:

- satisfies the route audit;
- satisfies memory-or-flatness through retained memory;
- fails the flatness certificate;
- witnesses nonzero translation holonomy;
- admits no route-independent boundary-level `now` factorization and therefore no global now on that declared boundary.

The binary one-boundary exhaustion tests both distinct local-now assignments against all four candidate factorization attempts and finds no counterexample to the obstruction theorem.

## Exact claim

Confluence is purchased, not inferred. The certificate is only about the declared finite route family. It does not establish a universal physical clock, route-independent personal identity, or temporal lineage.
