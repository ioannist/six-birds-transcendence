# G3a — TTH-09 route licenses: pre-registered definitions

**Declaration only. No endpoint, holonomy, reachability, normal-form, or license verdict has been computed.** The tables and predictions are to be committed before G3b. Only syntax, types, and reference integrity are checked here. This packet changes no Lean declaration or registry row.

## Authority and scope

The authority is [G0_generic_contracts.md](G0_generic_contracts.md), TTH-09, lines 192–214. In particular:

> “`endpoint r` is the fold of the raw action table, not a stored route verdict.”

> “Endpoint equality then follows by the shared normal form.”

> “`r.endpoint = s.endpoint` is neither a field nor enough to construct this license.”

> “Unlike flatness, [confluence] needs no zero-clock law.”

The G0 necessity sketch fixes three one-event routes, an empty rewrite graph, and `D = {r₀,r₁,r₂}`. G0 also identifies the constant endpoint of `diamondCertificate` as an inadequate positive instance and proposes the sufficient-license wording for TTH-09. That wording/status decision is **not applied** by G3a.

The raw declaration is [TTH09-ROUTES.model.json](proposed_models/TTH09-ROUTES.model.json). It contains two models, not computed certificates. There are no endpoint, normalizer, license, or holonomy-result fields. Available events, boundary initial bits, action tables, clock increments, ranks, rewrites, critical pairs, and completion paths are primitive data. The two-element clock group and its action on the bit are declared synthetic finite semantics; no physical-clock interpretation is asserted.

## Raw execution and comparison domains

Let `B = {0,1}` and `G = Z/2Z`. An event has an entry/exit vertex, an action table `B → B`, a clock increment in `G`, and availability. A route is a boundary reference and a list of event references. A boundary has an entry vertex, exit vertex, and initial bit.

`AdmissibleRoute(r)` checks that every event is present and available, adjacent event vertices match, and the first/last vertices match the declared boundary. An empty event path is permitted only when the boundary entry equals exit. All declared routes here have one event. Route identity is its distinct raw event path, not an endpoint label.

Define the **executed function**, without any supplied endpoint:

```text
Exec([], x) = x
Exec(e :: tail, x) = Exec(tail, action(e)(x))
Endpoint(r) = Exec(events(r), initial(boundary(r)))
```

`Clock(r)` is the sum modulo 2 of its event increments. Let `ρ(g)(x) = x + g mod 2`. The primitive action/clock coherence check is:

```text
for every available event e and x in B:
    action(e)(x) = ρ(clock_increment(e))(x).
```

This is checked on the raw one-step tables, not assumed as an endpoint-factorization field. By induction it links execution of arbitrary supported event words to clock composition. The declared relative loop holonomy is

```text
H(r,s) = Clock(r) - Clock(s) in G.
```

It is the clock transport along `r` followed by inverse transport along `s`. `H = 0` means the **identity map**, not that one selected initial clock happens to be fixed. This supplies the clock-loop interpretation for G0's toggle route.

A comparison domain `D` is a fixed list with a declared boundary. `DomainCheck(D)` requires at least two distinct routes, no repeated entries, admissibility of all members, identical declared boundaries, and closure under the raw rewrite edges originating in `D`. A comparison is legal only for `r,s ∈ D`. The domains never shrink after looking at endpoints or failed licenses.

Reachability below is **reflexive transitive graph reachability**, computed by a finite fixed point on the declared route domain in G3b; it is not a bounded rewrite search. No candidate normalizer is a free result field.

## 1. Normalization license

This fixes G0's decreasing-rank, reachable boundary-canonical normal-form mechanism (`G0:198`). For the raw rewrite graph `R` restricted to `D`:

1. `DomainCheck(D)` holds.
2. Each raw rewrite preserves the boundary and stays in `D`.
3. The declared natural-number rank strictly decreases on **every** rewrite edge in `D`.
4. For each raw rewrite `(u,v)`, the raw action equations give `Exec(u,x) = Exec(v,x)` for **every** bit `x`. This check folds the action tables; no `endpointFactors` proof field is read.
5. A terminal route has no outgoing rewrite in `D`. For each `r`, compute `NF_R(r)`, the set of reachable terminal routes. It is a singleton, and its sole member is the same for every route of the declared boundary.

`NormalizationLicense(D)` is the conjunction of these checks. The normalizer and canonical boundary normal form are **defined from these reachable terminal sets**, not supplied. Rank guarantees termination; rewriting preserves execution; the shared normal form then derives equality of endpoints. Empty `R` does not by itself buy normalization on a multi-route boundary: each route remains a different terminal route.

## 2. Flatness license

This adopts G0's covered nonempty critical comparison, raw completion, clock, and connectivity mechanism (`G0:199`). Condition 5 additionally requires decreasing completion ranks and a shared unique normal form **beyond the G0 contract**. This is a stronger adopted flatness license; G0 does not require those additional conditions.

A critical pair is a declared pair of **distinct same-boundary route paths**; it need not be a branching rewrite peak. This follows G0's route-comparison usage. Each completion consists solely of `left`, `right`, `join`, and two lists of route references from each side to `join`. Lists with one vertex are reflexive paths; longer lists must follow raw rewrite edges. No endpoint equality occurs in this record.

For a domain `D`, filter critical pairs by its boundary and check:

1. `DomainCheck(D)` and raw event action/clock coherence hold.
2. The critical-pair set is **nonempty**. Each pair has distinct sides in `D`, and every route of `D` occurs as a side of a critical pair. Thus this is a covering comparison, not an empty universal quantification.
3. Each critical pair has a raw completion. Its join and all path vertices are in `D`; both completion paths use raw rewrites. If multiple completions are listed, every one must be valid and checked.
4. The elementary undirected completion-move graph has an edge between the two sides of each completed pair. **Every pair of routes in `D` is connected** in that graph.
5. Form the directed completion-reduction graph `Q`: add `left → join` and `right → join`, omitting identity edges. Each is backed by its actual rewrite path, and the raw rank strictly decreases on each proper reduction. Compute terminal reachability in `Q`. Each route has a unique reachable terminal normal form, the same for the whole boundary. This is the required covering completion's unique normal form, not an endpoint-selected representative.
6. For every completed critical pair `(u,v)`, `H(u,v) = 0`. Equivalently the clock transport around its comparison loop is the identity. A completion join gives the square of route/rewrite paths; the declared raw rewrite action equations are checked along both paths, as in normalization check 4. Holonomy and action coherence are separate checks.

`FlatLicense(D)` is the conjunction. Endpoint equality is derived by moving through the connected completion graph: zero relative clock transport and the one-step clock/action equations preserve execution on each elementary comparison. The normal form also anchors the covering completion. Coincident endpoints on one initial bit supply none of the rank, coverage, completion, connectivity, normal-form, or clock laws.

Flatness is not a copied `.flat` label. Its zero-holonomy condition checks entire clock maps. In this small declared family, the action/clock relation is deliberately exact; extending these definitions to arbitrary non-clock state observables would require an independently checked action of the clock/completion structure on those observables, not mere clock equality.

## 3. Confluence license

This fixes G0's global same-boundary joinability and finite closure alternative (`G0:200`).

1. `DomainCheck(D)` holds; raw rewrites preserve boundary and domain.
2. Every raw rewrite preserves `Exec(–,x)` for every bit, by the same raw action equations as normalization check 4.
3. Compute `R*` by a finite reachability fixed point. For **every** `u,v ∈ D` with the declared boundary, there exists a route `j ∈ D` with `u R* j` and `v R* j`.

This is stronger than merely checking forks from one starting route: it is the comparison-domain joinability G0 requires. It includes every pair of descendants of a raw branching route because rewrite closure keeps them in `D`. The finite joinability closure proof is the accepted alternative to a termination requirement. No zero-clock or completion certificate is needed by this mechanism. Endpoint agreement follows by rewriting both routes to their common descendant.

Define `RouteLicense(D)` as the disjunction of the three licenses. The future G3c theorem takes a checked domain and one of these mechanisms; its endpoint agreement is a **conclusion**. It does not take endpoint coincidence as evidence for any license. The individual checks may evaluate equality of executions on **raw rewrite edges**; that is the permitted local rewrite soundness law, not the all-pairs target conclusion under another name.

## The declared models

### TTH09-NECESSITY-01

- Bit states `0,1`; one boundary from `entry` to `exit`, initial bit `0`.
- Routes `r0,r1,r2`, each with its own one-event path `e0,e1,e2`.
- Events `e0,e1` read the identity action table and clock increment `0`; `e2` reads toggle and clock increment `1`.
- Fixed `D = [r0,r1,r2]`; rewrite edges and completions are empty; all raw ranks are `0`.
- Critical comparison pairs are `[r0,r1]`, `[r0,r2]`, `[r1,r2]`, fixed before evaluation. Their lack of completions is legal raw model data and an intended **license** failure, not a reference-integrity error.

Predictions identify the `r0/r1` coincident endpoint pair and the `r0/r2` nonzero clock loop. License claims are over **all of D**, not only `r0/r1`. This is a proposed countermodel to literal necessity **with the comparison domain fixed in advance**. It does not assert that no smaller endpoint-selected domain could ever possess a different certificate.

### TTH09-LICENSE-01

- Bit states `0,1`; boundaries `b0: entry → exit0`, `b1: entry → exit1`, both with initial bit `0`.
- For each `i`, two distinct one-event routes `a_i,n_i` have different event IDs but the same boundary. The `b0` events use identity with clock increment `0`; `b1` events use toggle with clock increment `1`.
- Fix `D0 = [a0,n0]` and `D1 = [a1,n1]`. They are **separate same-boundary comparison domains**; no cross-boundary comparison is licensed.
- Raw rewrites are `a0 → n0`, `a1 → n1`, with ranks `1` for `a_i` and `0` for `n_i`.
- Critical pairs are `(a_i,n_i)`. Their raw completion has join `n_i`, left rewrite path `[a_i,n_i]`, right path `[n_i]`. The reflexive right leg is explicit; the left leg is a real rewrite between distinct paths, not an endpoint-equality assertion.

This is the smallest two-boundary, nonconstant positive family with a distinct compared pair on each boundary. All three mechanisms are predicted to hold on each fixed domain. Nonconstancy is predicted across `b0/b1`, and each route's executed function is also predicted nonconstant on its bit input. Within one licensed boundary and fixed initial bit the endpoint must be constant **across routes**; asking for nonconstancy there would contradict the conclusion being licensed. The model therefore avoids the old globally constant `diamondCertificate.endpoint` while retaining genuine same-boundary agreement.

Sizes are counts of declared data, not computed verdicts:

| Model | Bit states | Vertices | Boundaries | Events/routes | Rewrite edges | Domains | Critical pairs/completions |
|---|---:|---:|---:|---:|---:|---:|---:|
| NECESSITY-01 | 2 | 2 | 1 | 3 / 3 | 0 | 1 | 3 / 0 |
| LICENSE-01 | 2 | 3 | 2 | 4 / 4 | 2 | 2 | 2 / 2 |

## Declaration integrity and next packet

G3a checks JSON parsing, unique raw IDs, action-table dimensions/types, clock/rank types, references in event/route/boundary/domain/rewrite/critical/completion tables, and the schemas of completion paths. It **does not** fold an action, sum a clock word, compute graph closure, check rank inequalities, or evaluate a license. Empty completions and rewrites are allowed schemas. No evaluator or Lean probe is run here.

G3b must compute every prediction independently from the committed tables, using finite graph fixed points and exact bit/group operations. If a prediction fails, report it without changing these declarations. G3c then proves the sufficient mechanisms and any confirmed necessity countermodel; status/text updates belong to that later packet.

Declaration receipt: JSON schema/type, unique-ID and reference checks passed for both models using Python's standard library. No action fold, clock composition, graph fixed point, rank-decrease law, or license was evaluated. The unchanged existing Lean tree passes `cd lean && lake build` (323 jobs); it does not import or evaluate these JSON declarations. `git diff --check` is clean. Only the three requested new audit artifacts are changed.
