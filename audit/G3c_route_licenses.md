# G3c — kernel-checked sufficient route licenses (TTH-09)

## Claim, classification, and status

**(b), TTH-09:** new raw route definitions and three generic sufficient-license theorems replace the old normalization schema as the row's evidence. The old declarations remain unchanged. Forced narrowing **N6** is applied only to the CST-TT-09 row.

Original CST-TT-08 text, preserved verbatim in the 09 rationale:

> Two admissible routes with the same boundary have the same temporal endpoint only under an explicit flatness, normalization, or confluence certificate.

New exact statement:

> Two admissible same-boundary routes have equal temporal endpoints when an explicit nonvacuous flatness, normalization, or confluence certificate licenses their comparison.

Status: **proved**. Ceiling: **structural endpoint sufficiency on a declared raw-path comparison domain; stronger adopted flatness license**. Flatness includes the decreasing completion ranks and shared unique normal form adopted in G3a, beyond G0. No inference of a license from endpoint coincidence remains. This is not a claim about a physical clock, recognition, a full package, or a Temporal-FIACH handoff.

Normative sources are the frozen `audit/G3_route_spec.md:22–102`, raw model JSON, and `audit/G0_generic_contracts.md:192–214`. The G3b finite outcomes are unchanged and are not used as Lean axioms.

## Generic statements and proof paths

Definitions: `lean/CSTTT/Transport/RouteLicenses.lean:11–142`.

`RawSystem R E B V S` is generic over route, event, boundary, vertex and state types. Its inputs are raw paths, boundary references, available events with actions and clock translations, boundary initial states, rewrite edges, ranks, critical comparisons, and completion paths. `Domain` is the predeclared same-boundary list. Only boundary decidable equality is needed for filtering; no Mathlib or finite-state axiom is used. A finite list domain is sufficient even when the ambient state type is infinite.

`execWord` (`:44`) folds raw event actions; `endpoint` (`:47`) executes that word on the boundary's raw initial state. There is no endpoint field. `DomainCheck` (`:62`) checks at least two **different raw event paths**, no repeated raw paths, admissibility/availability, shared boundary, and outgoing rewrite closure. Identical route IDs are not the criterion for distinctness. `domain_rejection_excludes_licenses` (`:221`) rejects all three licenses if the domain fails.

The exact signatures are:

```lean
theorem normalization_sufficient
    (m : RawSystem R E B V S) (d : Domain R B)
    (h : NormalizationLicense m d) (r s : R)
    (hr : r ∈ d.routes) (hs : s ∈ d.routes) :
    endpoint m r = endpoint m s

theorem flatness_sufficient
    (m : RawSystem R E B V S) (d : Domain R B)
    (h : FlatLicense m d) (r s : R)
    (hr : r ∈ d.routes) (hs : s ∈ d.routes) :
    endpoint m r = endpoint m s

theorem confluence_sufficient
    (m : RawSystem R E B V S) (d : Domain R B)
    (h : ConfluenceLicense m d) (r s : R)
    (hr : r ∈ d.routes) (hs : s ∈ d.routes) :
    endpoint m r = endpoint m s
```

Locations: `RouteLicenses.lean:153`, `:203`, `:164`. `routeIndependentEndpoint_generic` (`:228`) handles the disjunction. Each license contains the **defined** domain check, so the routes are admissible and have the same boundary; those facts are derived rather than omitted.

### Normalization

The license (`:88`) checks raw boundary/rewrite equations, decreasing ranks, rewrite action equality on **all input states**, and a shared unique reachable terminal image. `SharedNormal` (`:79`) defines this image directly from the raw relation. It does not take a normalizer function or normal-form table. `reach_execution` (`:145`) inducts over raw rewrite reachability to preserve execution. Both routes reach the same terminal form, hence execute identically. Shared boundaries identify their initial states.

### Confluence

The license (`:94`) checks raw rewrite soundness and joinability of **every pair in the whole domain**, not just local rewrite peaks. Both routes reach a common descendant; `reach_execution` derives execution equality. No rank or zero-clock premise is required by this mechanism.

### Stronger adopted flatness

The license (`:122`) checks nonempty distinct critical comparisons covering the domain, every completion's membership and actual paths, connectivity of the completion-move graph, decreasing proper completion reductions, the shared unique terminal completion image, raw action equations along completion paths, clock/action coherence, inverse clock equations, and zero relative clock holonomy on every selected completion.

Generic clock representation is a raw forward/backward translation table for each event. Checking both inverse equations realizes the inverse requirement that is built into G3a's Z/2 group. `clockWord` and `inverseClockWord` **compose those tables**, the latter in reverse order. The finite instance's translations are exactly the declared increment action `x ↦ x + increment mod 2`; the transcription script checks both forward and inverse evaluated maps. The generic proof therefore also applies to other invertible clock translations without assuming unverified group laws or an endpoint-factorization field.

`action_clock_word` and `clock_inverse_word` (`:172,:182`) prove the two compositional facts by induction on **arbitrary finite event words**. `completed_execution` (`:192`) derives equal executions from zero holonomy using the checked inverse equations. `flatness_sufficient` then inducts over the completion-move connectivity proof. Every critical pair and completion retains the frozen boundary-filter interpretation (either-side relevance, followed by checks of both sides). No favorable pair is selected after endpoint evaluation.

**Reachability representation:** Lean's `Reach` is the exact inductive reflexive transitive closure of the defined raw edge relation (`:71`). This represents all finite rewrite paths, not a bounded search. G3b computes that same relation by a finite fixed point. Here existence is proved by explicit paths and uniqueness/impossibility by induction over **all** paths. No supplied closure table, join verdict, or normal-form candidate is accepted.

Some license conjuncts are stronger than those strictly needed by the endpoint-equality proof; all are retained as gates and have raw-field rejection controls. Their proof fields are evidence of named predicates on the same raw data, never free `Prop` fields in `RawSystem`.

## Finite witnesses and the false converse

Source: `RouteLicenseModels.lean`. Data transcriptions cite JSON pointers `/shared_domains` and `/models/0,/models/1`. Source-order finite indices represent exactly the declared route/event/boundary/vertex sizes; event identity is preserved independently of its action table.

| Frozen G3b property | Kernel evidence |
|---|---|
| Necessity domain valid, all three paths supported | `necessity_domain` |
| r0/r1 equal endpoints | `necessity_equal` |
| r0/r2 separate endpoints | `necessity_separation` |
| r0/r2 nonidentity loop clock | `necessity_nonzero_holonomy` |
| No normalization, flatness, confluence on fixed D | `necessity_no_normalization`, `necessity_no_flatness`, `necessity_no_confluence` |
| Coincidence cannot define a license | `endpoint_coincidence_does_not_license` |
| Formal negation of literal necessity | `literal_necessity_false` |
| Both positive domains are valid | `positive_domain` |
| All three licenses on **each** positive domain | `positive_normalization`, `positive_flatness`, `positive_confluence` |
| Endpoint nonconstancy across boundaries | `positive_nonconstant` |
| Executed function nonconstancy on both bit inputs, every route | `positive_functions_nonconstant` |

The decisive statement is:

```lean
theorem endpoint_coincidence_does_not_license :
    DomainCheck necessity necessityDomain ∧
    endpoint necessity 0 = endpoint necessity 1 ∧
    ¬ RouteLicense necessity necessityDomain
```

`literal_necessity_false` negates the universal claim that endpoint coincidence of routes in this **fixed domain** implies one of the three licenses. It does not claim every smaller or alternative domain fails. The counterexample has no raw rewrite edges: induction forces any reachable route to equal its start, defeating shared normalization and joinability. No completion can be found in the empty raw completion list, defeating flatness already at G0's covering-completion requirement. The stronger adopted conditions are not the sole cause of rejection.

Nonemptiness is explicit: the positive domains have two distinct supported event paths, a real alias-to-normal rewrite, a valid covering completion, and a normal route. Their endpoint functions are nonconstant; equality within a fixed boundary is the desired licensed conclusion, not a globally constant endpoint definition.

## Argument classification

| Generic argument/object | Classification | Treatment |
|---|---|---|
| `R,E,B,V,S`, boundary equality instance | Raw domains / structural evidence | Types of raw tables and decidable boundary filtering |
| `m : RawSystem ...` | Raw data | Tables/functions, lists and ranks; no verdict or endpoint fields |
| `d : Domain R B` | Raw data | Boundary and route list fixed before comparison |
| `h : NormalizationLicense / FlatLicense / ConfluenceLicense / RouteLicense m d` | Evidence on raw data | Defined local equations and exact graph predicates, not arbitrary named propositions |
| `r,s` | Raw comparison inputs | Actual route IDs whose paths are checked |
| `hr,hs` | Evidence on raw data | Membership in the fixed domain |
| Endpoint, action fold, clock compositions and inverse, selected comparisons/completions, moves/reductions, reachable/terminal images | Defined objects | No independently supplied argument or result table |
| Admissibility, shared boundary and initial state agreement | Derived evidence | From the license's domain check |
| Normalizer/join/endpoint-factorization/status label | Absent as raw fields or theorem arguments | Reachable witnesses are proved inside defined graph predicates; execution equality is derived |

## Raw-field coverage and guards

Source: `RouteLicenseGuards.lean`. Every variant changes a raw field family without writing a verdict. A domain failure excludes **all** licenses by `domain_rejection_excludes_licenses`. These are method sensitivity tests, not new pre-registered scientific interventions.

| Raw field | Constraining law/check | Guard theorem |
|---|---|---|
| Route event path | Admissibility, raw-path distinctness/no-duplicates | `path_distinctness_guard`, `critical_path_guard` |
| Route boundary reference | Domain boundary equality and typed event vertices | `route_boundary_guard` |
| Domain boundary | Shared boundary check | `domain_boundary_guard` |
| Domain route list | At least two distinct raw paths, no repeats, rewrite closure | `domain_routes_guard` |
| Event availability | Every realized path event available | `availability_guard` |
| Event entry | Consecutive/entry vertex equations | `event_entry_guard` |
| Event exit | Consecutive/exit vertex equations | `event_exit_guard` |
| Boundary entry | Actual path start equation | `boundary_entry_guard` |
| Boundary exit | Actual path end equation | `boundary_exit_guard` |
| Boundary initial state | One shared raw boundary initial state; endpoint fold uses it | `initial_readout_guard` (nonconstant readout fails; lawful changes need not invalidate licenses) |
| Event action | Actual rewrite equations for all states; clock/action square | `action_guard` |
| Forward clock table | Action coherence and inverse equations | `forward_clock_guard` |
| Backward clock table | Both raw inverse equations | `backward_clock_guard` |
| Relative clock transport | Zero holonomy from actual composed tables | `holonomy_guard` |
| Rewrite edges | Raw path reachability, boundary closure and all-pairs joinability | `rewrite_guard`; necessity normalization/confluence negatives |
| Rank | Strict decrease on rewrites and proper completion reductions | `rank_guard`, `completion_rank_guard` |
| Critical comparisons | Nonempty covering set with distinct raw paths | `critical_nonempty_guard`, `critical_distinct_guard`, `critical_path_guard` |
| Completion rows | Every critical pair covered, every row checked | `completion_guard` |
| Completion left reference | Critical-pair membership and path start | `completion_left_guard` |
| Completion right reference | Critical-pair membership and path start | `completion_right_guard` |
| Completion join reference | Both actual paths end at the same raw join | `completion_join_guard` |
| Left completion path | Nonempty supported rewrite path with correct start/end | `left_completion_path_guard` |
| Right completion path | Nonempty supported rewrite path with correct start/end | `right_completion_path_guard` |
| Moves, reductions, closure, normal images, endpoints | Defined from the fields above | No extra replaceable field; controls propagate through these definitions |

The initial bit is an intentionally free lawful input. A license must work for every such input; a guard that rejected *all* changes to it would improperly narrow the theorem. Its sensitivity guard instead shows the declared positive nonconstant readout changes when that raw input is changed.

## Transcription coverage and checks

`RouteLicenseExport.lean` exports **evaluated definitions**, not a second table. `scripts/check_tth09_transcription.py` runs a read-only Lean probe under `/tmp` and compares the evaluated snapshot with the frozen JSON. Coverage: exact action tables on both bits, finite vertex counts, every route path/boundary reference, event entry/exit/availability/action ID/action output/clock increment/forward and inverse translations, all boundary fields, rewrite edges/ranks, critical pairs, every completion field/path, and all comparison domains. JSON IDs label source-order finite indices; metadata prose is not a semantic input. Three planted JSON drift checks change availability, a raw route path, or a clock increment and must be caught.

```bash
cd lean && lake build
cd ..
python3 -B scripts/check_tth09_transcription.py
python3 -B scripts/validate_lean.py --write-inventory
scripts/validate_lean.sh
```

Final receipts are appended after the build, transcription, validator and direct axiom probes finish. Only the TTH-09 09 row changes; its original 08 wording is included in `delta_rationale`. CST-TT-08 and the G3a/G3b frozen artifacts are untouched.

Final receipts:

- Full `lake build`: exit 0, **327 jobs**. The final cached whole-build run took **0.30 s**; observed new-module builds took approximately 1–5 s each. No warnings originate in the four new modules; existing vendor/legacy linter warnings are replayed.
- Transcription check: PASS for both models and every listed operative field. All three planted JSON drift cases are caught.
- `scripts/validate_lean.sh`: exit 0, overall PASS; **39 rows / 191 declaration entries**, no untrusted axioms, no placeholders, no high-confidence vacuity findings. There are 27 non-gating heuristic leads; the two new leads are the deliberately constant rank/fixed-boundary control data.
- Read-only `/tmp/g3c-axioms.lean` probes: **58 new theorems** resolve. Their transitive axiom union is **`propext`, `Quot.sound`**, with no `Classical.choice`, `sorryAx`, or `hiddenness_pending` dependency.
- Only TTH-09 changes in the 09 CSV. Counts are **6 proved, 14 checked finite countermodels, 11 conditional, 8 open**. Frozen G3a/G3b files and the 08 registry are byte-identical to HEAD. `git diff --check` is clean.

Self-review: all sufficient endpoint equalities are derived from raw execution, not projected from a supplied endpoint function/factorization. Raw-path domain distinctness guards reject duplicate paths with different labels. Each licensed comparison uses the same boundary initial state by construction. The only deliberately lawful unconstrained value is that initial state itself; its guard tests the dependent nonconstant readout rather than inventing a restriction on allowed initial values. The necessity result is scoped to the committed whole comparison domain. No remaining G3c proof blocker was found; arbitrary alternative license notions and physical-system interpretations are outside this result.
