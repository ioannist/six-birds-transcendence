# G3a — TTH-09 route predictions, fixed before evaluation

**Pre-registration only. Every entry below is a prediction, not a result.** Definitions and comparison domains are fixed in [G3_route_spec.md](G3_route_spec.md); raw data are in [TTH09-ROUTES.model.json](proposed_models/TTH09-ROUTES.model.json). No execution, closure, holonomy, or license computation is performed in G3a. The manager commits these files before G3b evaluates them.

License claims use the entire stated domain. Equal endpoints do not change that domain. No mutation or additional alternative model is introduced in this packet.

## Necessity model: TTH09-NECESSITY-01

`DomainCheck(D)` must be confirmed before this control is interpreted as a counterexample. A failed domain check invalidates that interpretation, even if endpoint coincidence and license rejection occur.

| ID | Property and fixed domain | Predicted verdict | Confidence | If the prediction fails |
|---|---|---|---|---|
| N-DOMAIN | `DomainCheck(D)` for the fixed three-route domain | **PASS** | High | The comparison domain is invalid; this control cannot be interpreted as a counterexample to license necessity. |
| N-NORM | `NormalizationLicense(D)` | **FAIL**: distinct routes remain distinct terminal rewrite forms, so no shared boundary normal form | High | Literal necessity has not been refuted by this mechanism; inspect whether the evaluator silently supplies a normalizer not reached by raw rewrites or selects a smaller domain. |
| N-FLAT | `FlatLicense(D)` | **FAIL**: covering completions are absent; the declared comparison containing the toggle is not zero-holonomy | High | The flatness definition or evaluation is accepting an empty completion or overlooking the fixed comparison domain. The proposed no-license countermodel would be unsupported. |
| N-CONF | `ConfluenceLicense(D)` | **FAIL**: the empty rewrite graph has no common descendant for two distinct routes | High | A coincident endpoint or route label has been mistaken for a rewrite join; alternatively the declared definition is not the one evaluated. |
| N-EQUAL | `Endpoint(r0) = Endpoint(r1)` with initial bit `0` | **PASS**, with predicted executed values `0,0` | High | The stipulated raw identity actions do not execute as intended; the necessity example fails. Do not repair the tables after evaluation. |
| N-DIFFERENT | `Endpoint(r0) ≠ Endpoint(r2)` with initial bit `0` | **PASS**, with predicted executed values `0,1` | High | The toggle branch is not separating the fixed domain; check raw action execution. |
| N-LOOP | `H(r0,r2) ≠ 0` as a clock-group element | **PASS**, predicted relative holonomy `1` (toggle) | High | The declared clock loop or inverse-composition convention is wrong; no nonflatness evidence may be claimed. |
| N-GLOBAL | All routes in `D` have one endpoint | **FAIL** | High | The fixed domain no longer establishes the intended global route separation. |
| N-CONVERSE | `r0/r1` agree, while `RouteLicense(D)` fails | **PASS** | High | The proposed finite counterexample to literal license necessity is not established. Retain necessity as unresolved rather than force a narrowing on this evidence. |

## Positive model: TTH09-LICENSE-01

| ID | Property and fixed domain | Predicted verdict | Confidence | If the prediction fails |
|---|---|---|---|---|
| P0-NORM | `NormalizationLicense(D0)` | **PASS** | High | The alias-to-normal rewrite/rank/action equations do not supply the boundary normal form; no normalization nonemptiness witness is available on this domain. |
| P0-FLAT | `FlatLicense(D0)` | **PASS** | Medium | The completion coverage, singleton normal-form, connectivity, or clock/action requirements are not actually met. Name the failed primitive check; do not weaken flatness. |
| P0-CONF | `ConfluenceLicense(D0)` | **PASS** | High | The raw finite rewrite closure does not join the declared pair; the positive confluence witness is unavailable. |
| P0-EQUAL | `Endpoint(a0) = Endpoint(n0)` | **PASS**, predicted executed values `0,0` | High | This invalidates endpoint preservation or execution for the first positive comparison, even if a defective license test passes. |
| P1-NORM | `NormalizationLicense(D1)` | **PASS** | High | The second boundary has no genuine normalized comparison; a globally constant first-boundary example cannot replace it. |
| P1-FLAT | `FlatLicense(D1)` | **PASS** | Medium | Common nonzero route translations were confused with nonzero **relative** holonomy, or some completion prerequisite fails. Report the actual failure. |
| P1-CONF | `ConfluenceLicense(D1)` | **PASS** | High | The second raw rewrite pair does not satisfy joinability/action preservation. |
| P1-EQUAL | `Endpoint(a1) = Endpoint(n1)` | **PASS**, predicted executed values `1,1` | High | The intended common toggle execution is not preserved; the positive boundary comparison is not established. |
| P-NONCONST | `Endpoint(n0) ≠ Endpoint(n1)` with both boundary initial bits fixed at `0` | **PASS**, predicted values `0,1` | High | The positive example is globally constant and does not close G0's positive-instance gap. This is a cross-boundary nonconstancy test, not a licensed cross-boundary equality. |
| P-FUNCTION | For every positive route `r`, `Exec(r,0) ≠ Exec(r,1)` | **PASS** | High | The positive endpoint functions collapse the input bit; the second independent nonconstancy check fails. |
| P-CLOCK | Raw event action/clock coherence on both positive domains | **PASS** | High | The clock transport is unrelated to executed state dynamics, so clock flatness cannot license these temporal endpoints. |

## Interpretation fixed before evaluation

The low-risk predictions are elementary raw bit/rewrite claims, but they remain unevaluated. The medium-confidence predictions are the positive **flatness** checks: their covering completion and unique-normal-form interpretation is made explicit in the spec so an evaluator cannot choose a weaker reading to obtain a pass.

If confirmed, the necessity example refutes the implication “pairwise endpoint coincidence implies at least one of these licenses on the fixed comparison domain.” It does not refute the sufficient-license theorem or every conceivable alternative notion of certificate. The positive example would provide nonconstant raw-execution witnesses for the three adopted sufficient mechanisms. Neither model is a physical handoff, a full Temporal-FIACH certificate, or evidence of endogenous temporal arrow.

G3b reports predicted-versus-computed outcomes and witnesses. Any failed prediction stays failed; revisions require a separately logged declaration. No TTH-09 promotion or row-text change is authorized by a prediction alone.
