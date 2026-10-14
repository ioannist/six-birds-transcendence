# FIACH-POS-03 predictions, fixed before evaluation

These predictions apply to [the POS-03 declaration](proposed_models/FIACH-POS-03.model.json) under [M1_model_spec.md](M1_model_spec.md). POS-03 was designed after POS-02's C1 failure; that provenance is disclosed in the spec. **No POS-03 predicate or mutation has been evaluated.** A failed prediction will be retained against this version; any repair needs another model ID. “Pass” below means the declared finite or surrogate check, never a full P05/T17-I claim.

## Positive properties and handoff obligations

| Property | Predicted verdict | Meaning if prediction fails |
|---|---|---|
| C1 | **Pass predicted, low confidence.** The derived maintained recurrent CORE is nonempty; old powerset closure bookkeeping passes; exact `E₂^0` and `E₂^(1/16)` defects are recorded; the perturbed `E₂` fixed distribution is unique, nonuniform, and retains at least the unchanged `3/4` CORE mass. The carried-over `P_ε` stationary distribution separately retains at least `3/4` on the same computed CORE. T1 does **not** prescribe this route-anchored selector: with anchors on both route components it may admit nearly all maintained recurrent states, so passing retention chiefly limits **transient leakage**, with weak object-selection force. | Report both exact retention values, the fixed-point space, defects, and CORE membership. A failed subcheck blocks even the C1 surrogate and must not be repaired by moving ε, τ, threshold, or CORE after evaluation. |
| C2 | Pass: whole-kernel factorization defect is nonempty and the pre-registered `A0a/B0` split pair is among its witnesses. | A different accidental split pair cannot rescue the declared C2 witness. |
| C3 | Pass: action-profile refinement reaches computed `q` equivalence on every ordered kernel pair, and `q` determines the all-words continuation coordinate. | Give the first mismatched pair; no one-step proxy may be called terminal. |
| C4 | Pass at its surrogate ceiling: nonconstant declared public interface admits a same-current/different-future `A0a/B0` witness under a declared continuation. | The finite nonexposure pointer fails; even success would not prove HIDD's full exposure law. |
| C5 | Pass at its surrogate ceiling: the common edge-product rule derives genuine `self`, scheduled `other`, internalized `none`, null `none`. | Report exact channel products; no ownership label substitutes for computed credit. |
| C6 | Pass at its surrogate ceiling: nonduplicate same-code histories have the same future full-signature trace for every finite word; funded, heterogeneous order/tick/progress/record and target ownership checks pass. | Report a distinguishing word or failed finite law; a bounded horizon is insufficient for future sufficiency. |
| C7 | Pass: same-domain joint-pairing distributions strictly refine the conservative ordered branchwise control; local inverse laws and staged observable transport hold. | A display-only probe or malformed reassembly does not establish binding. |
| C8 | Pass: six-state target-owned funded viable kernel; the underfunding counterfactual has empty maximal viable subset. | Report the failed ledger row or surviving subset; mere shrinkage is not the predicted collapse. |
| TTH-03 bridge | Pass: all six histories, distinct past representatives in one predictive class, strict edge, raw state map, and typed successor/signature transport. | A stored bridge field cannot replace a failed raw equation. |
| Route status | `.routeIndexed` from two shared-endpoint routes with retained residue and differing `hit` future; no flat certificate. | Multiplicity without endpoint-persistent future relevance gives `.unresolved`. |
| Corridor | One strict mixed-support atomic leg with no gap and nonredundant synthetic source/target interventions. | Detached or unrealized support blocks lineage; the intervention rule remains toy semantics. |
| TTH-02 package at arrivals | Valid **surrogate** target package at both route arrivals, with no TTH-05 premise. Full P05 TTH-02 remains unestablished. | A C1 or other failed clause blocks even surrogate assembly. |
| TTH-05 preservation | Valid state-indexed **surrogate** package at every target state. | A later-state failure blocks preservation despite any valid arrival. |
| TTH-04 composition | One leg only; nontrivial two-leg composition remains **not exercised**. | Any report of a positive two-leg witness from this fixture exceeds its data. |
| TTH-06 | All raw source/target, staged, bridge, corridor, route, autonomy, package, endpoint, and `notAddressed` links support a **surrogate** structural handoff; full Temporal-FIACH remains unestablished. | Identify the failed lane or link; do not promote TTH-06 from partial lanes. |
| T17-I | **Open**; no full design/02 integrated P05 certificate or soundness theorem is declared. | Calling this solved would exceed the claim ceiling. |

## Every declared mutation

The same positive-case predicate must be run after each listed raw edit. Local well-formedness is reported separately. IDs absent from the M1 diff list carry their POS-02 mutation rules unchanged.

| Mutation | Predicted response | Meaning if prediction fails or is qualified |
|---|---|---|
| `NEG-C6-CODE` | Future sufficiency fails on a same-code/different-`hit`-future pair. | The fixed `q` would not discriminate a substantive predictive defect. |
| `NEG-C6-HEALTH` | Future sufficiency fails after raw health/maintenance collision. | The declared health interface or all-words check misses the intended distinction. |
| `NEG-C7-NO-JOINT-OBSERVABLE` | `R_rec=K_bw` with well-formed raw assembly after deleting joint observables. | If strictness remains, the quotient reads undeclared joint data. |
| `NEG-C7-UNCOUPLED` | **Well-formed** local reassembly, fixed `jointPairing` interface, but one recombination class and no strict refinement. | Any local inverse-law failure makes this `INVALID-CONTROL`; retained strictness would refute the fixed-coupling factorization prediction. |
| `NEG-PKG-ENDPOINT` | Local C1 token deletion invalidates an otherwise valid arrival surrogate package. | If baseline package fails, count only `CONFIRMED-NARROW`, not loss of a valid package. |
| `NEG-PKG-LATER` | Later-state C1 token deletion invalidates otherwise valid state-indexed preservation while arrivals remain valid. | If baseline preservation fails, count only `CONFIRMED-NARROW`. |
| `NEG-C8-UNDERFUND` | Recomputed maximal positive-budget viable subset is empty. | Report every survivor; shrinkage alone is insufficient. |
| `NEG-BRIDGE-REP` | Raw A0b remap breaks representative/predictive/route transport. | A bridge proof field cannot hide a bad map. |
| `NEG-BRIDGE-EDGE` | Deleting the named strict frontier edge fails bridge edge coverage. | The edge obligation would be absent or untested. |
| `NEG-ROUTE-ERASE` | Route status becomes `.unresolved` after endpoint residue collapse. | Route indexing must read endpoint data, not merely path count. |
| `NEG-CORRIDOR-DETACHED` | No mixed support; strict corridor fails. | A detached copy must not pass Temporal-FIACH lineage. |
| `NEG-CORRIDOR-GAP` | Unrealized mixed stage fails no-gap. | A corridor predicate that ignores realized support is too weak. |
| `NEG-TTH06-LINK` | Handoff endpoint link fails while lanes remain untouched. | The certificate must derive the shared endpoint. |
| `NEG-C6-ORDER` | Zero order increment fails strict unfolded order. | Tick alone is not an order proof. |
| `NEG-C6-SUCCESSOR` | Missing B1safe/hit response fails successor totality. | An incomplete response table cannot prove all-word closure. |
| `NEG-C6-TICK` | Redirected A0a/nominal response fails phase toggle. | Raw action metadata alone must not dictate successor phase. |
| `NEG-C6-ARROW` | Externally owned A0a/hit action fails endogenous arrow. | Owner labels in unrelated fields cannot rescue it. |
| `NEG-C7-PRESERVATION` | **Well-formed** source and target local assemblies and commuting reassembly map, but joint-observable transport fails. | Any local or other staged failure makes the transport negative confounded. |
| `NEG-C1-CLOSURE` | Deleted response makes the Markov row incomplete and changes recomputed reachability closure/defect data. | It tests raw closure sensitivity; a missing-row control is not an isolated retention ablation. |
| `NEG-C2-SPLIT` | Whole-kernel defect becomes empty, including the declared split pair. | A surviving pair refutes the proposed public-readout exposure. |
| `NEG-C3-PROFILE` | Terminal refinement separates same-`q` histories; terminal-equals-`q` fails. | A one-step profile must not be mistaken for a predictive quotient. |
| `NEG-C4-EXPOSE` | Expanded raw channels remove the declared hidden pair. | Hiddenness is interface-relative; a survivor needs an explicit witness. |
| `NEG-C5-SCHEDULE` | Genuine cycle credit moves from `self` to `other`. | Report exact products; ownership alone cannot force the result. |
| `NEG-C5-INTERNALIZED` | Removing reverse edges changes balanced `none` to `ambiguous`. | A dual-asymmetry control must not receive self credit. |
| `NEG-C1-UNMAINTAINED-RECURRENCE` | The carried-over `P_ε` stationary retention and, **with low confidence**, the new `E₂^(1/16)` fixed-distribution retention both fall below `3/4` when the externally owned B recurrent component is excluded by the fixed route-anchored CORE rule. T1 does not prescribe that selector; this control mainly probes how its maintenance filter changes recurrent coverage. | If either retention check passes, report that exact value and qualify or fail the control; if C1 becomes undefined or other clause failures dominate, report that separately. Do not tune the selector or threshold. |

**Least confident:** C1's exact `E₂^(1/16)` retained mass and nonuniformity; the new C1 maintenance negative's retention effect; the fixed-interface C7 uncoupled control's full local/staged well-formedness; and whether the C7 transport negative isolates that equation after all staged checks. The new C1 prediction is scientifically decisive for POS-03's package and surrogate handoff; no declaration file may be edited after its evaluation.
