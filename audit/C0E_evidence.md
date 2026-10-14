# C0E — computed semantics before a new handoff claim

Research/design only. The verdicts below concern the **frozen raw tables**, not the booleans in their `assignment` objects. The current Python evaluator reads `future_sufficient`, `order_stable`, `successor_total_on_viable`, `tick_viable`, `arrow_endogenous`, `binding_integrated`, `recombination_relation_preserved`, and `viable` back from the assignment ([`_clause_rule`](../cst-tt/src/cst_tt/package_gluing.py#L222-L277)). Thus the old certificate verdict does not establish these meanings. Definitions here are proposed contracts, not implemented Lean proofs.

The [integrated-package semantics](../cst-tt/docs/INTEGRATED_PACKAGE_SEMANTICS.md#L33-L33) identifies C6 as “substantive C6 temporal closure” and lists C7/C8 as separate package obligations. Therefore operational C6 cannot silently stand in for integrated binding or viability.

The proposed `(tick phase, cumulative progress, cumulative record)` interface is **new and restricted**. It was selected with the frozen outcomes already known, so its positive result is exploratory and cannot retrospectively validate the frozen C6 future-sufficiency flag. Public report alone is constant and would make sufficiency empty. Health is an available future observable that this restricted interface excludes. The paper's future-sufficiency definition permits a declared observation interface: “for each continuation-event pair there is a function ...” from the state code to the future observation ([Holonomy-with-Memory paper, future-sufficiency theorem](../../six-birds-papers/Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex#L362-L394)). The [notation scaffold](../cst-tt/vocabulary/TYPE_AND_NOTATION_SCAFFOLD.md#L16-L23) similarly makes predictive equivalence relative to declared continuations. The C6 temporal components motivate this choice, but it was **not** fixed before seeing AUT-POS-01. A stronger interface including health refutes the phase code, as shown immediately below.

## 1. C6 `future_sufficient`

**(a) Definition/source.** [C6](../cst-tt/docs/C6_TEMPORAL_SUBSTANCE.md#L3-L14) says “C6 is not a Boolean label” and separately requires a “future-sufficient predictive now.” Let `F(x,w)` be the phase/progress/record trace produced by the unique finite run from viable state `x` under disturbance word `w`. A code `q` is sufficient iff `q(x)=q(y) → F(x,w)=F(y,w)` for every viable `x,y` and every word `w`; equivalently every trace factors uniquely on the reachable image of `q`, as in the [paper](../../six-birds-papers/Tsiokos_2026_Holonomy_with_Memory_in_Six_Birds_Theory_Predictive_Quotients_Witnesses_and_Fixed_Support_Route_Transport.tex#L379-L394).

**(b) Failure control.** Keep the frozen static C6 tag/list as `q` and use `w=[nominal]`: `SAFE-0` and `SAFE-1` have equal code but successor phases 1 and 0. The all-state identity code would pass by construction and is rejected as evidence. A phase code is coarser than the full state: `SAFE-0` and `WARNING-0` share phase 0. Under `hit`, however, `SAFE-0 → WARNING-1` (warning health) while `WARNING-0 → SAFE-1` (safe health). Thus it **fails** future sufficiency as soon as health is observed. This counterexample sits beside, and limits, the restricted positive result.

**(c) Frozen verdict: fails; restricted-interface pass is near-automatic.** The target C6 assignment has one `cross_predictive_tag = predictive:T:rank2` ([model](../cst-tt/models/packages/PKG-POS-04-FIACH-TARGET.model.json#L110-L145)). The two nominal transitions above are in [AUT-POS-01](../cst-tt/models/autonomy/AUT-POS-01.model.json). The stored `true` disagrees with the static-code interpretation.

**(d) Draft extension.** `FIACH-POS-02` adds `predictive_now_by_state[x] := tick_phase(x)`, computed from AUT's state table, and leaves all frozen values intact. All eight transitions flip phase modulo 2 and have identical progress and record increments of 1. Consequently the restricted factorization is **near-automatic** from the transition schema; induction on words adds little discriminating force. This **changes the science** from a static package code to a state-dependent package interpretation, and does **not** validate the frozen static C6 code. It fails for health, as the `hit` pair above shows, and does not establish every future observable in the paper's unrestricted interface. If the original C6 requires those, demote to “future-sufficient for the declared phase/progress/record interface of AUT-POS-01.”

## 2. C6 `order_stable`

**(a)** [C6](../cst-tt/docs/C6_TEMPORAL_SUBSTANCE.md#L7-L14) requires “stable order”; the [C6 card](../cst-tt/corpus/clause_cards/C6.md#L8-L21) calls for a funded order/tick/arrow on the staged phase carrier. Define stability as strict increase of declared corridor `order_rank` across each stage edge, followed by nondecreasing **unfolded event order** under target actions, with strictly positive record increments. A cyclic finite phase label itself is not an absolute order.

**(b)** Swap the existing corridor ranks at stages 1 and 2, or set one action's record delta to 0; the rule fails. It does not hold merely because a field says `true`.

**(c) Frozen verdict: substantive-pass at this event-order ceiling.** Corridor ranks are `0<1<2`; every target action has record delta 1. An absolute order on the four cyclic controller states would fail (`SAFE-0→SAFE-1→SAFE-0`), so that stronger reading is explicitly excluded.

**(d)** No new value. Lean must construct unfolded record order from transition deltas. If the row demands a strict order on the finite state set itself, demote that reading.

## 3. C6 `successor_total_on_viable`

**(a)** [C6](../cst-tt/docs/C6_TEMPORAL_SUBSTANCE.md#L8-L11) says “viable successor available.” Define `∀ x∈K, d∈{nominal,hit}, ∃!` a listed target-owned action and successor in `K`, with action resources retained and ledger update satisfied. `K` is the declared four-state candidate, subject to the independent C8 invariant check.

**(b)** Delete `WARNING-1/hit` from a copy of the table: one of eight required pairs is uncovered.

**(c) Frozen verdict: substantive-pass operationally.** Eight distinct entries cover `4×2`; all successors remain in the four-state set, actions have owner 101, and required resources are retained. The full clause remains conditional on the C8/package interpretation.

**(d)** No new value; derive from the transition/action tables rather than `successor_total_on_viable=true`.

## 4. C6 `tick_viable`

**(a)** [C6](../cst-tt/docs/C6_TEMPORAL_SUBSTANCE.md#L9-L12) requires a “viable tick” and “strictly positive tick progress.” Define each viable response to satisfy `phase(y)=(phase(x)+1) mod tick_modulus`, `progress_delta>0`, and `y∈K`. The modulus is the declared AUT value 2.

**(b)** Redirect `SAFE-0/nominal` to existing `SAFE-0`, or replace its progress delta with the existing zero cost value; either fails.

**(c) Frozen verdict: substantive-pass operationally.** All eight responses flip `0↔1`, have progress delta 1, and stay in the candidate `K`.

**(d)** No new value. The corridor exit index 2 and AUT endpoint phase 0 agree by `2 mod 2 = 0`; this is the endpoint convention, not an equality of raw tick indices.

## 5. C6 `arrow_endogenous`

**(a)** [C6 card](../cst-tt/corpus/clause_cards/C6.md#L19-L33) requires progress and arrow to be “target-endogenous” and identifies an external schedule as a failure mode. Require each postwithdrawal response action to be owned by 101, use only retained target resources, have positive record delta, and use no removed scheduler. Define cumulative record on a run by `record(next)=record(current)+record_delta`; link its starting value to target C6 `record_before=3` and the first edge to `record_after=4`.

**(b)** Change one action owner to source 17, require `external-scheduler`, or make its record delta 0; the universal property fails.

**(c) Frozen verdict: substantive-pass for the declared controller.** Eight owners are 101, all deltas are 1, and all action resources are retained; target C6 has `3<4`. This does not establish an unmodeled physical clock.

**(d)** No new value. The recurrence is a derived run semantics; it must be proved in Lean from action data.

## 6. C7 `binding_integrated`

**(a)** The [C7 card](../cst-tt/corpus/clause_cards/C7.md#L8-L21) calls the primitive “strict recombination quotient refinement `R_rec ≻ K_bw`” on **joint branch histories** and asks to distinguish it from independent copies. At the *finite relation* ceiling, take `K_bw` as the two unary branch marginals and `R_rec` as a joint relation. Strictness means that the relation is nonempty, has both full marginals, and is a proper subset of the Cartesian product of those marginals. Full integrated binding additionally requires that pairs arise from actual joint histories and that the operational package uses them.

**(b)** Replace the target off-diagonal relation by the Cartesian product on its two existing branch labels. Marginals remain full, but strictness fails. This distinguishes relation content from a `true` flag.

**(c) Frozen verdict: undefined for integrated binding.** The target has two off-diagonal pairs of four Cartesian possibilities, so strict **finite relation information** passes. No joint-history or recombination operation table witnesses that this is integrated binding; `joint_relation_tag='xor:T'` is a name. The [C7 card](../cst-tt/corpus/clause_cards/C7.md#L14-L17) itself says no integrated instance is exhibited.

**(d)** No honest rule derives missing joint histories from the frozen pair names. A new experiment/model must supply histories, decomposition/reassembly maps, and behavior; no invented table is proposed. Demote to “the declared two-branch recombination relation strictly refines its branchwise marginals” until such data exist.

## 7. C7 `recombination_relation_preserved`

**(a)** [C7](../cst-tt/corpus/clause_cards/C7.md#L19-L21) says preserve joint recombination information across decomposition/reassembly. On the available table, use the staged map of source branch labels to target labels and check a biconditional on **all four** ordered source pairs: `(a,b)∈R_S ↔ (f(a),f(b))∈R_T`, with `f` bijective on the declared branch sets. A forward-only implication would permit added target pairs.

**(b)** Delete one target off-diagonal pair or add a diagonal pair. The biconditional fails while the branch map remains total.

**(c) Frozen verdict: substantive-pass at finite-relation ceiling.** The map `S:L↦T:L`, `S:R↦T:R` carries precisely the two off-diagonal source pairs to the two off-diagonal target pairs; all four membership comparisons agree. This says nothing about unrepresented joint histories.

**(d)** No new value. The bridge must compare the mapped **source** table against independently read target table, not read `recombination_relation_preserved=true` or merely compare target labels.

## 8. C8 `viable`

**(a)** The [C8 card](../cst-tt/corpus/clause_cards/C8.md#L8-L8) requires a “nonempty maintained viability kernel under declared ledger; underfunding collapse.” Define `K` as a nonempty set containing the endpoint, whose every state has positive budget, target-owned maintenance, retained required resources, and whose every declared disturbance has a target-owned response in `K` satisfying `budget(y)=budget(x)-cost+regeneration`; positive regeneration requires the retained target regenerator. That is the declared operational C8 ceiling: a maintained, funded, target-owned kernel. TTH-02 separately needs a target package at assembly, with its own C6/C7 checks and this operational C8 clause; it reads raw target dynamics/ledger data for C8 but assumes no postwithdrawal autonomy theorem or TTH-05 result. The later TTH-05 package-preservation claim additionally requires a genuinely checked C1–C8 package predicate at each state. Raw state-indexed data may be shared without reversing the proof dependency.

**(b)** Remove `target-regenerator` from retained resources: warning-state actions of cost 1 and regeneration 1 lose their funded response. Alternatively set warning regeneration to 0; computed next budget becomes 0, outside `K`.

**(c) Frozen verdict: substantive-pass for C8 at its declared operational ceiling.** The declared four-state `K` contains `SAFE-0`; all budgets are 1; all eight ledger equations read `1=1-cost+regeneration`; response resources are retained. All eight responses remain in `K`, with target ownership and retained resources. The per-state `package_valid=true` values do not provide a per-state C1–C8 assignment or a checked dynamic C6, so **TTH-05 full package preservation remains undefined**.

**(d)** The phase-code draft helps C6 but supplies no per-state package assignments for C1–C8. No honest rule derives those assignments. Retain the C8 operational pass at its declared ceiling. For TTH-05, use “AUT-POS-01 has a nonempty target-owned, funded controlled invariant over its declared disturbances; per-state integrated-package preservation is unestablished” unless an independent state-indexed package model is supplied.

## 9. Route status and non-vacuous flatness

**(a)** [Route Completion](../cst-tt/docs/ROUTE_COMPLETION.md#L3-L10) requires retained nontrivial residue for `route-indexed`, but `flat` needs “joining critical pairs, a unique normal form, and zero clock-translation holonomy.” [Memory or Flatness](../cst-tt/docs/MEMORY_OR_FLATNESS_THEOREM.md#L5-L16) motivates memory when same-current routes have different future values. First declare which event-dependency paths represent **theory routes**; the frozen model does not make that identification. Only then define comparison domain `D` as distinct theory routes with the same boundary. A flat certificate requires `D≠∅`, a declared rewrite/completion system covering every pair, a unique normal form, and explicit route clock-translation maps whose holonomy is zero on every pair. Computed `.routeIndexed` requires `D≠∅` **and** an endpoint-accessible residue/provenance value for each route that distinguishes the compared histories; no certified flatness is also required. Otherwise the computed status is `.unresolved`. The stored `route_status` remains a declared model label, not input to `routeStatusOf`.

**(b)** Delete either mixed branch dependency: the candidate path-pair domain becomes empty, so neither flat nor route-indexed fires. Merge the two path-specific endpoint residues into the one frozen residue list: route-indexed fails even if two paths remain. A model with two paths but no completion/clock data cannot receive `.flat` by vacuous universal quantification.

**(c) Frozen verdict: declared model status with computed path multiplicity; route-memory evidence undefined.** `COR-POS-01` has two directed paths `s-entry → source-mixed → t-exit` and `s-entry → target-mixed → t-exit`. Their middle-event identifiers distinguish the **paths in the graph**, but both feed the same `t-exit`, whose stage carries **one** residue list. The model does not say that these dependency paths count as theory routes or where either path's provenance persists at the endpoint. The stage residue list grows, but that proves neither retained route memory nor nonflatness. No rewrite critical-pair universe or path-specific clock-translation maps are supplied, so no flat certificate can be computed. The frozen `route-indexed` field is a declared status, not a computed pass.

**(d)** The draft `FIACH-POS-02` records two **candidate dependency paths** by exhaustive traversal of the existing event DAG. It adds no endpoint path-specific residue or clock values. A future route-indexed proof needs an independently justified theory-route interpretation and raw evidence locating each path's persistent provenance at `t-exit`; a flat upgrade also needs independent completion/clock evidence.

## 10. TTH-03 representative bridge and history coverage

**(a)** [Heterogeneous Temporal Transport](../cst-tt/docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md#L17-L28) says `TR-POS-01` has “two representatives of one predictive class” and that both induce the same target predictive value. A genuine FIACH bridge must have a nonempty reachable frontier with an actual strict source edge, **two distinct source histories in one predictive class**, a total raw state map on that frontier, equal target predictive images of both representatives, and checked preservation of successor/order/tick/progress/record/ownership/route laws. `BridgeTableCheck` is only raw map lookup, coverage, and source/target table equations; conclusions are proved separately.

**(b)** On TR-POS-01, map its two representatives to different target predictive values: representative independence fails. On FIACH, deleting a C6 map entry or the strict source edge fails coverage. A singleton relation is prohibited as the positive witness.

**(c) Frozen verdict: undefined.** FIACH's source package and corridor give `record 0→1`, stage `0→1`, but no distinct source-history representatives or history coverage map. `TR-POS-01` is separate: source record `3→4`, target `30→40`, unlike FIACH's `0→1` and `3→4`; no certificate identifies the systems. Its nontrivial witness cannot be transplanted by name.

**(d)** No rule derives the missing histories or cross-model alignment. Do not fabricate a duplicate representative. Demote the proposed FIACH instance to “scoped coordinate transport on the recorded strict handoff frontier; representative independence and coverage of all reachable histories are unestablished.” The original TTH-03 row cannot be promoted on FIACH-POS-01/02 alone.

## Additional C0 corrections

* **Endpoint convention:** corridor exit tick index 2 maps to AUT endpoint `SAFE-0` phase `2 mod 2 = 0`. The link also checks carrier 101 and event `t-exit`; it does not equate raw index 2 with phase 0.
* **TTN-03:** CM-03 routes `[0,2,1]` and `[1,0,2]` are both permutations of `{0,1,2}` and thus reversible. `a∘b=[2,0,1]`, `b∘a=[1,2,0]`; they disagree at every input. Constant record gives no strict endogenous record edge. CM-03 remains a separate negative control.
* **Package negative:** delete C1 `object_token` from the target local assignment. Flipping `c1_audit_sealed` only tests a recorded gate and is not the primary negative.

## Frozen-data disposition

| Property | Verdict on frozen data | Disposition |
|---|---|---|
| C6 future sufficiency | **fails; restricted-interface pass is near-automatic** | Draft phase code is exploratory, selected with frozen outcomes known; health refutes it |
| C6 order stability | substantive-pass at unfolded event-order ceiling | Compute from ranks/deltas; avoid finite-state absolute-order claim |
| C6 successor totality | substantive-pass operationally | Compute 8/8 response coverage, conditional on full K |
| C6 viable tick | substantive-pass operationally | Compute phase law and positive deltas |
| C6 endogenous arrow | substantive-pass for declared controller | Compute ownership, resources, positive records |
| C7 binding integrated | **undefined** | Finite strict-relation fact only; demote integrated binding |
| C7 relation preserved | substantive-pass at finite-relation ceiling | Prove four mapped-source biconditionals |
| C8 viable | **substantive-pass at declared operational ceiling** | Keep C8 kernel result; TTH-05 package preservation undefined pending per-state C1–C8 evidence |
| Route status | declared model status with computed path multiplicity | Theory-route identification and endpoint-persistent provenance absent; flatness undefined |
| TTH-03 bridge coverage | **undefined** | Demote FIACH instance; seek real histories and representative relation |

The largest scientific risk is that a near-automatic restricted C6 phase code and a substantive operational C8 kernel still do **not** give a state-indexed integrated C1–C8 package, proven endpoint route memory, or a nontrivial TTH-03 bridge. Consequently FIACH-POS-02 is a **partial evidence draft**, not a completed Temporal-FIACH witness.

## Reproduction

Read-only Python using `json`/`itertools` on the five frozen component model files can enumerate all `4×2` controller pairs, four C7 pair-membership comparisons, the two DAG paths, and CM-03 permutation compositions. The calculations above were made from those raw fields, not from `audit`/`derived_facts`/stored verdict fields. The planned Lean implementation must reproduce each finite equation with `decide`/`simp`; this design document alone is not kernel evidence.
