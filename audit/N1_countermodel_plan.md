# N1: real-predicate countermodel triage

The row texts below are the `exact_statement` values in
`cst-tt/registries/FINAL_THEOREM_STATUS.csv`. L3b verdicts are from
`audit/L3b_countermodel_open_fidelity.md`. **(a)** means a POS-04-family
instance proved in `lean/CSTTT/POS04/Countermodels.lean`; **(b)** means a
separate finite control is needed in N2; **(c)** means infeasible now because
neither POS-04 nor a specified separate control can realize the row's real
predicates. **No rows are assigned (c)**: the partial POS-04 witnesses are
classified (a) with their precise ceiling gaps stated below, while every
remaining row has a specified (b) control. No result here alters a registry
status. The frozen `Countermodels/Kernel.lean` declarations remain in place,
including their stipulated predicates.

The POS-04 predicates read the raw T1 action supports, stages, events,
resources, route tuples, and couplings. Relevant definitions are
`POS04/C4C5.lean:29–56`, `POS04/C7.lean:12–109`,
`POS04/C8.lean:13–64`, `POS04/Corridor.lean:10–87`,
`POS04/RouteMemory.lean:27–96`, and `POS04/Assembly.lean:224–243,290–326`.
The positive package is **substantive C1–C3 and C8, surrogate C4–C7**.
That ceiling applies to every POS-04 result below.

## TTN-01 — detached reconstruction

**Exact statement:** “There exists an exact finite detached reconstruction with endpoint equality, target package realization, and target autonomy but no strict overlap temporal corridor.”

**L3b:** STIPULATED. **Choice:** (b), **L**. Encode CM-02 or a new POS-04
control with *zero* mixed-support legs, a computed endpoint match, a proved
target `PackagePass`, and a proved `TargetAutonomy`; then refute the strict
corridor. POS-04 `.detached` has **one** realized mixed leg
(`neg_corridor_detached_one_mixed_leg`, `POS04/Corridor.lean:98–103`), and its
receiver still transfers source content. Calling it a detached reconstruction
would make the row false for the offered witness. N2 needs a genuine zero-mix
copy whose target package and autonomy survive independently.

## TTN-02 — public shadow

**Exact statement:** “There exist exact finite systems with identical public observations and different hidden consciousness-relevant structural predicates.”

**L3b:** STIPULATED. **Choice:** (a), **S**.
`ttn02_public_shadow` uses two *pointed* target T1 systems at `p1w0` and
`p1w1`, with the same canonical action table. `c4Current` gives equal public
channels, while raw action-support-derived `rawM` differs; `C4Collision` is
also proved. **Gap:** this is nonidentifiability of the finite predictive-M
structure on the declared public interface, not a full P05 consciousness
predicate. Retain the row only at that finite-interface ceiling, or revise
“consciousness-relevant” to “predictive-M” before promotion.

## TTN-03 — holonomy without arrow

**Exact statement:** “There exists an exact finite route system with nontrivial holonomy and no endogenous temporal arrow.”

**L3b:** STIPULATED. **Choice:** (b), **M**. Encode CM-03's two finite
permutations, prove each is reversible and that their composites do not
commute, then compute the record-arrow predicate from its constant record
update. POS-04 has retained route memory and a funded record writer; it is
not an arrow-free instance. N2 must connect the computed update to the
theory's `RecordArrow` predicate, not set the arrow verdict to `False`.

## TTN-04 — current collision and licensed repair

**Exact statement:** “When two histories are current-equal but predictively unequal, a current-only predictor cannot represent both; the licensed repairs are retained route memory or a proof of flatness.”

**L3b:** FAITHFUL at the route-discipline ceiling. **Choice:** (a), **S**.
`ttn04_current_collision_memory` proves equal computed target endpoints for
routes `.a/.b`, unequal future readouts *after* a funded target step, failure
of every current-only predictor, and `MemoryRepairs`. The repair follows the
existing `memoryOrFlatness` theorem using the separately proved
`pos04_route_code_future_sufficient`; it is not assumed. The two-route
domain is finite and nonempty. The future readout deliberately reads the
first source phase from the retained raw route tuple, as POS-04 disclosed;
its distinction has limited independent evidential weight.

## TTN-05 — clock translation loop

**Exact statement:** “There exists an exact finite clock-translation loop with nonzero holonomy, so no route-independent global present factors through the shared boundary alone.”

**L3b:** WEAKER. **Choice:** (b), **M**. Encode CM-07's mod-2 clock loop and
compose its translation around the loop; prove residue 1 and then use
`RouteTheory.noCanonicalGlobalNowOfTranslationHolonomy`. POS-04's unequal
route readouts are not a clock-translation loop and cannot certify nonzero
translation holonomy.

## TTN-06 — withdrawn essential resource

**Exact statement:** “There exists an exact finite target whose runtime behavior is maintained by an essential withdrawn resource and therefore fails post-withdrawal autonomy.”

**L3b:** WEAKER. **Choice:** (a), **S**.
`ttn06_withdrawn_essential_resource` proves the target `PackagePass` and
`TargetAutonomy` under funded target recharge, then proves the greatest
viable set is empty and autonomy false when that recharge is removed. The
predicate is the C8 raw ledger/action-support fixed point, not a stored
resource flag. **Gap:** the POS-04 negative is withdrawal of *target-owned
recharge*, not CM-04's external scheduler. This is a real autonomy-boundary
instance of the row, with a different finite mechanism. Source withdrawal
alone leaves POS-04 autonomous, as L6b proved.

## TTN-07 — stable phase without progress

**Exact statement:** “There exists an exact finite clock whose phase is stable while genuine temporal progress is absent.”

**L3b:** STIPULATED. **Choice:** (b), **M**. Encode CM-05's one-state
transition and compute phase constancy and failure of a nontrivial progress
law from that transition. POS-04's realized event paths have strict progress
and funded tick; it does not instantiate this boundary. The certificate's
stored `tick_viable` must not stand in for genuine progress.

## TTN-08 — local/global incompatibility

**Exact statement:** “There exists an exact finite family of locally accepted clause witnesses that admits no coherent global package witness.”

**L3b:** STIPULATED. **Choice:** (b), **M**. Encode CM-08's two assignments
of `0` and `1` to a shared coordinate as actual `ClauseWitness` data;
establish local acceptance from clause rules and refute any global witness
whose restrictions equal both. POS-04's 160 coordinates form a compatible
package, so it is no countermodel. Acceptance must be computed, not stored.

## TTN-09 — gap and resumed stream

**Exact statement:** “There exists an exact finite episode with equivalent endpoints and a realized-time gap; it is a resumed stream rather than a strict no-gap corridor.”

**L3b:** STIPULATED. **Choice:** (a), **S**. `ttn09_gap_resume` uses the
declared POS-04 `.gap` intervention. Source-live and target-exit stages
remain realized, `mix1` does not, and the raw strict event order and T1
endpoint class agreement remain. `corridorNoGap` computes `false`, yielding
`¬ CorridorPass`. **Gap:** the endpoint comparison is the raw route/receiver
factor class, not an active receiver output across the broken corridor;
`receiverOutput .positive .gap` is unavailable. The theorem supports the
strict no-gap boundary, not active transfer through a gap.

## TTN-10 — scalar defect and hard gate

**Exact statement:** “There exists an exact finite defect profile with a small scalar mean and a failed nonnegotiable hard gate; scalar aggregation does not determine acceptance.”

**L3b:** STIPULATED. **Choice:** (b), **M**. Encode CM-10's nine zero defects
and one unit hard defect in `Robustness/DefectVector`'s actual component
types, compute mean `1/10`, and prove hard-gate rejection. Include the
equal-scalar accepted/rejected comparator for the final nonidentifiability
reading. N2 now proves that comparator; POS-04 has no such defect vector.

## TTN-11 — symmetric fork

**Exact statement:** “There exists an exact symmetric two-target fork for which swap symmetry preserves validity and no invariant unique continuer can be selected.”

**L3b:** STIPULATED. **Choice:** (b), **L**. Encode a finite two-target fork
with validity computed from each target's actual package/corridor data and
show swap preservation and fixed-point-free nonselection. POS-04 has two
routes but **one shared target endpoint** (`compared_routes_share_target_endpoint`,
`POS04/Assembly.lean:317–320`); it cannot be called a two-target fission.
The generic `TemporalFissionCertificate` stores a `valid` predicate;
N2 supplies it from a branch-owned relabeling of POS-04 package, autonomy,
and transition data before applying the symmetry result.

## TTN-12 — finite prefix versus unbounded liveness

**Exact statement:** “For every tested finite horizon there is an exact countdown system that succeeds through that horizon and fails immediately afterward; finite success alone does not imply unbounded liveness.”

**L3b:** WEAKER. **Choice:** (b), **M**. Define a countdown transition and
resource policy indexed by arbitrary `h : Nat`, prove each of the first
`h` required steps is live, and compute failure at the next step. Existing
`UnboundedInvariant.CountdownLive` already proves the Boolean boundary but
has no transition system. POS-04 funded C8 is a maintained closed kernel,
so it does not supply this finite-prefix failure.

## TTN-13 — same-carrier re-encoding

**Exact statement:** “A nonidentity re-encoding on one fixed carrier does not satisfy the distinct-carrier condition required for cross-carrier transport.”

**L3b:** STIPULATED. **Choice:** (a), **S**.
`sameCarrierReencode` swaps the two T1 `p0` phase states and fixes the
others; `same_carrier_reencode_involution` proves it is invertible and
`same_carrier_reencode_nonidentity` proves it is nonidentity. The theorem
`ttn13_same_carrier_boundary` applies the *actual* `distinct` field of
`TemporalFIACHCertificate` to refute any certificate whose source and target
IDs are both `tagCarrierId .target`. **Gap:** the phase permutation is not
claimed to preserve every T1 transition; the row only asks for nonidentity
re-encoding on the same carrier and a distinct-carrier typing boundary.

## TTN-14 — marginals versus recombination

**Exact statement:** “There exist exact finite joint structures with identical branchwise marginals and different recombination structure; branchwise preservation does not imply integrated binding.”

**L3b:** WEAKER. **Choice:** (a), **S**.
`ttn14_marginals_do_not_fix_recombination` uses the declared C7 transport
intervention: complete ordered branch records stay equal, while the exact
joint coupling distribution changes. The modified target remains locally
consistent; its `C7Strict` and the staged `C7Transport` equation fail.
**Gap:** this refutes the declared finite C7 surrogate, not full P05 C7
integrated binding. The stronger package interpretation still needs a
substantive P05 C7 realization or honest text reduction. This refines, and
does not erase, the already sound CM-15 finite relation lemma noted in L3b.

## N2 queue and status discipline

N2's separate-model rows are **TTN-01, 03, 05, 07, 08, 10, 11, 12**.
They are now implemented in `lean/CSTTT/Countermodels/RealControls.lean`;
the `(b)` classification records their need for separate controls, not an
unfinished proof.
The six POS-04 proofs are additional evidence; they do not silently replace
the registry's present `formal_declarations` or cure the nine stipulated
`Kernel.lean` witnesses. Before any status promotion, revise the registry
to point at each real theorem and narrow TTN-02, 09, and 14 wording where
their noted gaps exceed the current text. TTN-01's tempting POS-04
`.detached` witness is explicitly rejected as a proof of its exact row.

## N2 implementation and statement mapping

Each theorem below has an explicit existential witness (TTN-12 has one for
**each** `h : Nat`). The companion computed theorem exposes its decisive
finite facts. All eight rows have a **structural finite** ceiling; none is a
claim about physical consciousness, numerical identity, or unbounded
survival. The new controls do not read any `premise_checks`,
`conclusion_failure_checks`, or other stored verdict field from CM JSON.

| Row | Existential theorem and computed statement | Mapping, ceiling, gap |
|---|---|---|
| TTN-01 | `ttn01_exists`: a typed source-to-target endpoint copy, target `PackagePass` and `TargetAutonomy`, and `¬ HasMixedSupport`; `ttn01_no_atomic_corridor` refutes every atomic certificate over those stages. | CM-02's two source-only/target-only stages. This is an endpoint, package, and autonomy counterexample to a strict overlap corridor. The copied target has the POS-04 C4–C7 surrogate package ceiling. |
| TTN-03 | `ttn03_exists`: two reversible three-state route maps that do not commute, with no strict record edge or endogenous update and failure of `RecordTheory.StrictlyMonotoneOn`. | CM-03's exact permutations and constant record update. `routeSpec` populates the actual `TemporalClosureSpec.endogenousRecordUpdate` field from the route successor and strict record order; the arrow verdict is computed. **Gap:** this is an arrow boundary, not a positive full C6 closure witness. |
| TTN-05 | `ttn05_exists`: a mod-2 one-node loop with nonzero translated phase and `¬ RouteTheory.CanonicalGlobalNow`. | CM-07's loop translation of one, evaluated against the shared boundary. This is a clock-translation obstruction, not a full multi-carrier temporal signature. |
| TTN-07 | `ttn07_exists`: a singleton `TemporalClosureSpec` with viable stable tick and successor, but no successor satisfying its genuine-progress relation. | CM-05's self-step and single phase. The progress law requires a distinct next state, so stasis fails it. The frozen `tick_viable` flag is unused. |
| TTN-08 | `ttn08_exists`: two accepted `ClauseWitness` assignments on one coordinate, but no `IntegratedPackageWitness` with both restrictions. | CM-08's conflicting values 0 and 1. Acceptance checks equality with each locally declared value; `conflict_opposite_rejected` shows that rule can fail. **Gap:** these are two instances of one clause type, not an eight-clause C-package. |
| TTN-10 | `ttn10_exists` proves the rejected profile; `ttn10_equal_scalar_exists` gives an accepted and rejected `DefectTheory.DefectVector` with equal length, defect sum, gate schema, and scalar test, but opposite `VectorAccepts` results. | CM-10's nine zeros and one hard unit defect are the rejected vector. Moving that one unit to a soft coordinate with a declared one-unit allowance gives the accepted comparator. Both have sum 1 and mean 1/10. The scalar-nondetermination clause is now proved, without a stored verdict. |
| TTN-11 | `ttn11_exists`: two distinct branch carrier IDs, a real `TemporalFissionCertificate`, swap preservation of validity, and no valid related target fixed by branch swap. | CM-11's two-target involution. `forkRelabel` transports the POS-04 target ID, C5/C6/route ownership, and resource owner to each branch. `ForkPackagePass` checks C1–C7, branch-owned C8 availability and greatest viability, and canonical rows; `ForkAutonomyPass` reruns the post-withdrawal rule on each branch. `forkRelated` requires the computed receiver output and a declared endpoint-copy edge. **Gap:** the same positive corridor precedes branching; two independent branch corridors are not certified. |
| TTN-12 | `ttn12_exists_for_every_horizon`: for each `h`, a transition on finite `Fin (h+2)` states with a live prefix through `h` and failure at `h+1`. | Generalizes CM-13's 2→1→0 budget trace. The next-state and positive-budget laws compute the verdict; there is no unbounded policy. |

### Raw-data extensions and decision rules

The CM files omit some inputs needed by the theory predicates. The following
rules were declared in the Lean module **before** their verdict theorems:

- **TTN-01:** copy a source endpoint's raw T1 coordinate into a separately
  tagged target; enumerate source-only then target-only stages. The copied
  coordinate is not a temporal stage or a mixed-support event. Target package
  and autonomy are recomputed from POS-04's funded target model.
- **TTN-03:** use CM-03's constant record update as the raw record function;
  an endogenous arrow needs a strict record edge on a route step. The
  published permutations are checked as involutions and noncommuting maps;
  `routeSpec.endogenousRecordUpdate` uses exactly that edge rule.
- **TTN-05:** translate phase by the declared loop increment modulo the
  declared modulus 2. Identity and loop paths start at the same boundary;
  their local now is the translated phase from zero.
- **TTN-07:** a one-state successor is its self-step. Tick viability checks
  the defined step and stable phase. Genuine progress requires a successor
  distinct from the current state, making stasis an explicit negative.
- **TTN-08:** a local clause accepts precisely when its one-coordinate
  assignment equals that clause's declared value; the hard gate checks the
  same equality. The global witness must restrict to both local values.
- **TTN-10:** CM-10 identifies the sole failed gate as index nine, so that
  component is hard with defect one. The first soft coordinate has a
  one-unit allowance as a **declared comparator design choice** that makes
  acceptance possible; it is not a consequence of CM-10's frozen data.
  This choice is legitimate for the existential counterexample. The other
  eight soft coordinates have zero tolerance. The rejected vector places
  the unit at the hard gate; the accepted vector moves it to the allowed
  soft coordinate. Gate types and tolerances remain identical. The scalar
  rule is the frozen `10 × sum ≤ count` test.
- **TTN-11:** copy one source endpoint into each of two distinct branch
  identities. `forkRelabel` fixes the source ID and sends the base target
  ID and its owned resource to the branch ID. The same map interprets the
  target-owned C5 protocol, C6 owner, and route readout on that branch;
  `fork_clause_owners_transport` checks each equation. Each branch's action table is
  proved equal to the POS-04 target table; `fork_available_transport`,
  `fork_greatest_transport`, and `fork_receiver_greatest_transport` prove
  preservation of C8 and withdrawal viability under this relabeling.
  `ForkPackagePass` checks all declared clause grades with branch ownership,
  and `ForkAutonomyPass` requires source absence and a nonempty branch-owned
  viable set. Relatedness requires the POS-04 receiver's computed endpoint
  and membership in the two raw copy edges. Validity also checks bridge,
  corridor, and carrier separation; the Boolean branch swap is CM-11's
  published involution.
- **TTN-12:** for horizon `h`, use finite states `Fin (h+2)`, initial budget
  `h+1`, transition `b ↦ b−1` with zero fixed, and `Live b ↔ b>0`.

**Status limit:** these N2 theorems are new evidence; the registry still
points at the older stipulated witnesses. TTN-03, 08, and 11 have the
specific ceiling gaps in the table above. Promotion requires the manager's
statement-fidelity review and a registry update; no frozen file was changed
in N2.
