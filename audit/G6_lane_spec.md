# G6a — fixed lane definitions and separation controls

**Declaration only. No control, lane predicate, or prediction has been evaluated.**
This specification and [TTH06-LANES.model.json](proposed_models/TTH06-LANES.model.json)
are to be committed before G6b. They extend the committed POS-04 declaration;
they neither change nor retroactively validate any frozen model/result.

Authority: [G0 TTH-06 contract](G0_generic_contracts.md:68), including its warning that the old underfunding/withdrawal controls
also break package evidence. Prerequisites are the G2c assignment/gluing theorem,
G4 raw atomic composition, and assigned C8's generic greatest-viable-set theorem.

## 1. One raw interface and deterministic constructions

`RawLaneModel` consists of ONE immutable assignment in the existing typed `Cell`
namespace; the raw typed staging recipe and target cover; the finite corridor
and bridge selectors already declared by POS-04; and one **post-exit retention
rule**. No lane status, acceptance table, candidate future model, or independently
supplied mapped assignment is a field. The JSON imports the POS-04 declaration by
path, commit and hash, and specifies overlays rather than duplicating its tables.
All predicates below apply identically to the baseline and every control.
Owner CR1 selects **Version F** (full autonomy) as primary and **Version O**
(operational autonomy, narrowing N3) as supplementary. P and L are shared.
The two autonomy predicates are distinct fixed functions of this same raw model.

Let `a(m)` be the canonical POS-04 assignment after importing any raw JSON edits
and then applying the declared typed assignment edits. JSON views are not second
stores: changing `/base/new_data/corridor/events/...` changes the ONE `.eventTable`
cell seen by every clause and lane. All other shared cells remain identical.
Missing cells stay `none`; acceptance must check completeness before any internal
lookup default can be used.

Let `r = arrivalCover .target` and `s = canonicalStage`. In this family these are
fixed raw rules, not alternate per-control selectors. The cover's root is C1,
whose scope covers `primitiveCells`; its other scopes are `clauseScope .target`.
Adjacency is the computed parent relation. The stage's operation is the existing
`swapCell`/`translatedValue`, independent of clause index.

Define the computable target image

```lean
B m := exchangeAssignment (a m)
-- B m k = (a m (swapCell k)).map (translatedValue k)
```

Mapped locals are `mappedLocal (a m) s r c`, never supplied. On a covered cell,
the clause-independent stage makes this local equal `B m k`. Hence edge
compatibility is checked as equality of those actual values; it is not a flag.
The G6c adapter must prove that `B m` equals G2c's `assembledAssignment`, including
for missing cells. This removes the classical selector from G6b's executable
representation without replacing gluing by a different predicate. No acceptance
result may substitute for that equality bridge.

### Temporal phases (a disclosed extension)

The raw phase order is fixed:

1. arrival and completed corridor;
2. the declared single funded target step for the retained-route probe;
3. withdrawal;
4. post-withdrawal controlled responses.

The arrival assignment and its package dynamics remain immutable snapshots of
the funded regime. Withdrawal is an external intervention, **not** a letter in
C6's declared `Action` word alphabet. Thus the package C6 word law concerns its
assigned funded action dynamics; it does not promise survival of an external
resource-removal intervention. Bridge and route audits use arrival/pre-withdrawal
resources. Autonomy uses the same resource primitive AFTER applying retention.
This phase distinction is part of the new declaration, not inferred from POS-04.
It implements G0's requested post-exit-only control while holding route evidence
fixed. No source-presence or budget field of the arrival assignment is edited.

## 2. Package lane P: integrated arrival target realization

Fix `P(m)` as the conjunction:

- `MapTotal (a m) s r`;
- `ValuePreserving (a m) s r`;
- `EdgeCompatible (a m) s r`;
- every covered cell of `B m` is present;
- every local restriction of `B m` equals the defined mapped local;
- `AssignedPackagePass (B m) .target`, i.e. **each** assigned `C1Accept` through
  `C8Accept`, with its own completeness, raw-rule, and hard-gate checks.

The immutable cover is independently checked by `arrival_cover_check`; it is not
changed by any control. Restriction/value equalities and every clause's acceptance
must be evaluated, not inferred from the baseline. G2c supplies the generic
assembly proof from the computed local and map/gluing checks; its locality
lemmas transfer local acceptance to the actual global assignment.

`SourcePackagePass` and staged preservation remain additional `HandoffPass`
obligations in G6c; they are not a substitute for P. The package control deletes
a shared C1 input and therefore may also reject SOURCE C1/map totality. This is
an explicitly predicted intra-package effect. In Version F, failure of P also
forces failure of full autonomy; in Version O it is predicted to isolate P.

Grades remain C1–C3/C8 substantive T1/operational components and C4–C7 surrogates.
A missing required C1 table rejects package **acceptance/evidence**; it does not
show that the unchanged T1 dynamics have physically lost objecthood.

## 3. Lineage lane L: raw corridor and bridge

`L(m)` is the conjunction of the following computed checks, with no package
acceptance or post-withdrawal retention premise:

1. Adapt the same assigned event table, realized stages, histories, raw action
   rows/hazards, ticks, writers, resource owners and arrival ledger to G4's single
   atomic leg, for **each** raw route tuple. Use the fixed audited source/target
   vertices `mix_2-source`, `mix_2-target`, and later vertex `exit-target`.
   Run `AtomicLegPass` and single-leg `CorridorPass`: distinct carriers,
   source-only entry/target-only exit, realization/support, supported event
   execution, positive order/tick/progress/record updates, nonredundant support
   interventions and computed route-indexed discipline. Audit selectors are
   declared raw data and do not move to another mix after a mutation.
2. Check the assignment-indexed POS-04 bridge, preserving the G1c contract:
   nonempty supported history frontier and strict edge; coordinate-copy receiver;
   history coverage; representative independence **derived** from terminal maps;
   successor, order, tick, progress, record, route, maintenance and owner equations;
   full-interface defined future and closure-wide readout laws; weighted
   bisimulation; frozen signature snapshot-image codec/transport equations.
   Every row, successor, code, observer and closure is defined from the same
   assigned primitives, not from an untouched positive instance. The source and
   target action-row probabilities are the assigned rows, linked to T1/M where
   that gate requires it. Histories, future words and finite snapshot images have
   exactly the domains of the G1c POS-04 adapter; no bounded-word substitute.
3. Check the typed receiver/corridor exit link, including the declared target
   factor, event endpoint, ownership, and raw route tuple. Activation is computed
   from source presence, funding and a realized mix. The raw copy map computes
   both predictive classes. Route provenance is read after executing the funded
   target step in phase 2, from the resulting register, not from a route name.

This is the declared assignment-indexed extension of the G4 and G1c adapters,
not a disjunction of variant-name lookups. The G6c implementation must link these
adapters to the existing positive theorems. In particular it must not retain
`atomicPosAvailable`, `BridgePass .positive .positive`, or another positive-only
constant as the mutated evaluator. Mandatory primitive dependencies exclude
`.publishedC`; M/futures are computed from rows, hazards and position, with their
existing raw-reference checks. All required dependencies must be present.

For the lineage control, `mix_1` remains mixed. The prediction that package C7
still passes relies on its **same** `mixed7` existential realized-mix rule,
not a redefined rule demanding a particular control label. C6's `strictEvent6`
checks strict steps and realized path references; the changed support bit is not
a strictness flag. Losing the fixed `mix_2` source audit vertex is expected to
reject the atomic intervention audit, even if a different mixed event survives.

## 4. Shared withdrawal inputs, declared disturbances, and responses

Authority for Version F: [POST_WITHDRAWAL_AUTONOMY.md:5](../cst-tt/docs/POST_WITHDRAWAL_AUTONOMY.md:5),
“for every declared disturbance, a target-owned action reaches another surviving
state while preserving the integrated package, retained-resource closure,
positive tick progress, strict record advance, and budget solvency”; and
[ExactAutonomyCertificate](../lean/CSTTT/Autonomy/FiniteAutonomy.lean:20),
including `packageInside` and the universally quantified `response` field.

### New, minimal disturbance interface (fixed for F AND O)

POS-04 declares the control actions `stay`, `cw`, and `ccw`, but does NOT supply
an exogenous disturbance interface. It would be incorrect to call these three
actions disturbances. Declare a NEW finite type:

```lean
inductive LaneDisturbance where | nominal
-- enumeration = [nominal], fixed before evaluation
```

Rule: the minimal nonempty environment needed to request a maintenance response
without importing unprovided dynamics. `nominal` makes NO change to the assigned
action probabilities, hazard table, resource supply or ledger. It asks the
internal target controller to execute a supported response. This singleton
universal quantifier is intentional and has limited power: **no adversarial or
nontrivial disturbance robustness is claimed**. Enlarging its alphabet/effects
would require a new declaration, not a post-evaluation edit. The action domain
remains the separate existing three-element POS-04 `Action` type.

The named essential resource is **`target_recharge`**, copied from POS-04
`new_data.maintenance.target_resource`. Baseline retention includes that name
because its raw target recharge-availability primitive is true. No availability
primitive is read as an autonomy verdict.

Let `d = clause8 (B m) .target`. Construct the WITHDRAWN inputs:

```lean
dW m := { d with resource := { d.resource with rechargeAvailable :=
  d.resource.rechargeAvailable && decide ("target_recharge" ∈ retainedResources m) } }
```

The withdrawal view removes source, migration bridge/controller, external
decoder/scheduler and undeclared repair roles; its source presence is false.
Those six roles and their removal rule are explicit raw declaration fields.
No such role may be an input to a post-withdrawal response. Retained resources
must be declared and target-owned. The arrival receiver cell remains historical
activation data, not a post-withdrawal available source. Boundary K, disturbance
and action alphabets and response ownership are fixed before evaluation.
The controller/action owner is the target carrier, derived from the assigned
target resource owner by the same carrier-tag encoding; it is checked, never
assumed by a response proof. Tick and writer dependencies must be present
(`.ticks .target`, `.writers`, `.histories`, `.routeTable`) in addition to
C8 inputs; missing inputs reject BOTH autonomy versions.

### Exact response semantics and quantifier

For EVERY `x ∈ S`, EVERY declared raw route-register context and EVERY
`d ∈ [nominal]`, there must EXIST an action `a` owned
by the target such that:

1. its row is the actual assigned target `dW.rows x a` (nominal effect is identity),
   nonempty, with total numerator 4 at denominator 4;
2. **every** positive-probability successor is an in-K state in S; no exit or
   zero-weight counterfeit supports a response;
3. required maintenance resources are retained and target-owned; effective
   recharge is the declared unit recharge if available, otherwise zero;
4. the budget after paying cost and receiving effective recharge is positive
   and equals the prior budget; tick and record have their assigned positive
   unit advances with the corresponding writer available;
5. for Version F additionally, the computed package holds at the present state
   and every supported successor, as specified below.

Thus safety is probability-one across the raw stochastic row, stronger than
merely selecting one lucky positive-probability successor. The canonical policy
is a predicted witness where safe, not an assumed response. Evaluation must
search/check the same action alternatives for every state/disturbance and
report a failed pair if none works. The `ControlledSystem.step` projection for
the Lean certificate is positive row support, qualified by these ownership,
resource, ledger and update checks. Existence follows from a nonempty safe row;
all-support safety remains an extra checked theorem.

Autonomy entry states are defined from the RESULT of phase 2: for each raw
route, decode its receiver output, execute its actual funded target row, and
collect every positive-probability in-K successor and resulting register.
Require this entry set nonempty and every such endpoint inside the invariant.
Do not reset the factor/counters to the earlier corridor exit after the probe.
The corridor-to-receiver link remains at exit; the defined unit step links
that exit to withdrawal entry. The certificate exists for each entry state.

The finite state is the K factor, not a fictitious strictly increasing finite
clock. On execution lift it to `RunState = factor × unbounded counters × budget ×
retained register`, with the existing defined C6 tick/progress/record updates.
Positive increments are computed step recipes, and the run-level growth theorem
is proved over arbitrarily long words. Do not assert a strictly increasing
state-valued rank on recurrent K. Finite-factor fixed points below lift through
these checked run laws; no bounded-word enumeration replaces the universal
response or word claims.

## 4F. Version F — full autonomy, primary TTH-06

Define the withdrawn package assignment `BW m` from B by replacing ONLY the
target resource cell's recharge availability with its computed retained-resource
availability. All other cells, including historical receiver/event/route data,
are the same immutable package primitives. Per-state clause views are the
existing 160 coordinate views; they resolve to these SAME cells. The current
withdrawn source availability is separate raw phase data and cannot supply
responses. Package C7's surrogate acquisition/display check still evaluates its
recorded pre-exit history; it does not reacquire a source after withdrawal.
This is preservation of the declared graded package, NOT a full P05 C-package.

Let the actual per-state package predicate be

```lean
PackageAt m x := P m ∧ AssignedPackagePass (BW m) .target ∧
  StateViewsResolve (BW m) x ∧ RunReadoutLawsAt m x
```

`StateViewsResolve` checks the state-indexed views resolve exactly to their
primitive cells with all required inputs present. `RunReadoutLawsAt` uses the
defined C6 dynamics/closure-wide laws, unit writer/tick/progress/record updates,
and the actual withdrawn ledger; its run quantification is not a supplied flag.
P's map/gluing equations are part of integrated-package coherence. P and each
assigned clause are recomputed; do not substitute a cached arrival verdict.
Including P is disclosed: package preservation preserves the SAME coherent
integrated package that P describes, not just a safe factor or C8 predicate.

Define `pruneF m S` by filtering S to states satisfying `PackageAt` and the
response test above for **every** disturbance, with EVERY supported successor
also package-valid and in S. Compute `SF m` as the greatest fixed point inside K
(start at K and prune to equality, or enumerate all viable subsets and take
their union). The package/response predicates do not depend on a supplied safe
set or proof field. Exact fixed-point and monotonicity checks are required.

`AF(m)` contains the `ExactAutonomyCertificate`-shaped computed obligations:
all six withdrawal removals; boundary/disturbance class fixed; endpoint in SF;
**packageInside** for every state in SF; retained-resource closure/target ownership;
and target-owned responses to EVERY disturbance from EVERY state in SF, with
inside successors, anti-stall and solvent budgets. It also checks probability-one
row safety and the closure-wide run laws above. Endpoint and inside are defined
from the receiver and computed SF, not supplied. This is TTH-05-style preservation
at the declared package grades and singleton nominal environment.

### Predicted implication and proof architecture

Declare the target theorem (NOT proved/evaluated here):

```lean
theorem fullAutonomy_implies_package (m : RawLaneModel) : AF m → P m
```

The intended derivation is endpointInside + packageInside at that endpoint +
the P conjunct of `PackageAt`. Package failure is therefore predicted to force
AF failure; it is **not** an isolated package-breaking control for F.

For the primary generic TTH-06 proof, “none ... is inferred” is read
**proof-structurally**, per owner decision: build P directly by G2c, L directly
by G4/G1c, and AF directly by the package-preserving invariant/response checks;
retain these independently derived evidence objects. The readout does not use
AF to fill the P field, despite the disclosed logical implication. F makes no
claim that all three predicates are logically independent.

## 4O. Version O — operational autonomy, supplementary N3

Let `SO m := greatest8 (dW m) .target`, using the same C8 arbitrary-data operator.
`AO(m)` checks target C8 input completeness, explicit source/other-role removals,
resource closure/ownership, `available8`, `Ledger8`, `PUnchanged8`, nonempty SO
containing the computed endpoint, its viability/fixed-point equality, and the
shared EVERY-disturbance response semantics above **without PackageAt**.
For the nominal singleton the response quantifier specializes to the ordinary
existence of a safe funded target action per state, but that specialization must
be explicit in G6b/G6c. The same run-level budget/tick/record/writer laws apply.

No C1–C7 acceptance, P, or `packageInside` premise is included in AO. This is
**narrower operational C8 viability (N3)**, not TTH-05 full package preservation.
It is supplementary only. Predicted witnesses give logical independence of
P/L/AO on this family, whereas AF implies P. No result for O may be cited as
the primary full-autonomy TTH-06 theorem.

## 5. Exact interventions (apply individually to baseline)

| ID | Single declared intervention | P | L | AF (F) | AO (O) |
|---|---|---|---|---|---|
| `G6-PACKAGE-ONLY` | `put a .publishedC none` | fail | pass | fail (forced consequence) | pass |
| `G6-LINEAGE-ONLY` | `/base/new_data/corridor/events/1/source_support := false` (`mix_2`) | pass | fail | pass | pass |
| `G6-WITHDRAWAL-ONLY` | `/raw_interface/post_exit_retention/retained_resources := []` | pass | pass | fail | fail |

`/base/...` denotes a resolved imported POS-04 JSON document, not an edit to its
frozen file. Import its changed event list once into `.eventTable`. The typed
assignment deletion is applied with `put` and cannot delete only one of several
views. Controls do not accumulate. No label, class table, projection recipe,
observation alphabet, gate definition, or audit selector is changed.

The withdrawal control changes only the post-exit retention rule. It leaves the
arrival resource availability true, ledger 1/1/1, every action row, and both tags'
package/bridge/corridor/route data fixed. It is deliberately not the old
`underfund8` mutation of a package resource cell.

## 6. Evaluation and promotion discipline (separate F/O gates)

G6b evaluates P/L/AF/AO for baseline and every control using identical predicates
within each version, exact probabilities and finite fixed points. The disturbance
interface is the same fixed nominal singleton in both. Report per-disturbance
responses, packageInside at EVERY invariant state, actual safe sets, lifted run
laws, all lane outcomes and secondary effects. Existing positive theorems alone
are not outcomes of the new shared interface. No prediction is tuned after a
failure; repair requires a new declaration.

**F primary gate:** positive baseline; isolated lineage-only and autonomy-only
controls; the declared `AF → P` theorem; and the package-failure consequence
`¬P ∧ L ∧ ¬AF`. That consequence is expected dependence, not confounding or an
isolation count. If either supposed F isolation also fails P or its other lane,
it is confounded. Derive package, lineage and full autonomy separately before
assembling the generic certificate/readout. Full autonomy requires packageInside
and the total response proof, not just C8 greatestness.

**O supplementary gate:** positive baseline and all THREE isolated controls:
`¬P ∧ L ∧ AO`, `P ∧ ¬L ∧ AO`, `P ∧ L ∧ ¬AO`. Any second lane failure is confounded.
Report and label O's narrower N3 ceiling separately; it cannot clear the F gate.

Each G6c `HandoffPassF`/`HandoffPassO` also checks source package, staged
preservation, content sensitivity/source-absence, endpoint/route agreements and
recognition `notAddressed` from raw data. All certificate fields prove computed
predicates. No derived object is supplied. G6c must prove the same declarations
that G6b evaluates, including the B/gluing equivalence.

Only structural/reference checks are permitted in G6a. No status change is made.

### CR1 declaration change list

- Separate AF (primary) from AO (supplementary N3); P/L and all three raw mutations
  unchanged. Rename versioned predicted vectors, not the existing control IDs.
- New minimal exogenous disturbance `nominal`, identity effect on assigned
  probabilities/resources; actions remain a separate three-element control type.
- Declare EVERY-state/EVERY-disturbance response semantics, with probability-one
  stochastic support safety, target ownership and explicit unit run updates.
- New explicit six-role withdrawal rule and response owner recipe; retained
  resource policy and phase ordering unchanged.
- Define BW, per-state package predicate, package-filtered greatest invariant and
  packageInside for F; declare AF implies P and expected joint P/AF rejection.
- Entry states at withdrawal are derived from the phase-2 step results, rather
  than resetting to the earlier receiver factor; this clarifies the existing
  declared phase ordering. All resulting endpoints must be inside the invariant.
- No frozen POS-04 file, Lean declaration, registry status or outcome is changed.
