# G4 — strict composition of computed atomic legs

## Claim and classification

TTH-04 (09, unchanged text): “Audited atomic overlap legs compose into a strict
carrier-chain temporal corridor when consecutive legs agree exactly on the
intermediate carrier, temporal frontier, route residue, and ownership interface.”
Ceiling: **structural lineage criterion only**. No package, autonomy, recognition,
physical realization, or numerical-identity conclusion follows.

All additions are **(b) mathematical**, TTH-04: replace the old summary interface
as row evidence with a finite atomic execution audit and induction over actual
legs. Existing declarations remain unchanged. No narrowing of the row is applied.
The corrected packet replaces the impossible POS-04 two-leg instance with the
frozen COR-POS-02A/B pair. POS-04 is the single-leg/base-case instance.

Sources: [atomic semantics](../cst-tt/docs/TEMPORAL_CORRIDOR_SEMANTICS.md:5),
[composition semantics](../cst-tt/docs/CORRIDOR_COMPOSITION_THEOREM.md:5),
[G0 contract](G0_generic_contracts.md:51). The semantic atomic requirements include
source-only entry, target-only exit, distinct carriers, mixed support, no gap,
strict order/tick/progress/record, forward event dependencies, nonredundant
interventions, maintained ownership, and exact joins.

## Raw data, computed gates, and constructions

[AtomicChain.lean](../lean/CSTTT/Corridor/AtomicChain.lean) defines:

- `Frontier`: predictive coordinate, order, tick, progress, record, residue,
  maintenance, and owner. Tick is the exact absolute index in COR's JSON; no
  modulo or truncation is introduced.
- `RawStage`: support list, realization, and the complete frontier.
- `RawEvent` / `RawDependency`: actual named, owned stage events and edges.
- `ReadoutUpdate`: numerical increments, appended tokens, next maintenance and
  owner. These are raw recipes, not propositions or stored verdicts.
- `FiniteAtomicLeg`: carriers, stages, events, dependencies, recipes, additive
  intervention inputs and audit references, and the intervention-rule enumerand.
- `AtomicLegCheck` / `AtomicLegPass`: check distinct carriers and exact singleton
  endpoint support/ownership; all stages realized, supported, maintained and
  owned by active carriers; mixed support; event references and owners;
  unique local event IDs; forward dependencies; every successive readout recipe; intervention effects;
  computed route discipline.
- `AdjacentFrontierCheck`: intermediate carrier equality and exact equality of
  the shared stage, including every frontier field, support and realization.
  Residue and owner are additionally stated as explicit equations.
- `chainCheck`: checks every atomic leg and every neighboring interface.
  `CorridorPass` additionally requires a nonempty chain and distinct outer carriers.
- `chainStages`: concatenates while removing the duplicate first boundary stage
  of each subsequent leg. `chainEvents` shifts local event ordinals into that
  trace and removes identical shared events. `chainDependencies` merges edges. The generic graph uses `constructedEvents`
  and `constructedDependencies` with leg-scoped IDs; unrelated equal local names
  cannot collide. The unscoped view is used only to compare this named frozen instance.
  `chainReadoutEdges` is the concatenation of all advancing local pairs/recipes.
  Joins contain one identical boundary stage, not a spurious zero-length step.

### Route rule and its precise limit

`pathsAt` enumerates supported event paths, using one event at each successive
stage and the actual dependency edges. `routeExecutions` is the computed
entry-to-exit comparison domain. `routeStatusOf` rejects an empty domain,
invalid dependencies, empty recipes or root residue, and failed execution of
append recipes against the actual exit residue. Otherwise its value is
`routeIndexed`.

This is a **conservative route-indexed discipline**, not a nonflatness theorem.
The raw COR dependency paths are a declared finite execution comparison domain;
it does not assert that its two input-dependency paths retain distinguishable
future outputs. No `.flat` constructor is available here, and residue growth is
never used to infer nonzero holonomy. Flatness/normalization/confluence licenses
are separately defined and proved in G3c. The TTH-04 claim requires exact retained
route-residue interfaces, not a new memory-versus-flatness separation.
Stored JSON `route_status`, `ownership_interface_valid`, and
`representative_independent` flags supply **no proof**.

### Main signatures

```lean
theorem strictTemporalCorridorComposition_generic
    (legs : List FiniteAtomicLeg) (h : CorridorPass legs) :
    StrictCorridorWitness legs

theorem append_corridor (left right : List FiniteAtomicLeg)
    (hl : CorridorPass left) (hr : CorridorPass right)
    (hj : boundaryCheck left right = true)
    (hd : ((left ++ right).head?.map (·.source)) ≠
      ((left ++ right).getLast?.map (·.target))) :
    StrictCorridorWitness (left ++ right)
```

`chain_derivation` inducts over the list, constructing a single-leg derivation or
prepending a checked leg and exact interface to the recursively constructed tail.
`derivation_append` proves binary composition by induction over that derivation.
The witness has only proofs of `CorridorPass`, the constructed inductive derivation,
all readout checks, realization of every stage in the computed concatenation,
and strict order/tick/progress/record for every computed advancing edge.
No derived trace, verdict, route status, or witness is a supplied argument.
`chain_readout_steps` proves every advancing pair/recipe in the whole chain passes;
`readout_step_strict` derives the four strict inequalities from independently
checked positive increments and their numerical equations.

## Genuine two-leg instance and transcription

[AtomicModels.lean](../lean/CSTTT/Corridor/AtomicModels.lean) transcribes operative
JSON tables with provenance comments at each table:

- `COR-POS-02A`: 17 → 55, three stages, four events, four dependencies.
- `COR-POS-02B`: 55 → 101, three stages, four events, four dependencies.
- `COR-POS-02-COMPOSED`: 17 → 55 → 101, five stages, seven events, eight dependencies.

All eight signature fields, active support, realization, carrier codes, event
IDs/owners/ordinals, dependency references, additive base and contributions, and
intervention audit IDs are transcribed. Full and removal projections are computed,
then compared with the frozen recorded projections.

**Disclosed derivation of missing recipes:** for consecutive recorded signatures,
use successive differences for the five numerical coordinates, the suffix after
the prior residue for append tokens, and the recorded next maintenance/owner.
The audit separately requires positive order/tick/progress/record differences,
exact append equations, supported ownership, and forward supported execution.
Thus the positive increments and retention can fail; the equality to the recorded
recipe is a finite table-consistency check. This does **not** infer unbounded
future behavior or an independent causal model from a snapshot difference.
The recipes are fixed definitions for these instances; guards change snapshots
or recipes independently. No constants were tuned to make an audit pass.

`left_pass`, `right_pass`, `exact_frontier`, `two_leg_pass`, `two_leg_corridor`,
and `two_leg_append` establish the generic hypotheses and the constructed witness.
`composed_stages_exact`, `composed_events_exact` (order-insensitive graph equality),
and `composed_dependencies_exact` link the constructed concatenation to COMPOSED.
`route_comparison_domains_nonempty` computes two supported event paths per leg;
`route_status_computed` proves both conservative statuses from execution.

[check_corridor_transcription.py](../scripts/check_corridor_transcription.py)
probes evaluated Lean values via a temporary file under `/tmp`. Coverage:
all operative tables above, derived recipes, full/removal projections, audit
references, carrier chains, and the constructed COMPOSED trace/graph. Constant
event/dependency kind vocabulary, takeover/mixed/audit ordinals, and COMPOSED leg
descriptor shifts are also checked. It excludes descriptive metadata and stored
transport/status verdicts. In-memory snapshot, event, and intervention drift
self-checks must each be caught. No frozen files are written.

## POS-04 single-leg adapter

[AtomicCorridor.lean](../lean/CSTTT/POS04/AtomicCorridor.lean) gives
`pos04_atomic_leg_pass` and `pos04_single_leg_corridor`, for either declared route.
It has four stages and one source-to-target carrier change.

Adapter rules: carrier codes are existing tag indices; counters are the declared
realized-path ordinals; the predictive coordinate is the unchanged terminal M
class; mixed support is the declared support of the two mixed events; a jointly
supported event is expanded to owned source/target vertices, and consecutive
stage vertices are connected. The route residue encodes the actual source-history
states and executed event prefix; `pos04_exit_residue_exact` links the exit to the
L7 raw route register. `pos04_atomic_M_link` identifies the class partition with
raw action-support/hazard M. Snapshot availability gates funded ticks, writers,
strict realized paths, both funded kernels and the existing route-future outputs.
`pos04_adapter_existing_audit` also supplies the L7 corridor, both C6 traces and
actual retained-route-memory theorem. No new T1 table is introduced.

POS-04 interventions execute its declared Boolean support-removal conjunction,
not COR's additive projection. Additive-only input slots are inert in that mode.
This synthetic intervention semantics is not independent causal corroboration.

## Controls

[AtomicGuards.lean](../lean/CSTTT/Corridor/AtomicGuards.lean):

- `detached_has_no_mixed_stage`, `detached_fails`, `detached_no_witness`: remove
  target support at the mixed stage, leaving no mixed stage.
- `gap_fails`, `gap_no_witness`: mark the mixed stage unrealized.
- `mismatched_leg_still_passes`: translate every right-leg progress rank by one;
  its own update laws still hold.
- `frontier_mismatch_fails`, `frontier_mismatch_no_witness`: the otherwise valid
  right leg no longer matches the left exit. This isolates the interface gate.
- Parameterized raw-field, detail-field, update-recipe and interface-field guards
  cover the families below. These are sensitivity probes, not claims that every
  mutation isolates exactly one downstream failing conjunct.

## Argument classification

| Argument | Classification | Constraint |
|---|---|---|
| `legs` / `left`, `right` | Raw finite data | `AtomicLegCheck` and adjacent checks, via `CorridorPass` |
| `h`, `hl`, `hr` | Evidence on raw data | Proof of computed nonempty/check/distinct predicates |
| `hj` | Evidence on raw data | Computed exact last-to-first boundary equality |
| `hd` | Evidence on raw data | Distinct outer carrier IDs, as accepted G0 requires |
| Merged stages/events/dependencies, route paths/status, intervention outputs | Defined objects | Not theorem arguments |
| Atomic derivation and `StrictCorridorWitness` | Defined/constructed proof objects | Constructed by induction |

## Field coverage and guards

Every guard is kernel-proved. `every_raw_field_guard`, `every_raw_detail_guard`,
`every_update_recipe_guard`, and `every_interface_field_guard` are universally
quantified over the respective finite selector type; they provide a theorem for
each table row, not a sampled runtime test.

| Raw family | Check/law | Guard theorem/selector |
|---|---|---|
| Source, target IDs | Distinct; singleton endpoint support/owner | `every_raw_field_guard .source/.target` |
| Stage list and order | Length ≥3; endpoint checks; zip length and ordered recipes | `every_raw_detail_guard .stageList/.stageOrder` |
| Stage support | Nonempty; owner active; mixed support | `every_raw_field_guard .support`; `detached_fails` |
| Realization | Every stage true; computed concatenation realization | `every_raw_field_guard .realization`; `gap_fails` |
| Event IDs, owners, stage ordinals | Unique local IDs; resolve; supported owner; stage bounds | `every_raw_detail_guard .eventId/.eventOwner/.eventStage` |
| Dependency parent/child | Resolve; strictly forward; complete executed paths | `every_raw_detail_guard .dependencyParent/.dependencyChild`; `.dependencies` raw-family guard |
| Audit source/target/later IDs | Resolve, correct mixed ownership, later exit dependencies | `every_raw_field_guard .sourceAudit/.targetAudit/.laterAudit` |
| Base and both contributions, each numeric field | Actual entry/exit projection equations; computed removal differences | Nine projection selectors in `every_raw_detail_guard` |
| Intervention rule | Execute declared additive or support-deletion rule | `mixed_support_removal_guard`; POS-04 wrong-mode guard |
| Recipe list | Exactly one per advancing pair | `every_raw_field_guard .updates` |
| Shared carrier and full frontier | Exact stage and carrier identity | All selectors of `every_interface_field_guard`; valid-leg mismatch control |

### Readout coverage throughout the chain

| Readout | Checked update/preservation law | Readout guard | Recipe guard |
|---|---|---|---|
| Predictive | Next = prior + declared predictive advance | `.predictive` | `.predictive` |
| Order | Next = prior + strictly positive advance | `.order` (cap) | `.order` |
| Tick | Next = prior + strictly positive advance | `.tick` | `.tick` |
| Progress | Next = prior + strictly positive advance | `.progress` (cap) | `.progress` |
| Record | Next = prior + strictly positive advance | `.record` | `.record` |
| Residue | Next = prior ++ nonempty declared suffix | `.residue` | `.residue` |
| Maintenance | Next = declared nonempty maintenance state | `.maintenance` | `.maintenance` |
| Owner | Next = declared owner; owner belongs to next support | `.owner` | `.owner` |

Readout guards are `every_readout_update_guard` (with the relevant selector
equality); recipe guards are `every_update_recipe_guard`. All pairs in every leg
are checked, by `chain_readout_steps`; exact boundary equality handles joins.
No unbounded closure is asserted for this finite-corridor theorem.

## Verification and status

Reproduce:

```bash
cd lean && lake build
cd ..
python3 -B scripts/check_corridor_transcription.py
python3 -B scripts/validate_lean.py --write-inventory
scripts/validate_lean.sh
```

TTH-04 is promoted only after these gates and the axiom probes pass. The other
38 rows and all CST-TT-08 files remain unchanged. The old summary declarations
are retained for compatibility, but are no longer the evidence carrying this row.

### Receipt

- `lake build`: exit 0, **332 jobs**. New module build times in the final module
  pass: AtomicChain 3.8s, AtomicModels 6.3s, AtomicGuards 6.2s, AtomicExport 2.0s,
  POS04.AtomicCorridor 6.4s. No new-module warnings; inherited warnings replay.
- Transcription check: exit 0; all three in-memory drift controls caught.
- Direct probes: **44/44** new theorems resolve; axiom sets are `[propext]`,
  `[propext, Quot.sound]`, or the standard three.
- Validator: exit 0, `OVERALL pass`; TTH-04 has 12 theorem-kind evidence
  declarations, with probe and axiom gates passing. Receipt:
  `lean/.validate-logs/run-20260930T192146-039921Z/report.json`.
- Frozen tracked science files (excluding the authorized 09 CSV): byte-identical
  against HEAD; only the TTH-04 row of that CSV changes. `git diff --check` passes.
- 09 counts: **7 proved, 14 checked finite countermodels, 10 conditional, 8 open**.

Self-review: source-only/target-only endpoints, positive increments, supported
execution, both computed interventions, and exact interfaces all gate the result.
The valid-right-leg mismatch isolates the join failure. Local event IDs are unique;
leg-scoped IDs prevent generic name collisions. No route flatness, unbounded COR
future law, or independent causal corroboration is inferred. These are limits of
this structural result, not additional lane conclusions.
