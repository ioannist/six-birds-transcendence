# G6d POS-04 finite lift and multi-resource positive games

## Proved boundary

This seam instantiates the committed `RawFiniteAutonomy` transport. It adds no
registry promotion. TTH-06 remains **conditional**: exact arbitrary-partial
multi-resource game adapters and the complete polymorphic lineage/RawHandoff
assembly remain outstanding.

The new modules are:

- `POS04ResourceRuntime`: seven distinct resources (the six withdrawn roles and
  target recharge), one source/acquisition–receiver–target execution, assigned
  ledger/ownership instructions, and the raw withdrawal protocol.
- `POS04RawFiniteAutonomy`: primitive, required-resource, retained-account owner,
  and action-owner lifting equations, quantified over unbounded run contexts;
  a concrete nonempty `positive_lift` instance.
- `POS04MultiResourceGames`: a constructed positive invariant and causal nominal
  response policy, both named game readouts, and TTH-05 transport at every entry.

The authority is the frozen `G6_lane_spec.md:146` (sections 4–6) and
`TTH06-LANES.model.json.raw_interface`: its disturbance interface, response
semantics, budget rule, six-role withdrawal and actual phase-2 entry rule. Resource
codes reuse the existing removed-role and recharge serialization, with injectivity
and equality theorems. No additional price, threshold or model version is declared.

### Exact lift

`finite_cells_eq`, `primitive_lift`, `resource_lift` and `account_owner_lift`
compare interpreted values, including `none`, on **every** relevant run context.
The finite state assignment equals the run assignment exactly. For POS-04 these
views share their raw primitives across states; run counters, funded state and
route tuples remain in the actual updater and game.

`lift` needs explicit checked raw target ownership. `lift_of_game` derives it
from resource safety at a genuine game entry; `positive_lift` separately proves
it on the canonical data, without assuming an unconstructed game. External
ambient outcomes have a total helper projection, but do not enter the positive
invariant: `policy_supported` proves all actual canonical-policy branches are
in `K` before projection. No class representative substitutes for a branch.

### Constructed games and TTH-05

`positive_certificate` constructs the target invariant
`(actual K state, route tuple, arbitrary counter, arbitrary tick, funded)`.
It uses the assigned canonical action and proves normalization, legality,
full-support preservation, solvency and positive advancement. The generic
strategy induction yields `positive_full`; deleting only the package obligation
from its strategy yields `positive_operational`.

`positive_each_entry_exact` constructs an `ExactAutonomyCertificate` for **every**
activated realized phase-2 entry. `positive_each_entry_words` then gives the
TTH-05 controlled-run/package conclusion for every finite nominal word. The
finite transition relation is the committed exact image of actual legal support,
not an independently supplied factor transition table.

The positive resource accounts explicitly remove all six acquisition roles.
Source-mode charges use no maintenance resource and cannot satisfy the required
recharge inclusion (`source_mode_not_legal`). Source history execution still
uses the source rows during acquisition. It is never imported as post-withdrawal
response support.

## Argument classification

| Argument/object | Classification | Binding |
|---|---|---|
| `RawLaneModel.assignment` | raw partial assignment | staged/glued by `POS04DispatchedStage` |
| `retained`, `removed`, post-withdrawal source presence | raw withdrawal metadata | `Protocol`; no verdict fields |
| finite kernel/action/nominal alphabets | declared raw domains | existing POS-04 enums; `canonical_checked` |
| ledger, resources, rows, hazards, ticks, writers, histories, routes, receiver/events | assigned raw primitives | shared instruction evaluator; missing reads propagate |
| runtime/finite cells, accounts, charges, updater and entries | defined objects | raw instruction expressions and shared execution |
| factor projection and factor system | defined objects | actual factor read; exact legal-support image relation |
| `Checked`, `Lift`, owner equation | evidence on raw data | all equations proved, positive instance supplied |
| invariant and strategy | auxiliary proof-bearing witnesses | checked against actual semantics, per adopted hybrid architecture |
| game readout and TTH-05 certificate | derived proof objects | generic strategy induction and transport |

## Resource/readout coverage

| Field | Checked law / proof | Guard |
|---|---|---|
| primitive cell views | `primitive_lift`, `run_assignment_eq` | generic `RawFiniteAutonomy.missing_factor_cell_guard` / `changed_factor_cell_guard` |
| factor and actual branches | `row_exact`, `policy_supported`, `policy_update` | shared missing row/update guards; no representative selection |
| required recharge | `resource_lift`, `required_eq` | `no_recharge_no_games` |
| account and action owners | `account_owner_lift`, `action_owner_read`, `lift` | generic wrong-resource/action-owner guards |
| seven identities / six-role removal | `resourceCode_injective`, `canonical_withdrawal` | generic aliasing/withdrawal checks |
| source availability | resource check requires false | `source_present_no_games` |
| acquisition mode | charge requires target mode for required resource | `source_mode_not_legal` |
| balance/debit/effective credit | `legal`, `policy_step`; conserved positive canonical unit ledger | generic depleted-resource guard; withdrawal control |
| order, ticks, progress, record | `policy_step`, generic `step_advances` on every strategy play | `capped_field_rejected` for each of four fields |
| writer availability | `resource_inside` for both retained route tuples | generic `writer_unavailable_rejected` |
| residue | `policy_update` and `policy_step` preserve raw tuple | generic `changed_residue_rejected` |
| acquisition dependencies | shared `AcquisitionExecution.Ready` and raw phase-2 entries | `missing_acquisition_no_games` for every consumed cell |
| resource dependencies | shared `ResourceRuntime.Ready` | `missing_resource_no_games` for every consumed cell |
| package at every run | `package_inside`, closed eight-schema dispatcher | `package_deletion_no_full` |

The four capped-field proposals alter just one resource-game readout and reject
its actual step at a genuine invariant state. They are sensitivity guards, not
an exhaustive isolation claim. The other guards explicitly reject a named check
or semantic readout; no guard assumes readiness together with a missing
required input.

## Direct negatives

- `withdrawal_control`: both named games fail when the required retained recharge
  is removed, derived directly from impossible resource safety at an entry.
- `source_present_no_games`: both games fail if the source remains present after
  withdrawal.
- `package_deletion_no_full`: full game fails because it would imply the actually
  rejected arrival package.
- The two missing-input theorems reject both games before any decoding default.

The full four-control F/O equivalences are **not claimed** in this seam.

## Transcription and self-review

`check_tth06_transcription.py` retains its legacy regression explicitly at the
legacy weaker lineage ceiling, and extends it with direct Lean instruction
exports for all four G6 controls: seven account names/owners/balances/retention,
six-role withdrawal, required recharge, source presence, target/source-mode
charges, and exact effective budget updates. Comparisons use `Fraction` against
frozen G6b ledgers and the declared raw withdrawal rules. Five new in-memory
drift probes reject balance, ownership, retention, absent charge and source-mode
maintenance use. This is transcription, not a claim of game equivalence.

Self-review corrected the raw charge credit to use **effective** retained
recharge, and rejected source-mode maintenance charges. Positive games and the
canonical lift are proved under those actual rules. These are additions to the
TTH-06 binding, classified **(b) mathematical constructions**; no existing theorem
statement or status is changed.

## Remaining gates

1. Exact F/O runtime equivalences for arbitrary partial assignments. In particular,
   bind the frozen unit-ledger and whole-family response/readout checks; a more
   general resource game must not be called equivalent merely because canonical
   truth agrees.
2. Check the complete temporal recipe/closure binding and complete generic
   lineage from the shared runtime; retain distinct paths, shared endpoint,
   every-branch retention and complete actual-execution transport.
3. Final polymorphic `RawHandoff`, soundness, readout separation/dependence,
   complete control vectors including relabeling, and promotion fidelity review.

No CST-TT-08 file, model declaration, registry, inventory or `paper/` is changed.

## Verification receipt

- `cd lean && lake build`: green (477 jobs; final build 9.02 s;
  initial three-module compilation approximately 2.6/2.8/4.0 s).
- `python3 -B scripts/check_tth06_transcription.py`: exact comparison passes;
  five new resource drift probes caught, old comparisons retained.
- `#print axioms` probes for all 56 new theorems: only `propext`, `Quot.sound`,
  and `Classical.choice`, or fewer.
- `scripts/validate_lean.sh`: exit 0; 39 rows / 210 row declarations resolve;
  no untrusted axioms, no placeholders, no high-confidence vacuity; 38
  non-gating heuristic leads across CSTTT. Inventory and registry unchanged.
- Forbidden-construct scan of the new modules: no findings.

Build warnings are replayed pre-existing linter warnings; none originate in
these three modules.
