# G6d historical protocol and generic TTH-05 entry transport

## Proved boundary

TTH-06 remains **conditional**. This seam completes the generic historical
finite-factor **transport theorem**, and extracts the frozen phase-2 and
nominal protocol as actual typed instructions. It does **not** complete the
polymorphic POS-04 whole-game instance or `RawHandoff` assembly.

| Module | What is proved |
|---|---|
| `StaticSlice` | A polymorphic typed instruction reads exactly a finite dependency slice. Successful evaluation equals the immutable decoder, for arbitrary partial assignments. Missing any consumed cell yields `none`; duplicate scope IDs read the same cell. |
| `POS04HistoricalProtocol` | Exact arbitrary-partial `check_iff` and `all_routes_iff` with frozen `phase2Check`; readiness, normalized response rows, exact support iff raw row membership, and actual updates on **every** ambient response branch. |
| `POS04HistoricalRuntimeProtocol` | Exact arbitrary-partial instruction acceptance iff frozen `POS04OperationalGame.Protocol`, including raw withdrawal metadata, advancement, canonical-row preservation, and all phase-2 routes. This is the protocol, **not** AF/AO itself. |
| `HistoricalFiniteAutonomy` | Raw finite-factor system/withdrawal/package/response construction for `HistoricalPackageRuntime`; checked projection laws; TTH-05 certificates at every actual historical entry; every finite disturbance word; all-support preservation. |

### Exact acquisition extraction

`POS04HistoricalProtocol.check rid` is the composition of the typed
`StaticSlice.instruction phase2Dependencies` and the existing raw phase-2 rule.
The staged slice is put back into the source namespace by the proved
assignment involution. No caller supplies a candidate slice, decoded data,
activation verdict, entry set, or desired class.

`check_iff` quantifies **all partial assignments**. The rule checks activation
by all eligible raw event records, first-match path lookup, realized unit steps,
source and target historical support, typed entry/exit boundaries, target
resource/ownership availability, the route writer, and the nonempty strictly
positive four-unit target row. `ready_of_check` proves the extracted check gives
the generic historical interpreter its actual required cells. `response_rows`,
`response_support_iff`, and `response_all_branches` identify every supported
ambient branch and actual successor, without predictive representative choices.

The extracted checks preserve the duplicate-ID, missing-source-tick and
unavailable-source-recharge diagnostics (`duplicate_event_regression`,
`missing_past_ticks_regression`, `source_recharge_regression`). The registered
package and lineage deletions also retain their acquisition checks. Source
absence rejects independently. None of this changes funded actual **lineage**
execution, which legitimately consumes source ticks and source resources.

`POS04HistoricalRuntimeProtocol.check m` additionally interprets the raw
withdrawal metadata, target advancement/ledger/writer rules, and P-preservation.
`check_iff` is precisely a biconditional with the existing nominal protocol.
Safe response strategies and run-context package preservation remain separate
obligations; a passing protocol is not an autonomy proof.

### Generic TTH-05 result

`HistoricalFiniteAutonomy` reuses `RawFiniteAutonomy.Frame` and the proved
`GameAutonomyTransport` engine. It binds that engine to
`HistoricalPackageRuntime` instead of funded-source `PackageRuntime` acquisition.
The finite factor step is **defined** as the image of a legal actual positive
branch; its advancement/solvency relations are actual update-law witnesses.

`full_readout_each_entry_exact` says, for arbitrary raw types, model `m`, finite
frame `f`, and partial source assignment `a`, given `Checked m f a`, the proved
`Lift m f a` equations, and `PostWithdrawalFullAutonomy m a`, one constructed
strategy invariant supplies `ExactAutonomyCertificate` at **every** historical
entry. `full_readout_nonempty_exact` separately exhibits a genuine entry;
`full_readout_each_entry_words` applies TTH-05 to every finite declared
disturbance word. `all_support` retains **every** actual branch of each causal
response before the finite projection.

The lift is proof-bearing per-instance evidence, not a generic finite-context
assumption. Its primitive equations cover every package-relevant run; resource
and account equations cover every resource-relevant run. Disturbances/actions
are the actual execution domains, with a nonempty disturbance domain. This is
not decision completeness of a finite constructor for unrestricted recipes.

## Argument classification

| Argument | Classification |
|---|---|
| Cell/value, register/value, factor, outcome, resource, action, disturbance and acquisition types | Raw polymorphic interfaces. |
| Historical package/runtime `m`, stage, cover, closed dispatcher and target updater | Raw data; target assignment and all game interpretations are defined by the committed binding. |
| Finite frame enumeration, projection/cell/resource/owner instructions and resource IDs | Raw finite projection instructions; exhaustive enumerations and identifiers checked. |
| Source assignment / POS-04 withdrawal metadata | Raw data. No lane outcome supplied. |
| `Checked`, `Lift`, phase-2 completeness and exact raw equations | Evidence on raw data; missing inputs reject. `Lift` is required and proved per instance, never a supplied boolean. |
| Game readout | A semantic premise for the transport theorem, derived from invariant-game soundness at the enclosing validity layer. No raw record stores it. |
| Slice, decoded assignment, rows, updater, factor system, withdrawal, invariant and TTH-05 certificate | Defined or theorem-constructed objects. |

## Field/readout coverage and guards

This table covers this seam; it is not the final RawHandoff promotion table.

| Field | Law/check | Guard or exact equation |
|---|---|---|
| Every finite slice cell | Eager typed read; immutable decoder identity | `StaticSlice.missing_rejected`, `read_iff`, `locality` |
| Source/target rows, policy, histories | Raw historical support and exact target response | `POS04HistoricalProtocol.missing_rejected`, `response_rows`, `response_support_iff` |
| Events, realization, receiver, route, writer | Frozen phase-2 raw rules on the same slice | `check_iff`, `missing_cell_all_routes_rejected`, `source_absent_rejected`, duplicate regression |
| Target ticks, resources, maintenance, withdrawal metadata | Frozen nominal protocol; raw price, advancement, P-preservation | `POS04HistoricalRuntimeProtocol.check_iff`, `missing_rejected`, `locality`, `zero_ledger_rejected`, `postwithdrawal_source_present_rejected` |
| Unconsumed source ticks/resources/hazards | Exact scope exclusion | `no_source_ticks`, `no_source_resources`, `no_hazards`, `replacement_unchanged` |
| Finite projection, required support, action/resource owner instructions | Complete instruction dependencies | `HistoricalFiniteAutonomy.missing_field_guard` for each `InputField` |
| Resource identifier, source/target carrier, disturbance/action enumerations | Injectivity, distinct carriers, equal actual domains, nonempty disturbances | `aliased_resource_guard`, `empty_disturbance_guard`, `Checked` |
| Factor package primitive views | Equality with actual run assignment on **all** package-relevant runs | `changed_factor_cell_guard`, `missing_factor_cell_guard`, `Lift.cells` |
| Required resources | Equality with actual run support; retained inclusion | `changed_resource_table_guard`, `omitted_resource_guard`, `required_retained` |
| Account/resource/action ownership | Actual account and owner equations on relevant runs | `changed_account_owner_guard`, `wrong_resource_owner_guard`, `wrong_action_owner_guard` |
| Actual order/tick/progress/record/residue/balance updates | Inherited `ResourceRuntime.StepLaw` against the actual shared updater | `projection_laws`, `all_support`; no finite-state strict-growth claim |
| Historical entries and safe responses | Defined activated entries; game-derived nonempty invariant; all-support response law | `full_readout_nonempty_exact`, `full_readout_each_entry_exact`, `all_support` |

## Remaining work, in order

1. Bind these explicit phase-2/nominal instructions into the **whole** POS-04
   historical package/resource runtime, and prove its F/O game biconditionals
   with AF/AO for arbitrary partial assignments. In particular, enforce all
   declared routes and the complete writer/ledger/strict-positive-row protocol;
   the bare historical acquisition component alone does not enforce them.
2. Instantiate `HistoricalFiniteAutonomy.Checked`/`Lift` on that whole runtime
   using the already-proved actual ledger/register/primitive equations. The new
   generic transport has **not** yet acquired that concrete whole-runtime
   instance. Existing family historical TTH-05 instances remain valid.
3. Combine complete funded actual lineage (corridor, all four snapshots, full
   execution bridge, endpoint, factor/record, and `Indexed`/`Retained` route
   semantics) from the same raw cells. Do not infer it from historical autonomy.
4. Finish RawHandoff F/O soundness, named O separation, F dependence, all POS-04
   control/diagnostic equivalences, transcription extension and promotion gate.

No claim of whole-game equivalence, final generic lineage, final RawHandoff
soundness, or promotion is made here. The 09 registry and inventory are unchanged.

## Statement changes

All additions are **(b) mathematical additions for TTH-06**: exact typed raw
protocol extraction and generic historical TTH-05 transport (reusing the
existing TTH-05 theorem unchanged). No (a) renames, no changes to existing Lean
statements, row text, ceilings, statuses, frozen models, or CST-TT-08 files.
No new model or prediction is declared.

## Verification

Commands:

```sh
cd lean && lake build
cd .. && scripts/validate_lean.sh
python3 -B scripts/check_tth06_transcription.py
```

Explicit axiom probes cover every new theorem. The existing transcription
checker remains a **family regression**, not a transcription claim for the
unfinished polymorphic assembly. `paper/` is untouched.


Verification receipt for this seam:

- `lake build`: exit 0, **491 jobs**. New-module build times: `StaticSlice`
  1.3 s, phase-2 protocol 5.0 s, nominal runtime protocol 3.6 s, historical
  finite autonomy 6.5 s. No new-module warnings; existing replayed warnings remain.
- `scripts/validate_lean.sh`: exit 0, overall **pass**; 39 rows, 210 evidence
  occurrences (209 distinct declarations), no untrusted axioms, placeholders or
  high-confidence vacuity findings. The heuristic scan reports 39 non-gating
  leads, including the new factor-assignment declaration; this is not a vacuity
  verdict.
- Explicit `#print axioms` probes: **69/69** new theorems resolve, with axioms
  contained in `propext`, `Classical.choice`, `Quot.sound`.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0; unchanged family
  observations and planted-drift checks pass. No unfinished generic assembly
  is claimed to be transcribed by that check.
- Forbidden-construct scan of the four new modules and `git diff --check`:
  clean. Tracked CST-TT files are byte-identical to HEAD. No registry or
  inventory changes; no edits to `paper/`; no commit.
