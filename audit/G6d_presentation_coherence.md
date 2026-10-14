# G6d — endpoint/factor/record presentation boundary

TTH-06 remains **conditional**. This seam proves presentation equations and
an inhabited, arbitrary-partial POS-04 specialization. It does **not** export
`RawHandoff`, final generic F/O soundness, or claim that the promotion gate is
complete. Existing declarations and frozen definitions remain unchanged.

## Construction and exact scope

`FramePresentation.Raw` contains separately typed source/receiver acquisition
frames, raw finite primitive schemas/views, typed coordinate instructions,
event/receiver views, stage/owner interfaces, factor-map instructions and a
record decoder. `FramePresentation.presentation` **defines** the temporal
presentations from the frames: rows, updater, period and all evolving observer
instructions are inherited. Only the predictive alphabet is translated by its
raw typed image. No future, code, closure, probability table or observer
candidate is supplied. This extraction uses the endpoint's common finite
coordinate alphabet; the run frames remain separately typed and unbounded.

`PresentationCoherence.factorView` reads exactly seven factor inputs. Its
projection theorem follows from the eager sixteen-input temporal decoder.
Thus decoding the endpoint yields the same factor rows, hazards, policy,
positions, ticks, ledger and owner/resource primitives. The factor decoder
does not acquire dependencies on unrelated temporal fields.

`RecordLaws` compares priority-resolved raw event shapes, both full temporal
event lists, realization, both writer tables and the raw clock. Duplicate IDs
retain the frozen priority-lookup semantics; activation remains all-records.
The record audit's unit increment is **not** asserted equal to execution's
stage difference on arbitrary malformed events. `record_increment` and
`POS04PresentationCoherence.event_increment` derive agreement on certified
strict events. The record clock and carrier/stage interfaces are also checked
against the acquisition frames by `FramePresentation.SchemaCheck`.

`PresentationCoherence.Pass` is an interpretation-coherence predicate, not a
clause or autonomy verdict. It requires all-context temporal simulation laws,
actual endpoint/record decoder presence and the record equations. It does not
assert clause acceptance. Missing consumed inputs reject before fallback data
can become evidence. These checks do not require source funding in historical
F/O acquisition; funded actual source execution remains a lineage obligation.

## Main receipts

Names are under `CSTTT.TargetTheory.GenericHandoff`.

| Receipt | Content |
|---|---|
| `PresentationCoherence.decoded_fields`, `factor_decoded`, `endpoint_factor_decoded` | Every primitive/projection follows from successful eager decoding |
| `factor_predictive`, `factor_action` | Predictive classes and action weights use those projected raw fields |
| `FramePresentation.row`, `updater`, `observer`, `predictive` | Frame-owned probability/program/readout construction |
| `source_interface`, `target_interface` | Stage, route, event, clock and owner interface equations |
| `POS04PresentationCoherence.factor_decoder` | Exact seven-cell decoder equality for **every partial assignment**, on both tags |
| `endpoint_factor`, `endpoint_source_primitives`, `endpoint_target_primitives` | Endpoint and factor inputs are the same temporal primitives |
| `package_source_primitives`, `package_target_primitives` | Source and target closed-dispatcher C6 rules use those same primitive bindings |
| `runtime_laws`, `shared_frame` | All-run simulation plus all five coordinates of the shared runtime frame |
| `record_laws`, `event_increment` | Assignment-owned events, clocks, realization, writers and certified increments |
| `constructed_presentation`, `public_source_frame`, `public_target_frame` | Generic constructor equals the POS-04 presentation; frames are the public runtime frames |
| `checked`, `checked_of_lineage`, `public_coherence` | Interpretation equations for arbitrary partial assignments with the consumed inputs; complete semantic lineage supplies their presence |
| `canonical_checked` | Nonvacuous concrete instance |

## Argument classification

| Argument / field | Classification | Constraint |
|---|---|---|
| Cell/value families, finite coordinate/action/outcome/event/route domains, register types | Raw interface | No POS-04 alphabet/cardinality in the generic constructors; finite coordinate presentation is not the unbounded run |
| `sourceFrame`, `targetFrame` | Raw acquisition programs, views and schemas | Their existing execution/closure/readout checks; temporal rows/programs/readouts are inherited by definition |
| Source/target primitive schemas and sixteen cell views | Raw data | Eager decoding; temporal all-context simulation; stage/interface equations |
| Predictive translation, finite run projection, owner translation | Raw typed coordinate instructions | Actual probabilities, successors and every observation checked by `TemporalRuntimeCoherence.Laws`; owner injectivity checked there |
| Supported events / receiver / record / factor maps | Raw instruction decoders | Endpoint/record presence, `RecordLaws`, existing factor transport equations |
| Entry/exit/event/fallback/scale/transfer/clock | Raw schema operations | Endpoint execution rule, stage/owner/clock schema equations; fallback cannot establish presence |
| Assignment | Raw immutable data | One constructed target from `PublicRuntime`; `public_coherence` uses that exact assignment |
| Readiness, equations, supported-step hypotheses | Evidence on raw data | Not stored verdict flags or supplied semantic conclusions |
| Factor/endpoint bindings, temporal presentation, code, observer, future/closure, record edges | Defined objects | Derived from the above raw data and existing interpreter, never independent candidates |

## Field coverage and guards

| Raw family | Check / equation | Guard |
|---|---|---|
| Factor rows, position, hazards, policy, ticks, resource, ledger | Defined projection; exact decoder equality | `missing_factor`; `factor_field_guard` parameterized over **each** field/coordinate; concrete `factor_tick_guard`; existing factor transport field controls |
| Endpoint sixteen-input cells / events / receiver | Eager decoder then projection | `missing_endpoint_rejected`, `missing_endpoint` for every consumed cell; existing constant-receiver and exit-deletion semantic negatives |
| Rows and actual successor | Inherited frame instructions plus all-context simulation | `source_row_guard`, `target_row_guard`, `source_update_guard`; concrete `erased_row_guard`, `stationary_update_guard` |
| Predictive/order/tick/progress/record/residue/maintenance/owner readouts | Inherited frame observer; checked full observation equation at **every run** | `source_readout_guard` parameterized over each component; existing temporal field guards; concrete `capped_progress_guard` |
| Writer and absolute ticks | Inherited frame instructions; temporal `Laws.writer` / `ticks` | Existing `TemporalRuntimeCoherence.writer_guard`, `ticks_guard` |
| Record events (including support/atomic/strict/stages) | Resolved structural shapes and complete temporal event-list equality | `record_event_guard`; concrete event erasure |
| Record realization | Both temporal presentations and record agree | `record_realization_guard`; concrete `record_realized_guard` |
| Source/target writer tables | Exact raw table equality; closure writer is separately simulation-gated | `record_writer_guard`; concrete target-writer erasure |
| Record clock / strict increment | Raw clock equality; arithmetic from certified strictness | `record_clock_guard`, `record_increment`; concrete zero clock |
| Frame stages/events/routes/entry/exit/clock/owner | `SchemaCheck`, `source_interface`, `target_interface` | `source_interface_guard` / `target_interface_guard` with each field selector; concrete `frame_clock_guard`, `frame_owner_guard` |
| Typed factor/run frame | `frame_projection`, `shared_frame`; existing actual-support execution links | Projection missing-input / successor guards; existing omitted-positive-branch regression |

The guards reject coherence itself where stated. Existing concrete temporal
controls reject `TemporalRuntimeCoherence.Valid`; they are labeled as reused
component controls rather than a claim that a sufficient check's failure alone
refutes its semantic conclusion. Missing guards have consistent hypotheses;
none assumes readiness together with absence of a required input.

## Remaining promotion work

1. Bind this owning frame/presentation construction, package stage/cover and
   closed schemas into **one final polymorphic `RawHandoff`**. Public runtime
   resource sharing and target execution spans are already proved, but this
   module does not yet put every interpretation parameter under that owner.
   The final binding must retain the raw endpoint/record/factor interfaces and
   check the coordinate translations; it cannot merely wrap independent data.
2. Prove exact lane adapters for that final value, generic F/O soundness,
   genuine-entry `AF ⇒ P`, and named O separation / all controls, reusing the
   existing all-partial public-runtime/game/complete-lineage equivalences.
3. Extend transcription to the assembled interface and assess the frozen row.

No exact-equivalence counterexample was found in this seam. The full promotion
is unfinished, not refuted. Historical acquisition, selected-response
StrictSparse representation sensitivity, positive-support coverage, nominal
all-support/no-resource-shock scope, C4–C7 surrogate grades and the sound but
potentially incomplete finite constructor remain disclosed. Recognition is
not addressed. No frozen statement is narrowed or split.

## Statement changes and checks

All additions are **(b)**, TTH-06: owning raw presentation construction,
interpretation equations, exact partial adapters and guards. No (a) changes;
no existing Lean statements or CST-TT-08 files changed. The 09 status and exact
statement are unchanged; evidence/ceiling/rationale and the generated inventory
record the proved boundary and remaining gate.

- `cd lean && lake build`: exit 0, 521 default jobs. The build adding the
  presentation specialization took 7.53 s; subsequent generic/schema additions
  rebuilt `FramePresentation` in 5.2 s and the POS-04 specialization in 4.3 s.
  Final incremental run: 0.27 s. No warnings in the three new modules; inherited
  replayed lint warnings remain.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0, **36** planted
  transcription drifts caught (four new). Exact `Fraction` comparisons of both
  tags' factor rows, raw record event shapes/increments, realization, stage
  clock and assigned writers. A second complete run is byte-identical by `cmp`.
  Universal partial-assignment equations and direct rejection guards are
  kernel-checked in temporary Lean probes, rather than exported as verdicts.
- Inventory regenerated; `scripts/validate_lean.sh`: exit 0, 39 rows,
  274 evidence entries / 273 unique, 265 theorem-kind, 8 statement-only and
  1 other definition. No placeholders, untrusted axioms or high-confidence
  vacuity findings; 46 nongating heuristic leads, unchanged.
- All **81** new theorem declarations checked and axioms printed: standard
  three or fewer, including **25 axiom-free** declarations.
- New-module forbidden-construct scan and `git diff --check`: clean.
  Five frozen CST-TT-08 status surfaces byte-identical to HEAD. Only TTH-06's
  09 evidence/ceiling/rationale changed, with status/text unchanged. All edits
  are uncommitted; `paper/` and frozen model declarations untouched.

Self-review: the source/receiver frames are separate dependent register
families; equality of labels alone is not used as a frame proof. The frame
constructor has no alternative weight/updater/observer argument. The minimal
factor decoder equivalence covers absence as well as present values. Record
comparison uses the same raw priority lookup even for duplicate IDs, and
certified increment agreement does not claim agreement on malformed events.
The canonical instance establishes satisfiability. This remains a presentation
constructor and raw interpretation check, not an assembled generic handoff;
no certificate soundness or TTH-06 promotion is inferred from it. The remaining
ownership/assembly hinge above is explicit.

Ignored receipts: `lean/.validate-logs/g6d-presentation-*`; final validator JSON
`lean/.validate-logs/run-20261009T114859-450004Z/report.json`.
