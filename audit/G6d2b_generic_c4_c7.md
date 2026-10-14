# G6d-2b: generic C4 and C7 seam

## Proved boundary

`ExposureRules` and `JointRules` are polymorphic in their carriers, actions,
outcomes, histories and dependent cell namespace. C7 additionally varies branch
indices, assemblages, observations, stages and event IDs. Finite lists and their
coverage checks are raw schema data; none of the generic modules imports POS-04.
Channels, predictive readouts, branch records, exact rational pairing,
recombination, mixed-event detection, activation and receiver display are defined.
There is no supplied acceptance or display function. Option decoders reject any
missing consumed cell. Decoder, acceptance and gate locality are proved.

`POS04Exposure.generic_c4_iff` and `POS04Joint.generic_c7_iff` give both directions
for **every partial assignment and both tags**, not just canonical truth.
`POS04Joint.generic_transport_iff` does the same for staged transport.
Canonical witnesses, all four C4/C7 declared control outcomes and field guards
are transported through these equivalences.

Grades remain unchanged: C4 is the narrow collision/connector surrogate, with a
nonconstant exposed channel factoring through the computed predictive readout.
`full_nonexposure_fails` expressly rejects the full non-exposure condition used
here. This is not a proof of HIDD. C7 is the declared joint-distribution
recombination surrogate, not endogenous joint-history binding. Its operational
check requires a realized mixed event, activation, distinct computed receiver
displays, and canonical action-row agreement. Displays need not equal a fixed
baseline pair. The uncoupled control remains locally consistent and loses
refinement; the transport control is source-accepted, target-locally-consistent,
target-rejected, and transport-rejected, matching the existing L6b adapter.

## Argument classification

| Argument | Classification | Use |
|---|---|---|
| Type parameters, decidable equality | Raw typed interface | Arbitrary carrier/namespace, no ten-state generic constant |
| `Schema` | Raw enumerations, reference tables and declared instruction vocabulary | Domain coverage, split, row scale, reconstruction, reassembly |
| `Bindings` | Raw typed cell projections | Shared cell reads; scope defined from views |
| `Assignment` | Raw partial immutable cell data | Option decoding before any rule |
| Locality, rejection or acceptance hypotheses | Evidence on raw checks | Theorems consume the stated equations/membership facts |
| Source/target raw joint tables and typed state map | Raw transport data | Branch-record, coupling and distribution equations |
| Decoder output, predictive profile, channels, distributions and display | Defined objects | Not theorem arguments independent of the raw inputs |
| POS-04 `ExtraInputs` in adapter equations | Defined legacy decoder readout | Decoder equality and completeness gate link it to shared cells |

## Field coverage and guards

Names in the last column are in the indicated POS-04 adapter namespace.
Every listed guard rejects the generic acceptance predicate.

| Cell family | Computed law/check | Guard |
|---|---|---|
| C4 rows | Row validity, predictive hazards, supported connector | `POS04Exposure.rows_guard` |
| C4 positions | Computed predictive partition linked to declared M | `positions_guard` |
| C4 hazards | Raw action hazard words in predictive partition | `hazards_guard` |
| C4 channels | Interpreted instructions, collision and nonconstant exposed channel | `channels_guard`; `expose_control` |
| C4 policy | Actual connector transition weights | `policy_guard` |
| C4 histories | Connector endpoints, length and positive supported edges | `histories_guard` |
| C4 class reconstruction | Raw predictive equivalence and ordered reference classes | `classes_guard` |
| C7 joint left/right | Ordered branch records and joint refinement | `POS04Joint.left_guard`, `right_guard` |
| C7 joint coupling | Exact pair counts; nonzero cardinality, reassembly and strict refinement | `coupling_guard`; `uncoupled_control` |
| C7 joint reassembly | Coupling equals declared raw reassembly table | `reassembly_guard` |
| C7 joint observables | Fixed observable enables computed distribution display | `observable_guard`; `aggregate_control` |
| C7 rows | Valid exact scaled rows, supported histories, operational P equation | `rows_guard` |
| C7 policy | Supported canonical history execution | `policy_guard` |
| C7 histories | Nonempty supported paths and distinct raw path identities | `histories_guard`, `distinct_histories_guard` |
| C7 published P | Exact reconstruction from operational rows | `publishedP_guard` |
| C7 events | Realized non-exit atomic event with both supports | `events_guard` |
| C7 realization | Both mixed-event stages realized | `realization_guard` |
| C7 receiver presence | Activation needs source presence | `source_presence_guard` |
| C7 receiver funding | Both receiver and target funded | `receiver_funding_guard`, `target_funding_guard` |
| All consumed cells | Complete Option decoding, independently of defaults | Both adapters' `missing_rejected` (every cell in scope) |
| Transport | Typed mapped branch records, coupling and exact distributions | `transport_control` |

Generic guards additionally reject constant predictive readouts, empty channels,
short connectors, altered class reconstruction, absent mixed events, inactive
receivers, equal displays, absent observables, zero coupling size, wrong published
rows and duplicate raw histories. These are sensitivity guards, not independent
scientific model declarations.

## Not yet proved / status

G6d-2c (generic temporal rules and generic C8 with the run-to-factor lift) remains
next. No finite-context premise or run-to-factor lift is asserted in this seam.
The §7.4 stop rule still applies before that layer can be claimed complete.
TTH-06 remains conditional; no registry, inventory or frozen science file changes.

All additions are (b) mathematical extraction/adapter additions for the TTH-06
construction at its existing graded ceiling. Existing declaration statements are
unchanged; there are no (a) renames and no promotion.

## Verification / self-review

- `cd lean && lake build`: exit 0, 373 jobs; new adapters compiled in 15s
  (C4) and 24s (C7) on the final builds. No warnings from the new modules;
  existing CSTTT/vendor warnings remain.
- `scripts/validate_lean.sh`: exit 0; 39 rows, 210 evidence entries (209 unique),
  no untrusted axioms, no placeholders or high-confidence vacuity findings.
  There are 29 non-gating heuristic leads elsewhere in the tree.
- `/tmp` `#print axioms` probes cover all 96 new public theorems: only
  `propext`, `Quot.sound`, `Classical.choice`, or fewer.
- Self-review traced Option decode → raw computations → gate/rule → acceptance,
  and checked both-direction partial-assignment equations, missing cells, mixed
  realization/activation, transport and consistent uncoupled-control rejection.
  No claim of an independent review or of completed temporal/C8 extraction.
