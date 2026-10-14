# G6d: nominal historical component equivalences

## Proved

This is the entry/package/resource interpretation boundary needed by the whole
F/O adapter. **The whole AF/AO game biconditionals and final RawHandoff assembly
remain open.** TTH-06 stays conditional; no registry or inventory change.

All new mathematical additions are (b), for TTH-06. Existing declarations and
frozen semantics are unchanged. No new model or numerical rule is declared.

Modules and principal declarations, under `CSTTT.TargetTheory.GenericHandoff`:

| Module | Result |
|---|---|
| `POS04HistoricalEntryEquivalence` | `raw_entries_iff`, `entries_iff`: exact agreement with every frozen phase-2 entry for arbitrary partial assignments satisfying the nominal protocol |
| same | `entries_target`: every raw entry has target tag; `branch_entry`: every actual positive-support branch, including exits, is retained |
| same | `checked_entries_iff`: the adapter consumes the interpreted `POS04HistoricalRuntimeProtocol.check`, not a supplied verdict |
| same | `baseline_entries_iff`, `duplicate_event_entries_iff`, `missing_past_ticks_entries_iff`: whole entry relations for the baseline and diagnostics |
| `POS04HistoricalPackageEquivalence` | `inside_iff`, `package_at_iff`: the resource-factor and assignment-sensitive package readouts agree with the frozen run-context predicates |
| `POS04HistoricalResourceEquivalence` | `resource_closed_iff`: exact resource closure on every target run context |
| same | `response_rows_eq`, `update_eq`: exact target probabilities (`response_rows_eq` additionally assumes `ResourceClosed` at the run: at an unfunded run generic rows are empty while frozen rows are not) and actual updater; no representative branch is substituted |
| same | `writer_eval`, `record_eval`, `accounts_eval`, `charge_eval`: computed raw readouts agree with the assigned operational fields |
| same | `legal_of_resource_closed`: legal unit-ledger expenditure, with target ownership derived from assigned fields |

The protocol implies the declared unit ledger and target ownership
(`unit_fields`). Those values are not new constants: they are precisely the
frozen `Ledger8` constraints and raw resource-owner check. `withdrawn_eq_image`
proves that the funded nominal retention rule leaves every target primitive
unchanged, including missing values. It does not keep source acquisition
supports available after withdrawal.

The entry construction reads the twelve acquisition cells before decoding,
checks both source and target recorded-history support, scans all eligible
records for activation, and resolves path IDs according to the frozen first
record rule. Its strict realized path includes the unit clock law. The terminal
factor and provenance are computed from the actual history; target rows and
updates keep all ambient branches. Nothing assumes unique event IDs, source
funding, source ticks, or hazards.

## Argument classification

| Argument | Classification |
|---|---|
| `m : RawLaneModel`: partial assignment and withdrawal metadata | Raw data |
| Assigned rows, policies, histories, events, scopes, rules, receiver, routes, resources and ledger | Raw cells, interpreted by committed instructions |
| Nominal `Protocol m`, checked instruction equation, completeness and supported-branch membership | Evidence on raw data |
| History/path arguments to intermediate lemmas | Values constrained to the actual decoded route by `routeTuple = some …` |
| Runtime model, decoded data, received state, entry set, target assignment and run assignment | Defined objects; no supplied candidate |
| Readiness evidence | Derived from the interpreted protocol before totalization |
| Unit account/charge displays | Defined values whose equality to raw evaluation is proved from the declared ledger rules |
| Package/resource conclusions | Derived readouts |

## Field coverage and guards

| Field family | Checked binding/law | Guard/regression |
|---|---|---|
| Rows and policy | Exact `source_rows_read`, `target_rows_read`, `policy_read`; both recorded support relations | `missing_protocol_cell_rejected` quantifies every consumed cell |
| Histories and routes | `histories_read`, `routes_read`, `tuple_views`; no supplied entry | Exact baseline and missing-past-tick entry relations |
| Events/realization | `events_read`, `realized_read`, `phase2_raw_path`, `phase2_boundary` | Missing-cell guard; duplicate-ID regression preserves all-record activation |
| Receiver/activation | `receiver_read`, `activation_read`, `protocol_arrival`, `arrival_unique` | Missing-cell guard; committed source-absent rejection remains applicable |
| Target probabilities/successor | `branch_entry`, `entries_target`, `response_rows_eq`, `update_eq` | No branch filtering; entry biconditional covers exits as well. `response_rows_eq` holds under the extra `ResourceClosed` premise only |
| Package primitives and views | `withdrawn_complete`, `state_views`, `package_at_iff`; acceptance uses the closed dispatcher | Existing dispatcher missing-input guards; no extra all-cell gate is imposed on O |
| Ledger/resources/owner | `resource_data`, `unit_fields`, `accounts_eval`, `charge_eval`, `resource_closed_iff` | `wrong_owner_rejected`, `nonunit_ledger_rejected`, and missing-cell guard |
| Writer/record | `writer_eval`, `record_eval`, computed from the actual register | Missing writer/history/route input rejects before decoding |
| Withdrawal metadata | `withdrawal_read`, committed interpreted protocol, `withdrawn_eq_image` | Committed withdrawal-deletion rejection; no source support becomes a maintenance resource |

These are component equations, not the final closure/readout coverage table for
RawHandoff. The mandatory whole-game transition laws and complete lineage
remain completion gates.

## Next proof boundary

Construct both directions of the protocol-bound historical F/O invariant and
strategy transport. The existing entry, package, resource, row and updater
identities now supply their exact interpretation equations.

**Do not claim a pointwise legality biconditional.** Generic resource `Legal`
checks target-owned expenditure, whereas frozen operational `Legal` also checks
row closure in the factor kernel. For the reverse transport, derive that closure
from the chosen normalized response and every supported successor's invariant
membership. Then prove the actual `StepLaw` transport, using the record/ledger
and updater equations above. No assumed alignment flag or stronger legacy
acceptance condition is permitted.

After those game biconditionals: shared generic complete lineage, polymorphic
RawHandoff assembly, named-readout separation, controls, extended transcription,
and the faithful promotion gate. The remaining work is not replaced by a
conjunction with AF/AO or by canonical truth alone.

## Checks and self-review

- `cd lean && lake build`: exit 0, 496 jobs; final incremental build 14.18 s.
  Existing section-variable warnings replayed; no new-module warnings.
- `scripts/validate_lean.sh`: exit 0; 39 rows, 209 unique declarations; no
  untrusted axioms or gating scan findings. None of the non-gating heuristic
  leads comes from these three modules.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0 at its existing
  coverage, including planted-drift checks. No final generic transcription
  extension is claimed in this component seam.
- `/tmp` axiom probes: all 46 new theorems resolve and use only the standard
  three axioms (or fewer). Forbidden-construct and whitespace checks clean.
- Self-review checked the protocol-before-defaults direction, every entry and
  support branch, the all-record activation rule, and the separate legality
  versus row-closure obligations. Whole-game equivalence is explicitly pending.
- Frozen files, registry, inventory, and `paper/` unchanged. No commit made.
