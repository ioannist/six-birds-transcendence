# G7 — typed primitive-stage composition

TTH-07 remains **conditional**. This packet supplies the typed package-map
algebra needed by full composition, not the final handoff theorem or a two-hop
Temporal-FIACH instance. The frozen statement is unchanged.

`StageComposition.language` packages a typed intermediate cell and the two
raw instructions. Its interpreter executes left then right with `Option.bind`.
`stage` reads the right arrow, checks that its referenced intermediate cell
belongs to the declared left scope, and then reads the left arrow. Neither
absent primitives nor uncovered intermediate cells acquire fallback values.

## Argument classification

| Argument/object | Classification | Binding |
|---|---|---|
| Source/middle/target sorts and dependent values | Raw structural interface | Independently typed; no assumed equality of value sorts |
| Instruction languages, stage arrows, scopes and covers | Raw data | Existing primitive translation semantics and independently declared scope/adjacency |
| Original assignment | Raw data | Arbitrary partial assignment; no positive-fixture premise |
| Composed language/stage and intermediate globals | Defined objects | Actual instruction sequence and first-cover gluing, no supplied global witness |
| `ScopeLink` | Raw reference check | Every consumed right source cell belongs to the corresponding middle scope |
| Totality, reference, value and source-coverage hypotheses | Evidence | Existing independently interpreted primitive equations, not desired lane propositions |
| Middle cover/edge compatibility | Evidence | Existing structural connectivity and local primitive-value equations |
| Numerical witness and mutations | Raw data | Predeclared add/multiply parameters, Unit cells, scope/cover and source value |

`total` permits any middle assignment witnessing the right instruction's
existing `StageTotal`: its universal nonfailure law applies to every actual
left output. The left totality check supplies the original source presence.
This does not supply an independently chosen middle run or global readout.
Actual sequential/global agreement is proved separately.

## Coverage table

| Obligation | Receipt | Scope |
|---|---|---|
| Scope-gated raw arrow construction | `arrow_equation`, `missing_right_arrow`, `missing_middle_scope`, `missing_left_arrow` | All typed raw maps and references |
| Sequential interpreter equality | `local_equation` | Every partial assignment; no totality or readiness assumption |
| Actual negative readouts | `missing_middle_readout`, `missing_source_readout`, `failed_first_instruction_readout`, `failed_second_instruction_readout` | Actual composed output is `none`, independently of sufficient gate failure |
| Middle gluing and final global | `local_on_global`, `global_equation` | Every partial assignment under explicit middle cover/edge/scope equations |
| Composed totality | `total` | Two actual total-map checks plus middle scope-link |
| Reference preservation | `source_equation`, `reference`, `scope_link_reference` | Reference coordinates, including all missing-arrow cases |
| Value preservation | `value_preserving` | Left raw value check and right value check on the constructed left global; actual right references checked |
| Original source coverage | `source_coverage` | Both primitive coverage checks, preserving the first source namespace |
| Three-map association | `local_associative` | Every partial assignment, including failed intermediate reads/instructions |
| Inhabited numerical interpreter | `StageCompositionModels.positive`, `positive_total`, `cover_check` | Nonidentity raw add-then-multiply; actual interpreted output 8 |
| All-partial numerical/global equations | `output_equation`, `global_equation`, `changed_equation` | Every partial Unit assignment, unbounded Nat values |
| Raw absence controls | `source_missing`, `scope_missing`, `right_arrow_missing` | Actual output `none`, not Boolean gate rejection |
| Instruction versus coordinate distinction | `changed_reference`, `instruction_change_changes_readout` | Reference stays the same while actual output changes from 8 to 10 |

`value_preserving` uses exact constructed local/global equality on both
right-stage variants. Reference preservation transfers the raw scope-link to
the right reference stage; left value preservation identifies the two actual
middle locals. No acceptance or desired composite readout is a hypothesis.

## Witness and transcription

`audit/proposed_models/TTH07-STAGE-COMPOSITION.model.json` was declared before
evaluating the witness. Its numerical instruction parameters, source value,
Unit typed cells, scope/cover and raw controls define the Lean model. The
instructions add the declared parameter and multiply by the declared parameter;
they do not contain the expected output or a stored success flag.

`scripts/check_stage_composition_transcription.py` compares the interpreted
Lean parameters/cover and actual global/local/control outputs with the raw
JSON. It compiles arbitrary-partial output and direct absence probes, and
catches four planted parameter/scope drifts. The all-partial and generic
composition claims are kernel theorems, not finite numerical observations.
This witness has no corridor, bridge, receiver or autonomy data and therefore
does not establish the required full two-hop non-vacuity gate.

## Statement classification and remaining work

All **29 new theorems** (18 generic and 11 model) and the additional definitions
are **(b)** additions. No earlier Lean statement, frozen theorem text or status
is changed; no new axioms. Registry/inventory evidence attaches these exports
to TTH-07 as component evidence only.

Next: assemble the closed dispatcher/package composition from these primitive
laws; construct actual receiver sequencing, delivered-history reachability,
content distinction and source-absence propagation; concatenate actual
corridor legs; compose all-run bridge and funded resulting-route readouts;
transport final target/autonomy through the actual composed stage/withdrawal;
and provide a genuine predeclared two-hop raw positive before promotion.

The current `ScopeLink` connects the same clause index on both stages. A full
POS04 composition can instead read a middle cell supplied by a different
left clause (for example, a right c2 source-row reference versus a left c2
target-row scope). The full package composer must select the prefix clause
using the **same `firstCover` selector as the actual constructed left global**.
The conditional local/global theorem here is correct but does not discharge
that cross-clause construction. No same-index restriction will be silently
imposed on the full TTH-07 target.

## Review and verification

Fresh read-only reviewer `/root/stage_composition_review` (`gpt-6.1-sol`, high
effort) returned **ACCEPT**, with no required fixes. It assessed the packet as
a faithful primitive-stage component and explicitly retained the conditional
full TTH-07 target. It independently compiled both modules, checked all 29
exports/axioms (only `propext`, `Quot.sound`, or none), exact unique registry
coverage and inventory consistency, and the dedicated checker with its four
planted drifts. It confirmed the arbitrary middle-assignment totality argument
and the separate cross-clause prefix-selector obligation.

Manager self-review confirmed all-partial Option propagation, actual decoded
local/global equations, primitive-law composition and direct instruction
controls. Fresh final checks:

- `(cd lean && lake build)` passed, 539 jobs;
  `lean/.validate-logs/stage-composition-build.log`.
- `scripts/validate_lean.sh` passed, 39 rows, 539 entries, 538 unique exports,
  530 theorems, eight statement-only declarations and one definition; zero
  placeholders, high-confidence findings, untrusted axioms or issues. Receipt:
  `lean/.validate-logs/run-20261009T153319-506628Z/report.json`.
- `python3 -B scripts/check_tth06_transcription.py` passed, all 38 planted
  drifts; `lean/.validate-logs/stage-composition-tth06-transcription.log`.
- `python3 -B scripts/check_stage_composition_transcription.py` passed, all
  four planted drifts; `lean/.validate-logs/stage-composition-transcription.log`.
- `git diff --check` passed. Only TTH-07's evidence, ceiling and rationale
  changed in this registry packet; all frozen statements/statuses unchanged.
