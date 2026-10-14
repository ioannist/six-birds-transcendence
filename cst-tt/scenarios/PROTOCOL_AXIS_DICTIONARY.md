# Protocol-axis dictionary

**Status:** neutral scenario bookkeeping for CST-EXP-02; not a transfer criterion.

Each axis records a stipulated feature of an operational protocol. Axis values are deliberately independent: no value carries a target-package, lineage, autonomy, recognition, or ontological verdict. Composite cases use one primary value plus a `secondary_change_modes` note in the matrix.

## 1. `carrier_relation`

How are source and target supports related at the protocol level?

| Value | Neutral meaning |
|---|---|
| `same_support_reencoding` | One support is retained while representation, coordinates, or packaging changes. |
| `partially_overlapping_support` | Source-side and target-side supports are separately typed but share components or jointly contribute during some interval. |
| `disjoint_support` | Source-side and target-side supports have no shared support component at the declared comparison level. |

**Blocked inference:** Carrier relation does not determine transport, lineage, realization, or ontology.

## 2. `change_mode`

What operational mechanism changes source-side support into target-side support?

| Value | Neutral meaning |
|---|---|
| `gradual_replacement` | Support responsibility changes in multiple ordered stages. |
| `abrupt_translation` | A single or effectively unresolved stage maps a declared source record/package into target form. |
| `checkpoint_restart` | A retained record is used to activate a target after pause, shutdown, or absence. |
| `live_migration` | An active package is maintained while responsibility moves between concurrently operating supports. |
| `destructive_scan` | Source support/package is disabled or made unavailable as part of acquisition/reconstruction. |
| `nondestructive_copy` | A target is constructed while the source remains available for at least one stage. |
| `distributed_extension` | A package is extended across multiple supports without requiring a unique transfer instant. |

**Blocked inference:** Mode names describe engineering order, not continuity verdicts.

## 3. `source_fate`

What happens operationally to source-side package support?

| Value | Neutral meaning |
|---|---|
| `persists` | Source support remains active and available after target activation. |
| `degrades` | Source contribution is progressively reduced or loses declared capability. |
| `paused` | Source dynamics are intentionally suspended while a recoverable record/support remains. |
| `erased_before_activation` | Source package/support is made unavailable before target activation. |
| `erased_after_activation` | Source package/support remains for a period after target activation and is then made unavailable. |
| `remains_coupled` | Source remains an active causal/resource component of the operating source-target assembly. |

**Blocked inference:** Source destruction, persistence, or coupling does not by itself decide lineage.

## 4. `target_timing`

How is target activation temporally related to source activity?

| Value | Neutral meaning |
|---|---|
| `continuous_overlap` | Source and target have an interval of concurrent operation or contribution. |
| `delayed_activation` | Target activates after acquisition/construction, without a stipulated extended dormant gap. |
| `temporal_gap` | No active package is stipulated for a nonzero interval between source cessation/pause and target activation. |
| `time_rescaled_activation` | Target operation is related by an explicit non-unit clock map or time reparameterization. |

**Blocked inference:** Temporal continuity or discontinuity does not define lineage by itself.

## 5. `branching`

What is the cardinality/topology of operational package episodes?

| Value | Neutral meaning |
|---|---|
| `one_to_one` | One designated source episode is connected operationally to one designated target episode. |
| `one_to_many` | One source episode produces or feeds multiple target/live continuation episodes. |
| `many_to_one` | Multiple source/branch episodes contribute to one target episode. |
| `many_to_many` | The protocol contains multiple source-side and target-side episodes or distributed pieces. |

**Blocked inference:** Operational branching is not a lineage graph until a criterion supplies lineage edges.

## 6. `bridge_dependence`

What continuing bridge or protocol support is built into the scenario?

| Value | Neutral meaning |
|---|---|
| `permanent` | The source-target coupling/bridge remains part of the declared operating assembly. |
| `temporary` | The protocol schedules the bridge to end, but target autonomy is not stipulated. |
| `removable` | The setup exposes a well-defined withdrawal intervention; survival after withdrawal is left open. |
| `externally_decoded` | The claimed target-facing structure/readout requires a continuing external decoder or source process. |

**Blocked inference:** A removable bridge is not thereby safely removable; a permanent bridge is not thereby illegitimate.

## 7. `fidelity`

What kind of agreement is stipulated at the scenario's declared transfer granularity?

| Value | Neutral meaning |
|---|---|
| `exact` | Zero declared defect at the named granularity only. |
| `lossy` | Some declared source information/structure is omitted or changed. |
| `error_corrected` | A recovery/repair mechanism is part of the stipulated target construction. |
| `residual_bounded` | A named nonzero defect is bounded, with threshold significance left open. |
| `adaptive` | Agreement is maintained or approached through ongoing adjustment rather than one fixed copy map. |

**Blocked inference:** Exactness at one granularity does not imply exactness of the full package or lineage.

## 8. `reversibility`

Does the protocol expose an inverse at the declared granularity?

| Value | Neutral meaning |
|---|---|
| `reversible` | A declared inverse route recovers the named object exactly within its admissible domain. |
| `approximately_reversible` | A reverse route recovers the named object only up to a declared residual/equivalence. |
| `irreversible` | No admissible inverse is stipulated for the named object. |

**Blocked inference:** Protocol reversibility does not entail token identity or zero route holonomy for unmeasured structures.

## 9. `route_multiplicity`

How many admissible routes connect the declared operational endpoints?

| Value | Neutral meaning |
|---|---|
| `unique_route` | Only one route is admitted at the scenario's declared resolution. |
| `multiple_equivalent_routes` | Several routes are stipulated to agree under a named endpoint comparison, with stronger equivalence left open. |
| `holonomy_bearing_routes` | Closed or alternative routes can restore selected endpoint observables while changing another declared structure. |

**Blocked inference:** One successful route does not establish route independence; endpoint agreement does not erase route history.

## 10. `granularity`

At what level is the scenario's stipulated fidelity/comparison made?

| Value | Neutral meaning |
|---|---|
| `microstate` | Carrier-level state/configuration information. |
| `predictive_state` | Future-sufficient classes, transition structure, or continuation-relevant state. |
| `package_state` | A multi-clause package record or maintained package-level structure. |
| `event_package` | Globally packaged event/role/time/identity structure rather than pairwise local records. |
| `certificate_only` | Only a declared certificate, report, or externally decoded signature is matched. |

**Blocked inference:** Agreement at a coarser granularity cannot be promoted to a finer one without a theorem.

## Independence audit

A well-formed scenario must permit at least the following counter-combinations in principle:

- gradual + branch-valued, gradual + no-lineage, and gradual + underdetermined outcomes;
- destructive + positive, destructive + negative, and destructive + underdetermined outcomes;
- exact + no target package at a finer granularity;
- permanent bridge + valid distributed package, or permanent bridge + bridge-dependent shadow, depending boundary;
- reversible transport + route-sensitive lineage;
- public exactness + predictive mismatch;
- predictive exactness + binding/action-credit mismatch; and
- same-support re-encoding + `not_applicable_same_carrier` for cross-carrier candidates.

If a candidate makes any of these combinations impossible, that restriction must be a visible theorem/definition of the candidate rather than an assumption hidden in the axis vocabulary.
