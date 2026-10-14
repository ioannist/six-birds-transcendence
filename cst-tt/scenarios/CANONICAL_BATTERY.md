# Canonical and supplemental thought-experiment battery

**Phase:** CST-EXP-02
**Battery size:** 20 governing-plan scenarios + 15 supplemental stress controls (35 total)
**Rule:** no scenario defines transfer for the others; every later candidate must return a typed verdict vector or explicit underdetermination for all 35.

## 1. Battery index

| ID | Role | Scenario | Carrier relation | Mode | Source fate | Branching | Fidelity / granularity | Primary discriminators | Card |
|---|---|---|---|---|---|---|---|---|---|
| `S01` | `canonical` | Gradual component-by-component replacement | `partially_overlapping_support` | `gradual_replacement` | `degrades` | `one_to_one` | `adaptive` / `package_state` | `D02;D03;D06;D07;D08;D10` | [card](cards/S01.md) |
| `S02` | `canonical` | Instantaneous destructive scan and reconstruction | `disjoint_support` | `destructive_scan` | `erased_before_activation` | `one_to_one` | `exact` / `microstate` | `D01;D02;D03;D08;D09;D10` | [card](cards/S02.md) |
| `S03` | `canonical` | Nondestructive exact copy while source continues | `disjoint_support` | `nondestructive_copy` | `persists` | `one_to_many` | `exact` / `package_state` | `D01;D03;D06;D08;D10` | [card](cards/S03.md) |
| `S04` | `canonical` | Copy first, source deletion later | `disjoint_support` | `nondestructive_copy` | `erased_after_activation` | `one_to_many` | `exact` / `package_state` | `D03;D06;D08;D10` | [card](cards/S04.md) |
| `S05` | `canonical` | Two simultaneous exact targets | `disjoint_support` | `destructive_scan` | `erased_before_activation` | `one_to_many` | `exact` / `package_state` | `D01;D06;D08;D10` | [card](cards/S05.md) |
| `S06` | `canonical` | Target activation after a temporal gap | `disjoint_support` | `checkpoint_restart` | `paused` | `one_to_one` | `exact` / `predictive_state` | `D01;D02;D03;D05;D08;D10` | [card](cards/S06.md) |
| `S07` | `canonical` | Long-lived source-target overlap | `partially_overlapping_support` | `live_migration` | `remains_coupled` | `one_to_one` | `adaptive` / `package_state` | `D02;D03;D05;D06;D08` | [card](cards/S07.md) |
| `S08` | `canonical` | Distributed extension with no sharp handoff | `partially_overlapping_support` | `distributed_extension` | `remains_coupled` | `many_to_many` | `adaptive` / `package_state` | `D03;D04;D05;D06;D08;D10` | [card](cards/S08.md) |
| `S09` | `canonical` | Fission followed by independent divergence | `disjoint_support` | `nondestructive_copy` | `erased_after_activation` | `one_to_many` | `exact` / `package_state` | `D01;D04;D05;D06;D10` | [card](cards/S09.md) |
| `S10` | `canonical` | Fission followed by later fusion | `disjoint_support` | `abrupt_translation` | `erased_after_activation` | `many_to_one` | `adaptive` / `event_package` | `D02;D04;D05;D06;D07;D10` | [card](cards/S10.md) |
| `S11` | `canonical` | Public-perfect copy with predictive mismatch | `disjoint_support` | `nondestructive_copy` | `persists` | `one_to_many` | `lossy` / `predictive_state` | `D01;D02;D08;D09;D10` | [card](cards/S11.md) |
| `S12` | `canonical` | Predictive match with different binding or action-credit structure | `disjoint_support` | `abrupt_translation` | `persists` | `one_to_many` | `lossy` / `predictive_state` | `D01;D04;D06;D08;D10` | [card](cards/S12.md) |
| `S13` | `canonical` | Target maintained only by an external decoder or source process | `disjoint_support` | `distributed_extension` | `remains_coupled` | `one_to_one` | `lossy` / `certificate_only` | `D02;D03;D05;D06;D08` | [card](cards/S13.md) |
| `S14` | `canonical` | Closed route restoring current observables but changing predictive state | `disjoint_support` | `live_migration` | `paused` | `one_to_one` | `lossy` / `predictive_state` | `D01;D02;D03;D07;D09` | [card](cards/S14.md) |
| `S15` | `canonical` | Local pairwise matches without a global package | `partially_overlapping_support` | `distributed_extension` | `remains_coupled` | `many_to_many` | `lossy` / `event_package` | `D02;D03;D04;D06;D07;D08` | [card](cards/S15.md) |
| `S16` | `canonical` | Residual-bounded transfer near a viability boundary | `disjoint_support` | `abrupt_translation` | `degrades` | `one_to_one` | `residual_bounded` / `package_state` | `D02;D05;D08;D09;D10` | [card](cards/S16.md) |
| `S17` | `canonical` | Lossy transfer followed by endogenous repair | `disjoint_support` | `checkpoint_restart` | `erased_before_activation` | `one_to_one` | `error_corrected` / `package_state` | `D02;D04;D05;D06;D08;D09;D10` | [card](cards/S17.md) |
| `S18` | `canonical` | Exact reversible round trip across carriers | `disjoint_support` | `live_migration` | `paused` | `one_to_one` | `exact` / `package_state` | `D02;D03;D07;D08;D09;D10` | [card](cards/S18.md) |
| `S19` | `canonical` | Target with a radically rescaled clock | `disjoint_support` | `live_migration` | `erased_after_activation` | `one_to_one` | `adaptive` / `predictive_state` | `D01;D02;D03;D07;D08;D09` | [card](cards/S19.md) |
| `S20` | `canonical` | Pure representation or gauge change on one carrier | `same_support_reencoding` | `abrupt_translation` | `persists` | `one_to_one` | `exact` / `microstate` | `D02;D03;D07;D09;D10` | [card](cards/S20.md) |
| `S21` | `supplemental` | Checkpoint/restart while the source is paused | `disjoint_support` | `checkpoint_restart` | `paused` | `one_to_many` | `exact` / `predictive_state` | `D01;D02;D03;D05;D08;D10` | [card](cards/S21.md) |
| `S22` | `supplemental` | Live migration under concurrent source updates | `disjoint_support` | `live_migration` | `erased_after_activation` | `one_to_one` | `adaptive` / `event_package` | `D02;D03;D04;D06;D07;D08` | [card](cards/S22.md) |
| `S23` | `supplemental` | Many-source fusion into one target | `disjoint_support` | `abrupt_translation` | `erased_after_activation` | `many_to_one` | `adaptive` / `package_state` | `D01;D04;D05;D06;D07;D10` | [card](cards/S23.md) |
| `S24` | `supplemental` | Many-to-many sharded reconfiguration | `partially_overlapping_support` | `distributed_extension` | `degrades` | `many_to_many` | `error_corrected` / `event_package` | `D02;D03;D04;D05;D08;D10` | [card](cards/S24.md) |
| `S25` | `supplemental` | Adaptive error-corrected migration | `partially_overlapping_support` | `gradual_replacement` | `erased_after_activation` | `one_to_one` | `error_corrected` / `package_state` | `D02;D04;D05;D07;D08;D09` | [card](cards/S25.md) |
| `S26` | `supplemental` | Independently built package-equivalent target | `disjoint_support` | `abrupt_translation` | `persists` | `one_to_many` | `exact` / `package_state` | `D01;D03;D06;D08;D10` | [card](cards/S26.md) |
| `S27` | `supplemental` | Partial replacement around a persistent shared core | `partially_overlapping_support` | `gradual_replacement` | `degrades` | `one_to_one` | `adaptive` / `package_state` | `D02;D03;D05;D06;D08;D10` | [card](cards/S27.md) |
| `S28` | `supplemental` | Bridge removal followed by delayed target collapse | `disjoint_support` | `live_migration` | `erased_after_activation` | `one_to_one` | `residual_bounded` / `package_state` | `D02;D05;D08;D09` | [card](cards/S28.md) |
| `S29` | `supplemental` | External scheduler masquerading as temporal closure | `disjoint_support` | `abrupt_translation` | `remains_coupled` | `one_to_one` | `exact` / `predictive_state` | `D02;D03;D08;D10` | [card](cards/S29.md) |
| `S30` | `supplemental` | Certificate-only migration with package mismatch | `disjoint_support` | `nondestructive_copy` | `persists` | `one_to_many` | `exact` / `certificate_only` | `D01;D04;D08;D09` | [card](cards/S30.md) |
| `S31` | `supplemental` | Event package assembled from locally admissible edges | `disjoint_support` | `abrupt_translation` | `erased_after_activation` | `one_to_one` | `exact` / `event_package` | `D02;D04;D07;D08` | [card](cards/S31.md) |
| `S32` | `supplemental` | Approximately reversible round trip with accumulated residual | `disjoint_support` | `abrupt_translation` | `paused` | `one_to_one` | `residual_bounded` / `predictive_state` | `D01;D05;D07;D08;D09` | [card](cards/S32.md) |
| `S33` | `supplemental` | Dormant backup activated after source erasure | `disjoint_support` | `checkpoint_restart` | `erased_before_activation` | `one_to_many` | `lossy` / `predictive_state` | `D01;D03;D06;D08;D09;D10` | [card](cards/S33.md) |
| `S34` | `supplemental` | Overlap transfer that degrades the source | `partially_overlapping_support` | `live_migration` | `degrades` | `one_to_one` | `adaptive` / `package_state` | `D03;D05;D06;D08;D09` | [card](cards/S34.md) |
| `S35` | `supplemental` | Replacement-order critical pair | `partially_overlapping_support` | `gradual_replacement` | `erased_after_activation` | `one_to_many` | `exact` / `package_state` | `D01;D02;D04;D06;D07;D09;D10` | [card](cards/S35.md) |

## 2. Governing-plan coverage

S01–S20 instantiate, in order: gradual replacement; instantaneous destructive scan/reconstruction; nondestructive exact copy while the source continues; copy followed by later source deletion; two simultaneous exact targets; delayed activation after a temporal gap; long-lived source-target overlap; distributed extension with no sharp handoff; fission followed by independent divergence; fission followed by later fusion; a public/report-perfect but predictively different target; predictive matching with different binding or action-credit structure; target behavior maintained only by an external decoder/source; a route loop that restores public observables while changing predictive state; local pairwise matches that fail to glue globally; residual-bounded transfer near a viability boundary; lossy transfer followed by endogenous repair; an exact reversible round trip; a radically rescaled clock; and a pure representation/gauge change.

## 3. Minimal contrast pairs

The following comparisons isolate one or a small number of protocol changes. They are not claims that only those changes matter. No scenario is paradigmatic, and no candidate verdict is preassigned.

| Contrast | Principal variable isolated |
|---|---|
| S01 vs S02 | staged overlap/order versus abrupt destructive reconstruction |
| S02 vs S06 | ordinary delayed reconstruction versus a nonzero dormant gap |
| S03 vs S04 | source persistence versus later source deletion after coactivity |
| S03 vs S05 | one target plus source versus symmetric multiple targets without source |
| S05 vs S09 | symmetric activation versus later branch divergence |
| S09 vs S10 | persistent fission versus later many-to-one fusion/recombination |
| S07 vs S13 | long overlap with moving responsibility versus continuing external generation/readout |
| S07 vs S08 | eventual target-only handoff versus permanently distributed realization |
| S03 vs S11 | declared package exactness versus public-only exactness with predictive mismatch |
| S11 vs S12 | predictive mismatch versus predictive match with other package mismatch |
| S08 vs S15 | coherent distributed package versus locally accepted records with failed global glue |
| S14 vs S18 | route loop with predictive residue versus exact inverse round trip on named structure |
| S16 vs S17 | defect near viability boundary versus defect followed by target-native repair |
| S06 vs S19 | temporal absence versus continuous dynamics under radical time rescaling |
| S20 vs every cross-carrier case | genuine support change versus pure representation/gauge change |
| S06 vs S21 vs S33 | erased source gap versus paused recoverable source versus stale dormant backup |
| S01 vs S22 vs S35 | staged replacement versus concurrent-update cutover versus route-order critical pair |
| S10 vs S23 | fission-then-fusion versus independent many-source fusion |
| S08 vs S24 | stable distributed extension versus many-to-many repartition |
| S17 vs S25 | endogenous repair after loss versus explicit error-corrected support migration |
| S03 vs S26 | source-derived exact copy versus independently built structural twin |
| S01 vs S27 | complete replacement versus persistent-core partial replacement |
| S13 vs S28 vs S29 | obvious bridge dependence versus delayed collapse versus external temporal scheduler |
| S12 vs S30 | package-clause mismatch versus certificate-only counterfeit |
| S15 vs S31 | generic gluing failure versus event-package pairwise-edge obstruction |
| S18 vs S32 | exact round trip versus approximately reversible accumulated residual |
| S16 vs S34 | target viability boundary versus source-degrading transfer cost |

## 4. Axis coverage

### `carrier_relation`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `same_support_reencoding` | 1 | `S20` |
| `partially_overlapping_support` | 9 | `S01;S07;S08;S15;S24;S25;S27;S34;S35` |
| `disjoint_support` | 25 | `S02;S03;S04;S05;S06;S09;S10;S11;S12;S13;S14;S16;S17;S18;S19;S21;S22;S23;S26;S28;S29;S30;S31;S32;S33` |

### `change_mode`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `gradual_replacement` | 4 | `S01;S25;S27;S35` |
| `abrupt_translation` | 9 | `S10;S12;S16;S20;S23;S26;S29;S31;S32` |
| `checkpoint_restart` | 4 | `S06;S17;S21;S33` |
| `live_migration` | 7 | `S07;S14;S18;S19;S22;S28;S34` |
| `destructive_scan` | 2 | `S02;S05` |
| `nondestructive_copy` | 5 | `S03;S04;S09;S11;S30` |
| `distributed_extension` | 4 | `S08;S13;S15;S24` |

### `source_fate`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `persists` | 6 | `S03;S11;S12;S20;S26;S30` |
| `degrades` | 5 | `S01;S16;S24;S27;S34` |
| `paused` | 5 | `S06;S14;S18;S21;S32` |
| `erased_before_activation` | 4 | `S02;S05;S17;S33` |
| `erased_after_activation` | 10 | `S04;S09;S10;S19;S22;S23;S25;S28;S31;S35` |
| `remains_coupled` | 5 | `S07;S08;S13;S15;S29` |

### `target_timing`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `continuous_overlap` | 19 | `S01;S03;S04;S07;S08;S09;S10;S11;S12;S13;S15;S20;S22;S24;S25;S27;S28;S34;S35` |
| `delayed_activation` | 11 | `S02;S05;S14;S16;S17;S18;S23;S26;S30;S31;S32` |
| `temporal_gap` | 3 | `S06;S21;S33` |
| `time_rescaled_activation` | 2 | `S19;S29` |

### `branching`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `one_to_one` | 19 | `S01;S02;S06;S07;S13;S14;S16;S17;S18;S19;S20;S22;S25;S27;S28;S29;S31;S32;S34` |
| `one_to_many` | 11 | `S03;S04;S05;S09;S11;S12;S21;S26;S30;S33;S35` |
| `many_to_one` | 2 | `S10;S23` |
| `many_to_many` | 3 | `S08;S15;S24` |

### `bridge_dependence`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `permanent` | 1 | `S08` |
| `temporary` | 16 | `S01;S02;S04;S07;S09;S10;S14;S15;S16;S19;S21;S23;S27;S31;S33;S34` |
| `removable` | 16 | `S03;S05;S06;S11;S12;S17;S18;S20;S22;S24;S25;S26;S28;S30;S32;S35` |
| `externally_decoded` | 2 | `S13;S29` |

### `fidelity`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `exact` | 14 | `S02;S03;S04;S05;S06;S09;S18;S20;S21;S26;S29;S30;S31;S35` |
| `lossy` | 6 | `S11;S12;S13;S14;S15;S33` |
| `error_corrected` | 3 | `S17;S24;S25` |
| `residual_bounded` | 3 | `S16;S28;S32` |
| `adaptive` | 9 | `S01;S07;S08;S10;S19;S22;S23;S27;S34` |

### `reversibility`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `reversible` | 5 | `S13;S18;S20;S26;S30` |
| `approximately_reversible` | 15 | `S01;S06;S07;S08;S14;S16;S17;S19;S21;S22;S24;S25;S27;S32;S35` |
| `irreversible` | 15 | `S02;S03;S04;S05;S09;S10;S11;S12;S15;S23;S28;S29;S31;S33;S34` |

### `route_multiplicity`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `unique_route` | 18 | `S02;S03;S04;S06;S09;S11;S12;S13;S16;S17;S19;S21;S26;S28;S29;S30;S33;S34` |
| `multiple_equivalent_routes` | 13 | `S01;S05;S07;S08;S15;S18;S20;S22;S23;S24;S25;S27;S31` |
| `holonomy_bearing_routes` | 4 | `S10;S14;S32;S35` |

### `granularity`

| Value | Scenario count | Scenarios |
|---|---:|---|
| `microstate` | 2 | `S02;S20` |
| `predictive_state` | 9 | `S06;S11;S12;S14;S19;S21;S29;S32;S33` |
| `package_state` | 17 | `S01;S03;S04;S05;S07;S08;S09;S16;S17;S18;S23;S25;S26;S27;S28;S34;S35` |
| `event_package` | 5 | `S10;S15;S22;S24;S31` |
| `certificate_only` | 2 | `S13;S30` |

## 5. What is fixed and what remains open

Each scenario fixes only the operational facts needed to expose a discriminator. The following remain candidate outputs unless explicitly stated as a control fact:

- what object is transported;
- whether a target package exists;
- whether operational edges become lineage edges;
- whether lineage is zero, unique, branch-valued, fusion-valued, route-dependent, or underdetermined;
- whether bridge withdrawal leaves a target-native package;
- which defects matter and which thresholds are stable;
- what declared instruments can identify; and
- every ontological or personal-identity interpretation.

## 6. Candidate completion rule

A candidate has not completed the scenario phase merely by discussing famous cases. It must populate `ledgers/scenario_verdict_template.csv` for every row, cite the criterion used in each lane, and explain every underdetermined/not-applicable result. A candidate that uses one scenario to define its criterion and then treats the remaining cases as verbal exceptions fails the exit gate.
