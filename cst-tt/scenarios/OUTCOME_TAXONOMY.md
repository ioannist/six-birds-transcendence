# Typed outcome taxonomy

**Status:** candidate-output vocabulary; no scenario is preclassified.

## 1. Vector rule

A candidate returns one label in each applicable lane (`S-T`, `S-R`, `S-L`, `A`, `R`). A flat verdict such as “successful upload,” “same person,” “mere copy,” or “death” is not permitted. Composite phrases from the governing plan are retained as aliases for typed vectors, not as primitive labels.

| ID | Lane | Canonical label | Neutral meaning | Blocked inference |
|---|---|---|---|---|
| `OT-ST-01` | `S-T` | `no_transport` | The candidate's named transport predicate fails on the scenario. | Does not imply no target package or no lineage under another criterion. |
| `OT-ST-02` | `S-T` | `structural_transport_satisfied` | The named object/invariant satisfies the candidate's typed transport predicate. | Does not imply target realization, lineage, autonomy, recognition, or ontology. |
| `OT-ST-03` | `S-T` | `route_dependent_transport` | Transport verdict or transported structure differs across admissible routes. | Does not say which route is normatively correct. |
| `OT-ST-04` | `S-T` | `transport_underdetermined` | The candidate/instruments do not determine whether the transport predicate holds. | Must state whether the source is criterion ambiguity, missing data, or scenario underspecification. |
| `OT-ST-05` | `S-T` | `not_applicable_same_carrier` | The scenario fails the candidate's distinct-carrier applicability condition. | Does not deny same-support invariance or usefulness as a control. |
| `OT-SR-01` | `S-R` | `no_valid_target_package` | No target episode satisfies the declared target package/gate predicate. | Does not by itself settle lineage of records or partial structures. |
| `OT-SR-02` | `S-R` | `target_package_exists` | At least one target episode satisfies the declared target package/gate predicate. | Does not imply source-target lineage or autonomy. |
| `OT-SR-03` | `S-R` | `public_duplicate_with_hidden_mismatch` | Target matches the declared public/report interface while failing a named hidden, predictive, coherence, or package condition. | Public mismatch is not required; the hidden mismatch must be named. |
| `OT-SR-04` | `S-R` | `empty_target_after_viability_failure` | The target package relation returns empty because a declared viability/maintenance condition fails. | This is structural extinction under a criterion, not an ontological death claim. |
| `OT-SR-05` | `S-R` | `target_package_underdetermined` | Available scenario data do not determine target package satisfaction. | Must distinguish unavailable evidence from an undefined target predicate. |
| `OT-SR-06` | `S-R` | `target_package_not_applicable` | The scenario/candidate has no separately designated target-package question at the declared scope. | Permitted only with an explicit boundary, such as a same-carrier representation control or genuinely joint distributed object. |
| `OT-SL-01` | `S-L` | `no_declared_lineage_reaches_target` | A target package may exist, but the chosen lineage relation has no source-to-target edge. | Does not imply target nonrealization or metaphysical nonidentity. |
| `OT-SL-02` | `S-L` | `structural_successor` | The target is related forward to the source by the declared structural criterion, without a uniqueness/exclusivity claim. | Does not imply one-to-one continuation or personal identity. |
| `OT-SL-03` | `S-L` | `one_to_one_lineage_continuation` | Exactly one target successor is selected within the declared candidate domain and route scope. | Cardinality one does not license personal identity or global uniqueness outside scope. |
| `OT-SL-04` | `S-L` | `branch_valued_continuation` | One source has multiple lineage successors under the declared criterion. | Does not assert one token is literally numerically identical to all branches. |
| `OT-SL-05` | `S-L` | `fusion_valued_continuation` | One target has multiple lineage predecessors under the declared criterion. | Does not imply identity with every predecessor or preservation of conflicting histories. |
| `OT-SL-06` | `S-L` | `package_equivalent_duplicate_with_unresolved_token_identity` | Target tokens are package-equivalent under the declared structure while token/personal identity remains unresolved. | This is an explicit boundary label, not a hidden assertion that copies are new or same persons. |
| `OT-SL-07` | `S-L` | `lineage_underdetermined` | The criterion or available facts do not select a lineage classification. | Must identify symmetry, missing history, route dependence, or another specific source. |
| `OT-SL-08` | `S-L` | `lineage_not_applicable` | The candidate does not define lineage for this scenario class. | Permitted only with an explicit scope limitation, not silent omission. |
| `OT-A-01` | `A` | `bridge_dependent_shadow` | Named target package behavior fails or is undefined when continuing source/bridge/decoder support is withdrawn. | Does not entail that the coupled distributed assembly lacks a package. |
| `OT-A-02` | `A` | `autonomous_target_realization` | A target package exists and remains maintained under the declared withdrawal intervention, environment, disturbance class, and horizon. | Does not imply lineage or consciousness. |
| `OT-A-03` | `A` | `autonomy_failure_after_withdrawal` | A target package exists before withdrawal but fails the declared maintenance condition afterward. | Does not determine whether a shorter horizon would pass. |
| `OT-A-04` | `A` | `autonomy_underdetermined` | The setup or candidate does not determine post-withdrawal maintenance. | Must state missing intervention, horizon, dynamics, or observability. |
| `OT-A-05` | `A` | `autonomy_not_tested` | No autonomy intervention is applicable or supplied for the claim being evaluated. | Cannot be paraphrased as autonomous. |
| `OT-R-01` | `R` | `determinate_under_declared_instruments` | The declared instruments suffice to decide the candidate's structural verdict within stated error bounds. | Does not make the structural predicate true by observation alone. |
| `OT-R-02` | `R` | `indeterminate_under_declared_instruments` | Distinct structural/lineage possibilities remain observationally equivalent under the declared instruments. | Does not imply metaphysical indeterminacy. |
| `OT-R-03` | `R` | `instrument_not_supplied` | The candidate has not supplied a recognition/measurement bridge for this scenario. | Structural analysis may still be possible in a toy with complete-state access. |

## 2. Governing-plan minimum labels and their typing

| Required phrase | Typed representation |
|---|---|
| no valid target package | `OT-SR-01` |
| target package exists but no declared lineage relation reaches it | `OT-SR-02` + `OT-SL-01` |
| structural successor | `OT-SL-02` |
| one-to-one lineage continuation | `OT-SL-03` |
| branch-valued continuation | `OT-SL-04` |
| fusion-valued continuation | `OT-SL-05` |
| public duplicate with hidden mismatch | `OT-SR-03`, plus the candidate's independent lineage/autonomy labels |
| package-equivalent duplicate with unresolved token identity | `OT-SL-06` |
| bridge-dependent shadow | `OT-A-01`, plus a separate target-package label |
| autonomous target realization | `OT-SR-02` + `OT-A-02` |
| indeterminate under the declared instruments | `OT-R-02`, plus structural labels or structural underdetermination as appropriate |
| empty target after viability failure | `OT-SR-04` |

## 3. Underdetermination is typed

Every underdetermined label must identify one or more bases:

- `criterion_underspecified`: the candidate has not defined the relevant relation/predicate;
- `scenario_underspecified`: a scenario parameter needed by the criterion is intentionally left as a variant;
- `symmetry_nonselection`: available structural facts do not break a target symmetry;
- `route_dependence`: admissible routes yield different candidate outputs;
- `instrument_nonidentifiability`: declared observations leave several structural possibilities;
- `assumption_dependence`: different optional assumptions yield different outputs; or
- `out_of_scope`: the candidate explicitly does not cover the scenario class.

`underdetermined` is therefore an informative result only when its basis and scope are named.

## 4. Cardinality and token caution

`one_to_one_lineage_continuation` means cardinality one under a declared criterion, route family, and target domain. It does not mean personal identity. `branch_valued_continuation` and `fusion_valued_continuation` permit relation-valued structure without claiming that one numerical token is many tokens or vice versa.

## 5. Label composition rules

1. Exactly one applicable label is selected per lane; nonapplicable lanes require the explicit nonapplicable/not-tested label.
2. A positive `S-T` label cannot fill `S-R`, `S-L`, or `A`.
3. `OT-SR-02` and `OT-A-02` may coexist without any `S-L` edge.
4. `OT-SL-02/03/04/05` may be returned only by a declared lineage criterion, not by the scenario title.
5. `OT-R-02` reports instrument limits, not metaphysical indeterminacy.
6. No label in this taxonomy licenses an `O` claim. Personal identity or phenomenal realization must be separately stated with assumptions.

## 6. Unfilled template

`ledgers/scenario_verdict_template.csv` contains one unfilled row for every scenario. Future candidates must populate all 35 rows or explicitly mark a lane underdetermined/not applicable with a reason.
