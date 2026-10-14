# Corridor and Direct-Successor Control Suite

The phase lands **41** exact negative controls:

- 25 strict-corridor or composition-interface controls;
- 16 direct-successor controls.

Every control is hash-bound to its model, expected failed obligation, observed failed obligations, and checker function. No control passes its positive predicate.

| ID | Family | Expected failure | Observed failures |
|---|---|---|---|
| COR-C01 | strict-corridor | mixed-support-exact | event-graph-well-formed;every-atomic-leg-valid;mixed-support-exact |
| COR-C02 | strict-corridor | all-stages-temporally-realized | all-stages-temporally-realized |
| COR-C03 | strict-corridor | source-nonredundant | local-temporal-steps-valid;every-atomic-leg-valid;source-nonredundant |
| COR-C04 | strict-corridor | target-nonredundant | local-temporal-steps-valid;every-atomic-leg-valid;target-nonredundant |
| COR-C05 | strict-corridor | starts-source-only | starts-source-only;every-atomic-leg-valid;starts-local-source-only |
| COR-C06 | strict-corridor | ends-target-only | ends-target-only;every-atomic-leg-valid;ends-local-target-only;source-absent-after-takeover |
| COR-C07 | strict-corridor | source-absent-after-takeover | ends-target-only;every-atomic-leg-valid;ends-local-target-only;source-absent-after-takeover |
| COR-C08 | strict-corridor | route-status-valid | every-atomic-leg-valid;route-discipline-valid;route-status-valid;route-memory-valid |
| COR-C09 | strict-corridor | route-memory-valid | every-atomic-leg-valid;route-memory-valid |
| COR-C10 | strict-corridor | bundled-transport-evidence | every-atomic-leg-valid;bundled-transport-evidence |
| COR-C11 | strict-corridor | bundled-transport-evidence | every-atomic-leg-valid;bundled-transport-evidence |
| COR-C12 | strict-corridor | bundled-transport-evidence | every-atomic-leg-valid;bundled-transport-evidence |
| COR-C13 | strict-corridor | local-temporal-steps-valid | local-temporal-steps-valid;every-atomic-leg-valid;counterfactual-arithmetic;source-nonredundant;target-nonredundant |
| COR-C14 | strict-corridor | local-temporal-steps-valid | local-temporal-steps-valid;every-atomic-leg-valid;counterfactual-arithmetic;source-nonredundant;target-nonredundant |
| COR-C15 | strict-corridor | local-temporal-steps-valid | local-temporal-steps-valid;every-atomic-leg-valid;counterfactual-arithmetic;source-nonredundant;target-nonredundant |
| COR-C16 | strict-corridor | intervention-events-valid | every-atomic-leg-valid;intervention-events-valid |
| COR-C17 | strict-corridor | intervention-events-valid | every-atomic-leg-valid;intervention-events-valid |
| COR-C18 | strict-corridor | carrier-chain-valid | distinct-endpoints;carrier-chain-valid;ends-target-only;leg-count-matches-chain;frontier-cover-valid;boundary-signatures-compatible |
| COR-C19 | strict-corridor | frontier-cover-valid | every-atomic-leg-valid;frontier-cover-valid;mixed-support-exact;ends-local-target-only;local-support-scoped;target-present-from-mixed;ownership-interface;intervention-events-valid |
| COR-C20 | strict-corridor | local-support-scoped | every-atomic-leg-valid;mixed-support-exact;local-support-scoped |
| COR-C21 | strict-corridor | stage-indices-contiguous | stage-indices-contiguous;stages-well-formed;support-nonempty-and-unique;ends-target-only;local-temporal-steps-valid;event-graph-well-formed;every-adjacent-stage-operationally-linked;every-atomic-leg-valid;frontier-cover-valid;leg-stages-present;starts-local-source-only;mixed-support-exact;ends-local-target-only;local-support-scoped;target-present-from-mixed;source-absent-after-takeover;ownership-interface;route-memory-valid;counterfactual-arithmetic;source-nonredundant;target-nonredundant |
| COR-C22 | strict-corridor | forbidden-verdict-fields-absent | forbidden-verdict-fields-absent |
| COMP-C01 | composition-interface | frontier-signature-equal | frontier-signature-equal |
| COMP-C02 | composition-interface | shared-frontier-carrier | shared-frontier-carrier;frontier-signature-equal;frontier-support-equal |
| COMP-C03 | composition-interface | frontier-route-memory-equal | frontier-signature-equal;frontier-route-memory-equal |
| DS-C01 | direct-successor | not-replayable-archive | not-replayable-archive |
| DS-C02 | direct-successor | no-storage-mediator | no-storage-mediator |
| DS-C03 | direct-successor | edge-counterfactually-necessary | edge-counterfactually-necessary |
| DS-C04 | direct-successor | no-alternative-temporal-parent | no-alternative-temporal-parent |
| DS-C05 | direct-successor | single-use-temporal-token | single-use-temporal-token |
| DS-C06 | direct-successor | payload-components-complete | payload-components-complete;payload-hashes-match |
| DS-C07 | direct-successor | payload-hashes-match | payload-hashes-match |
| DS-C08 | direct-successor | edge-kind-valid | edge-kind-valid;no-storage-mediator;not-replayable-archive |
| DS-C09 | direct-successor | stage-adjacency | all-stages-temporally-realized;stage-adjacency |
| DS-C10 | direct-successor | predictive-step-valid | predictive-step-valid |
| DS-C11 | direct-successor | tick-step-valid | tick-step-valid |
| DS-C12 | direct-successor | strict-record-step-valid | strict-record-step-valid |
| DS-C13 | direct-successor | ownership-interface-valid | ownership-interface-valid |
| DS-C14 | direct-successor | distinct-carriers | distinct-carriers;target-event-is-first;source-and-target-support-valid;ownership-interface-valid |
| DS-C15 | direct-successor | edge-kind-valid | edge-kind-valid;edge-counterfactually-necessary;no-storage-mediator;not-replayable-archive;no-alternative-temporal-parent;single-use-temporal-token |
| DS-C16 | direct-successor | forbidden-verdict-fields-absent | forbidden-verdict-fields-absent |

The suite specifically tests detached-copy admission, temporal gaps, one-sided redundancy, route collapse, missing transport components, takeover failure, boundary mismatch, arbitrary data reachability, archival replay, absent progress, and verdict-loaded evidence.
