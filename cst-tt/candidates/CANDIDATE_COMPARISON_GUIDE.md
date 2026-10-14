# Candidate Comparison Guide — No Ranking in CST-EXP-03

The candidate matrix is a map of predicates, scopes, and expected differences. It is not a leaderboard.

## Prohibited uses

- Do not count `structural_transport_satisfied` cells and call the largest count best.
- Do not penalize a narrow schema merely because its S-R lane is not applicable, or reward a broad schema for buying stronger assumptions.
- Do not treat fewer underdetermined cells as greater truth; underdetermination can reflect honest data requirements.
- Do not interpret pairwise divergence counts as scientific distance or evidence weight.

## Legitimate uses

- Identify scenarios on which schemas make different predictions.
- Trace each difference to object choice, bridge morphology, route policy, package scope, or assumptions.
- Select adversarial counterexamples for CST-EXP-04.
- Find candidate pairs that may coincide on a restricted class and therefore suggest comparison theorems.

## Frozen comparison surfaces

`ledgers/candidate_feature_matrix.csv`, `ledgers/candidate_scenario_verdicts.csv`, `ledgers/candidate_divergence_matrix.csv`, and `ledgers/candidate_assumption_matrix.csv`.
