from __future__ import annotations

import hashlib
import itertools
import json
from dataclasses import dataclass
from typing import Any, Callable, Iterable, Iterator, Mapping

JsonObject = dict[str, Any]


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256((canonical_json(value) + "\n").encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class Candidate:
    model: JsonObject
    size_vector: tuple[int, ...]


@dataclass(frozen=True)
class CheckResult:
    premises: Mapping[str, bool]
    conclusion_failures: Mapping[str, bool]
    derived_facts: Mapping[str, Any]

    @property
    def qualifies(self) -> bool:
        return bool(self.premises) and all(self.premises.values()) and bool(self.conclusion_failures) and all(
            self.conclusion_failures.values()
        )


@dataclass(frozen=True)
class CountermodelSpec:
    countermodel_id: str
    name: str
    target_no_go_id: str
    toy_model_ref: str
    family: str
    claim_lanes: tuple[str, ...]
    scope: str
    size_measure: str
    search_bound: str
    lower_bound_argument: str
    lean_declaration: str
    generator: Callable[[], Iterable[Candidate]]
    checker: Callable[[Mapping[str, Any]], CheckResult]


@dataclass(frozen=True)
class SearchOutcome:
    spec: CountermodelSpec
    witness: Candidate
    check: CheckResult
    candidates_explored: int
    qualifying_candidates: int
    smaller_candidates_explored: int
    same_size_candidates_explored: int
    same_size_qualifying_candidates: int

    @property
    def minimality_status(self) -> str:
        return "proved-by-exhaustive-bounded-search"

    def model_document(self) -> JsonObject:
        return {
            "schema_version": "CST-TT-01-model-v1",
            "countermodel_id": self.spec.countermodel_id,
            "name": self.spec.name,
            "target_no_go_id": self.spec.target_no_go_id,
            "toy_model_ref": self.spec.toy_model_ref,
            "family": self.spec.family,
            "claim_lanes": list(self.spec.claim_lanes),
            "scope": self.spec.scope,
            "claim_ceiling": "structural-boundary-only",
            "size_measure": self.spec.size_measure,
            "size_vector": list(self.witness.size_vector),
            "model": self.witness.model,
            "premise_checks": dict(sorted(self.check.premises.items())),
            "conclusion_failure_checks": dict(sorted(self.check.conclusion_failures.items())),
            "derived_facts": dict(sorted(self.check.derived_facts.items())),
        }

    def certificate_document(self, finite_model_ref: str, finite_model_sha256: str | None = None) -> JsonObject:
        model_doc = self.model_document()
        model_hash = finite_model_sha256 or canonical_sha256(model_doc)
        return {
            "schema_version": "CST-TT-01",
            "countermodel_id": self.spec.countermodel_id,
            "name": self.spec.name,
            "target_no_go_id": self.spec.target_no_go_id,
            "toy_model_ref": self.spec.toy_model_ref,
            "model_family": self.spec.family,
            "finite_model_ref": finite_model_ref,
            "finite_model_sha256": model_hash,
            "claim_lanes": list(self.spec.claim_lanes),
            "scope": self.spec.scope,
            "premises_status": "certified",
            "conclusion_failure_status": "certified",
            "minimality_status": "certified",
            "result_status": "checked-finite-countermodel",
            "claim_ceiling": "structural-boundary-only",
            "search": {
                "algorithm": "deterministic-exhaustive-enumeration",
                "ordering": "lexicographic(size_vector, canonical_json(model))",
                "bound": self.spec.search_bound,
                "size_measure": self.spec.size_measure,
                "witness_size_vector": list(self.witness.size_vector),
                "candidates_explored": self.candidates_explored,
                "qualifying_candidates": self.qualifying_candidates,
                "smaller_candidates_explored": self.smaller_candidates_explored,
                "same_size_candidates_explored": self.same_size_candidates_explored,
                "same_size_qualifying_candidates": self.same_size_qualifying_candidates,
                "minimality_result": self.minimality_status,
                "lower_bound_argument": self.spec.lower_bound_argument,
            },
            "checker": {
                "python_checker": f"cst_tt.countermodels:{self.spec.countermodel_id}",
                "python_status": "passed",
                "lean_declaration": self.spec.lean_declaration,
                "lean_source_status": "explicit-proof-source-present",
                "lean_compile_status": "pending-toolchain",
            },
        }


def exhaustive_search(spec: CountermodelSpec) -> SearchOutcome:
    candidates = sorted(spec.generator(), key=lambda candidate: (candidate.size_vector, canonical_json(candidate.model)))
    if not candidates:
        raise ValueError(f"{spec.countermodel_id}: empty candidate generator")
    checked = [(candidate, spec.checker(candidate.model)) for candidate in candidates]
    qualifying = [(candidate, result) for candidate, result in checked if result.qualifies]
    if not qualifying:
        raise ValueError(f"{spec.countermodel_id}: no qualifying countermodel inside declared bound")
    minimal_size = min(candidate.size_vector for candidate, _ in qualifying)
    minimal = [(candidate, result) for candidate, result in qualifying if candidate.size_vector == minimal_size]
    witness, result = min(minimal, key=lambda item: canonical_json(item[0].model))
    smaller = [candidate for candidate, _ in checked if candidate.size_vector < minimal_size]
    same_size = [candidate for candidate, _ in checked if candidate.size_vector == minimal_size]
    return SearchOutcome(
        spec=spec,
        witness=witness,
        check=result,
        candidates_explored=len(checked),
        qualifying_candidates=len(qualifying),
        smaller_candidates_explored=len(smaller),
        same_size_candidates_explored=len(same_size),
        same_size_qualifying_candidates=len(minimal),
    )


def _binary_vectors(length: int) -> Iterator[tuple[int, ...]]:
    yield from itertools.product((0, 1), repeat=length)


def _all_functions(domain_size: int, codomain_size: int) -> Iterator[tuple[int, ...]]:
    yield from itertools.product(range(codomain_size), repeat=domain_size)


def _powerset(items: tuple[tuple[int, int], ...]) -> Iterator[tuple[tuple[int, int], ...]]:
    for mask in range(1 << len(items)):
        yield tuple(items[index] for index in range(len(items)) if mask & (1 << index))


# CM-01 — endpoint equality without temporal lineage.
def _gen_cm01() -> Iterable[Candidate]:
    for carrier_count in range(1, 3):
        for endpoint_equal, signature_equal, operational_link in itertools.product((False, True), repeat=3):
            model = {
                "carrier_count": carrier_count,
                "source_target_distinct": carrier_count >= 2,
                "endpoint_equal": endpoint_equal,
                "temporal_signature_equal": signature_equal,
                "operational_dependency_present": operational_link,
                "strict_temporal_lineage": operational_link and carrier_count >= 2,
            }
            yield Candidate(model, (carrier_count, int(operational_link)))


def _check_cm01(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={
            "distinct_carriers": bool(model["source_target_distinct"]),
            "endpoint_snapshot_equal": bool(model["endpoint_equal"]),
            "temporal_signature_equal": bool(model["temporal_signature_equal"]),
        },
        conclusion_failures={"strict_temporal_lineage_absent": not bool(model["strict_temporal_lineage"])},
        derived_facts={"endpoint_equality_is_not_an_episode_relation": not bool(model["operational_dependency_present"])},
    )


# CM-02 — detached exact copy with package-like and autonomy-like endpoint properties.
def _gen_cm02() -> Iterable[Candidate]:
    for carrier_count in range(1, 3):
        for stage_count in range(1, 4):
            for copy_edges in range(0, 2):
                for mixed_stage_count in range(0, 2):
                    for exact_copy, package_pass, autonomous in itertools.product((False, True), repeat=3):
                        strict_corridor = (
                            carrier_count >= 2
                            and stage_count >= 3
                            and mixed_stage_count >= 1
                            and copy_edges >= 1
                        )
                        model = {
                            "carrier_count": carrier_count,
                            "stage_count": stage_count,
                            "copy_edges": copy_edges,
                            "mixed_stage_count": mixed_stage_count,
                            "source_target_distinct": carrier_count >= 2,
                            "source_and_target_endpoints_declared": stage_count >= 2,
                            "source_derived": copy_edges >= 1,
                            "exact_temporal_copy": exact_copy,
                            "target_package_pass": package_pass,
                            "target_post_copy_autonomous": autonomous,
                            "strict_overlap_corridor": strict_corridor,
                            "support_pattern": ["source", "target"] if stage_count == 2 else [],
                        }
                        yield Candidate(model, (carrier_count, stage_count, copy_edges, mixed_stage_count))


def _check_cm02(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={
            "distinct_carriers": bool(model["source_target_distinct"]),
            "source_and_target_endpoints_declared": bool(model["source_and_target_endpoints_declared"]),
            "source_derived_copy": bool(model["source_derived"]),
            "exact_temporal_endpoint_match": bool(model["exact_temporal_copy"]),
            "target_package_pass": bool(model["target_package_pass"]),
            "target_autonomous_after_copy": bool(model["target_post_copy_autonomous"]),
        },
        conclusion_failures={"strict_overlap_corridor_absent": not bool(model["strict_overlap_corridor"])},
        derived_facts={
            "detached": int(model["mixed_stage_count"]) == 0,
            "kill_criterion_K_FIACH_04_not_triggered": not bool(model["strict_overlap_corridor"]),
        },
    )


# CM-03 — first noncommuting pair of reversible finite permutations; no endogenous arrow.
def _compose(left: tuple[int, ...], right: tuple[int, ...], value: int) -> int:
    return left[right[value]]


def _gen_cm03() -> Iterable[Candidate]:
    for state_count in range(1, 4):
        perms = tuple(itertools.permutations(range(state_count)))
        for route_a in perms:
            for route_b in perms:
                differing = [
                    state
                    for state in range(state_count)
                    if _compose(route_a, route_b, state) != _compose(route_b, route_a, state)
                ]
                model = {
                    "state_count": state_count,
                    "route_a": list(route_a),
                    "route_b": list(route_b),
                    "witness_states": differing,
                    "routes_reversible": True,
                    "nonzero_holonomy": bool(differing),
                    "record_update": "constant",
                    "endogenous_arrow": False,
                }
                yield Candidate(model, (state_count,))


def _check_cm03(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={
            "route_updates_reversible": bool(model["routes_reversible"]),
            "nonzero_route_holonomy": bool(model["nonzero_holonomy"]),
        },
        conclusion_failures={"endogenous_arrow_absent": not bool(model["endogenous_arrow"])},
        derived_facts={
            "first_disagreement_state": model["witness_states"][0] if model["witness_states"] else None,
            "record_is_constant": model["record_update"] == "constant",
        },
    )


# CM-04 — externally driven temporal shadow that stalls after support withdrawal.
def _gen_cm04() -> Iterable[Candidate]:
    for state_count in range(1, 4):
        for with_support in _all_functions(state_count, state_count):
            for without_support in _all_functions(state_count, state_count):
                progress_states = [state for state in range(state_count) if with_support[state] != state]
                no_support_stalls = all(without_support[state] == state for state in range(state_count))
                model = {
                    "state_count": state_count,
                    "with_external_scheduler": list(with_support),
                    "after_scheduler_withdrawal": list(without_support),
                    "supported_progress_states": progress_states,
                    "runtime_temporal_match": bool(progress_states),
                    "support_is_essential": bool(progress_states) and no_support_stalls,
                    "post_withdrawal_progress": any(without_support[state] != state for state in range(state_count)),
                    "post_withdrawal_autonomous": any(without_support[state] != state for state in range(state_count)),
                }
                yield Candidate(model, (state_count,))


def _check_cm04(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={
            "runtime_match_while_supported": bool(model["runtime_temporal_match"]),
            "external_support_is_essential": bool(model["support_is_essential"]),
        },
        conclusion_failures={
            "post_withdrawal_progress_fails": not bool(model["post_withdrawal_progress"]),
            "autonomy_fails": not bool(model["post_withdrawal_autonomous"]),
        },
        derived_facts={"collapse_mode": "global-stall-after-withdrawal"},
    )


# CM-05 — a stable one-state clock that never progresses.
def _gen_cm05() -> Iterable[Candidate]:
    for state_count in range(1, 3):
        for phase_count in range(1, 3):
            for transition in _all_functions(state_count, state_count):
                phase = tuple(state % phase_count for state in range(state_count))
                stable = all(phase[transition[state]] == phase[state] for state in range(state_count))
                progress = any(transition[state] != state or phase[transition[state]] != phase[state] for state in range(state_count))
                model = {
                    "state_count": state_count,
                    "phase_count": phase_count,
                    "transition": list(transition),
                    "phase": list(phase),
                    "tick_viable": True,
                    "phase_stable": stable,
                    "genuine_progress": progress,
                }
                yield Candidate(model, (state_count, phase_count))


def _check_cm05(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={"tick_viable": bool(model["tick_viable"]), "phase_stable": bool(model["phase_stable"])},
        conclusion_failures={"genuine_progress_absent": not bool(model["genuine_progress"])},
        derived_facts={"stability_is_stasis": model["transition"] == list(range(int(model["state_count"])))},
    )


# CM-06 — same present observation, different continuation signatures; route memory repairs the collision.
def _gen_cm06() -> Iterable[Candidate]:
    for hidden_state_count in range(1, 4):
        for current_symbol_count in range(1, 3):
            for current_observation in _all_functions(hidden_state_count, current_symbol_count):
                for probe_output in _all_functions(hidden_state_count, 2):
                    witness_pairs = [
                        (left, right)
                        for left in range(hidden_state_count)
                        for right in range(left + 1, hidden_state_count)
                        if current_observation[left] == current_observation[right]
                        and probe_output[left] != probe_output[right]
                    ]
                    model = {
                        "hidden_state_count": hidden_state_count,
                        "current_symbol_count": current_symbol_count,
                        "current_observation": list(current_observation),
                        "continuation_probe_output": list(probe_output),
                        "witness_pairs": [list(pair) for pair in witness_pairs],
                        "route_memory": list(range(hidden_state_count)),
                        "current_equal_predictive_mismatch": bool(witness_pairs),
                        "flat": False,
                        "memory_retained_in_unaugmented_state": False,
                        "memory_repair_separates_witness": bool(witness_pairs),
                    }
                    yield Candidate(model, (hidden_state_count, current_symbol_count))


def _check_cm06(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={"current_classes_collide": bool(model["current_equal_predictive_mismatch"])},
        conclusion_failures={
            "predictive_equality_fails": bool(model["current_equal_predictive_mismatch"]),
            "unaugmented_state_has_neither_memory_nor_flatness": not bool(model["flat"])
            and not bool(model["memory_retained_in_unaugmented_state"]),
        },
        derived_facts={
            "repair_available_by_route_memory": bool(model["memory_repair_separates_witness"]),
            "witness_pair": model["witness_pairs"][0] if model["witness_pairs"] else None,
        },
    )


# CM-07 — one nonzero clock-translation loop obstructs a global potential.
def _gen_cm07() -> Iterable[Candidate]:
    for node_count in range(1, 3):
        for modulus in range(1, 5):
            for loop_delta in range(modulus):
                model = {
                    "node_count": node_count,
                    "clock_modulus": modulus,
                    "loop_source": 0,
                    "loop_target": 0,
                    "loop_translation": loop_delta,
                    "same_boundary_routes": True,
                    "nonzero_translation_holonomy": loop_delta % modulus != 0,
                    "global_time_potential_exists": loop_delta % modulus == 0,
                    "local_now_identity_route": 0,
                    "local_now_loop_route": loop_delta % modulus,
                }
                yield Candidate(model, (node_count, modulus))


def _check_cm07(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={
            "same_route_boundary": bool(model["same_boundary_routes"]),
            "nonzero_translation_holonomy": bool(model["nonzero_translation_holonomy"]),
        },
        conclusion_failures={
            "global_time_potential_absent": not bool(model["global_time_potential_exists"]),
            "route_independent_now_absent": model["local_now_identity_route"] != model["local_now_loop_route"],
        },
        derived_facts={"cycle_sum_modulus": model["loop_translation"]},
    )


# CM-08 — locally valid single-coordinate clauses with incompatible overlap values.
def _gen_cm08() -> Iterable[Candidate]:
    for clause_count in range(1, 4):
        for coordinate_count in range(1, 3):
            for value_count in range(1, 3):
                for assignments in itertools.product(range(value_count), repeat=clause_count):
                    all_local = True
                    global_witness = len(set(assignments)) == 1
                    model = {
                        "clause_count": clause_count,
                        "coordinate_count": coordinate_count,
                        "value_count": value_count,
                        "shared_coordinate": 0,
                        "local_assignments_on_shared_coordinate": list(assignments),
                        "all_local_clauses_accept": all_local,
                        "overlap_compatible": global_witness,
                        "global_package_witness_exists": global_witness,
                    }
                    yield Candidate(model, (clause_count, coordinate_count, value_count))


def _check_cm08(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={"every_local_clause_accepts": bool(model["all_local_clauses_accept"])},
        conclusion_failures={
            "overlap_compatibility_fails": not bool(model["overlap_compatible"]),
            "global_witness_absent": not bool(model["global_package_witness_exists"]),
        },
        derived_facts={
            "conflicting_values": sorted(set(model["local_assignments_on_shared_coordinate"])),
            "obstruction_coordinate": model["shared_coordinate"],
        },
    )


# CM-09 — public collision with different hidden package/predictive fact.
def _gen_cm09() -> Iterable[Candidate]:
    for state_count in range(1, 4):
        for public_symbol_count in range(1, 3):
            for observation in _all_functions(state_count, public_symbol_count):
                for hidden in _binary_vectors(state_count):
                    witness_pairs = [
                        (left, right)
                        for left in range(state_count)
                        for right in range(left + 1, state_count)
                        if observation[left] == observation[right] and hidden[left] != hidden[right]
                    ]
                    model = {
                        "state_count": state_count,
                        "public_symbol_count": public_symbol_count,
                        "public_observation": list(observation),
                        "hidden_structural_fact": list(hidden),
                        "witness_pairs": [list(pair) for pair in witness_pairs],
                        "public_collision_hidden_mismatch": bool(witness_pairs),
                    }
                    yield Candidate(model, (state_count, public_symbol_count))


def _check_cm09(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={"public_or_report_collision": bool(model["public_collision_hidden_mismatch"])},
        conclusion_failures={"hidden_structural_identifiability_fails": bool(model["public_collision_hidden_mismatch"])},
        derived_facts={"witness_pair": model["witness_pairs"][0] if model["witness_pairs"] else None},
    )


# CM-10 — a fixed one-tenth scalar threshold can pass while one binary hard gate fails.
def _gen_cm10() -> Iterable[Candidate]:
    for component_count in range(1, 11):
        for defects in _binary_vectors(component_count):
            defect_sum = sum(defects)
            model = {
                "component_count": component_count,
                "defect_vector": list(defects),
                "defect_sum": defect_sum,
                "threshold_numerator": 1,
                "threshold_denominator": 10,
                "small_residual_test": f"10*{defect_sum} <= {component_count}",
                "small_aggregate_residual": 10 * defect_sum <= component_count,
                "every_hard_gate_passes": defect_sum == 0,
                "failed_gate_indices": [index for index, value in enumerate(defects) if value],
            }
            yield Candidate(model, (component_count, defect_sum))


def _check_cm10(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={"aggregate_residual_at_most_one_tenth": bool(model["small_aggregate_residual"])},
        conclusion_failures={"at_least_one_hard_gate_fails": not bool(model["every_hard_gate_passes"])},
        derived_facts={
            "first_failed_gate": model["failed_gate_indices"][0] if model["failed_gate_indices"] else None,
            "exact_residual_fraction": [model["defect_sum"], model["component_count"]],
        },
    )


# CM-11 — a fixed-point-free symmetric fork has no symmetry-invariant singleton selector.
def _gen_cm11() -> Iterable[Candidate]:
    for target_count in range(1, 5):
        for swap in itertools.permutations(range(target_count)):
            involution = all(swap[swap[index]] == index for index in range(target_count))
            fixed_points = [index for index in range(target_count) if swap[index] == index]
            model = {
                "target_count": target_count,
                "swap": list(swap),
                "swap_is_involution": involution,
                "valid_targets": list(range(target_count)),
                "fixed_points": fixed_points,
                "symmetric_valid_fork": involution and target_count >= 2 and not fixed_points,
                "invariant_singleton_selector_exists": bool(fixed_points),
            }
            yield Candidate(model, (target_count,))


def _check_cm11(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={"exact_fixed_point_free_symmetry": bool(model["symmetric_valid_fork"])},
        conclusion_failures={
            "no_symmetry_invariant_unique_selector": not bool(model["invariant_singleton_selector_exists"])
        },
        derived_facts={"relation_valued_branch_count": model["target_count"]},
    )


# CM-12 — equivalent endpoints separated by a stage with no temporal realization.
def _gen_cm12() -> Iterable[Candidate]:
    for stage_count in range(1, 5):
        for temporal_realized in _binary_vectors(stage_count):
            endpoint_equivalent = stage_count >= 2 and temporal_realized[0] == temporal_realized[-1] == 1
            internal_gap = stage_count >= 3 and any(value == 0 for value in temporal_realized[1:-1])
            model = {
                "stage_count": stage_count,
                "temporal_realized_by_stage": list(temporal_realized),
                "endpoint_temporal_signatures_equal": endpoint_equivalent,
                "internal_temporal_gap": internal_gap,
                "strict_no_gap_corridor": all(temporal_realized) and stage_count >= 3,
            }
            yield Candidate(model, (stage_count,))


def _check_cm12(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={
            "equivalent_realized_endpoints": bool(model["endpoint_temporal_signatures_equal"]),
            "explicit_internal_gap": bool(model["internal_temporal_gap"]),
        },
        conclusion_failures={"strict_no_gap_corridor_absent": not bool(model["strict_no_gap_corridor"])},
        derived_facts={
            "classification": "resumed-equivalent-stream-not-strict-corridor",
            "gap_indices": [
                index for index, value in enumerate(model["temporal_realized_by_stage"]) if value == 0
            ],
        },
    )


# CM-13 — finite live prefix in a deterministic countdown, followed by inevitable failure.
def _gen_cm13() -> Iterable[Candidate]:
    for maximum_budget in range(0, 5):
        for horizon in range(1, 4):
            trace = [max(maximum_budget - step, 0) for step in range(maximum_budget + 2)]
            finite_success = all(max(maximum_budget - step, 0) > 0 for step in range(horizon + 1))
            eventual_failure = any(value == 0 for value in trace)
            model = {
                "maximum_budget": maximum_budget,
                "state_count": maximum_budget + 1,
                "claimed_finite_horizon": horizon,
                "trace": trace,
                "live_predicate": "budget>0",
                "finite_horizon_success": finite_success,
                "eventual_failure_reached": eventual_failure,
                "unbounded_liveness": False if eventual_failure else True,
            }
            yield Candidate(model, (maximum_budget + 1, horizon))


def _check_cm13(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={"nontrivial_finite_trace_succeeds": bool(model["finite_horizon_success"])},
        conclusion_failures={"unbounded_liveness_fails": not bool(model["unbounded_liveness"])},
        derived_facts={
            "first_failure_step": next(
                (index for index, value in enumerate(model["trace"]) if value == 0), None
            )
        },
    )


# CM-14 — nonidentity re-encoding inside one fixed carrier.
def _gen_cm14() -> Iterable[Candidate]:
    for carrier_count in range(1, 3):
        for representation_count in range(1, 4):
            for reencoding in itertools.permutations(range(representation_count)):
                nonidentity = any(reencoding[index] != index for index in range(representation_count))
                model = {
                    "carrier_count": carrier_count,
                    "representation_count": representation_count,
                    "reencoding_map": list(reencoding),
                    "same_carrier": carrier_count == 1,
                    "nontrivial_reencoding": nonidentity,
                    "distinct_carrier_transport": carrier_count >= 2,
                }
                yield Candidate(model, (carrier_count, representation_count))


def _check_cm14(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={
            "single_fixed_carrier": bool(model["same_carrier"]),
            "nontrivial_representation_change": bool(model["nontrivial_reencoding"]),
        },
        conclusion_failures={"cross_carrier_typing_fails": not bool(model["distinct_carrier_transport"])},
        derived_facts={"classification": "same-carrier-reencoding-control"},
    )


# CM-15 — same branch marginals, different joint recombination relation.
def _marginals(relation: tuple[tuple[int, int], ...]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    return tuple(sorted({left for left, _ in relation})), tuple(sorted({right for _, right in relation}))


def _gen_cm15() -> Iterable[Candidate]:
    for alphabet_size in range(1, 3):
        product_points = tuple(itertools.product(range(alphabet_size), repeat=2))
        relations = tuple(_powerset(product_points))
        for source_relation in relations:
            for target_relation in relations:
                source_marginals = _marginals(source_relation)
                target_marginals = _marginals(target_relation)
                model = {
                    "alphabet_size": alphabet_size,
                    "source_relation": [list(pair) for pair in source_relation],
                    "target_relation": [list(pair) for pair in target_relation],
                    "source_marginals": [list(source_marginals[0]), list(source_marginals[1])],
                    "target_marginals": [list(target_marginals[0]), list(target_marginals[1])],
                    "every_branch_marginal_preserved": source_marginals == target_marginals,
                    "joint_recombination_preserved": source_relation == target_relation,
                }
                support_size = max(len(source_relation), len(target_relation))
                yield Candidate(model, (alphabet_size, support_size))


def _check_cm15(model: Mapping[str, Any]) -> CheckResult:
    return CheckResult(
        premises={"both_branch_marginals_preserved": bool(model["every_branch_marginal_preserved"])},
        conclusion_failures={"joint_recombination_differs": not bool(model["joint_recombination_preserved"])},
        derived_facts={
            "source_joint_support_size": len(model["source_relation"]),
            "target_joint_support_size": len(model["target_relation"]),
        },
    )


SPECS: tuple[CountermodelSpec, ...] = (
    CountermodelSpec(
        "CM-01",
        "Endpoint snapshot equality without temporal lineage",
        "TTN-01",
        "TTM-02",
        "endpoint-projection",
        ("S-L",),
        "Endpoint/signature equality is insufficient for the strict episode relation.",
        "(carrier_count, operational_link_count)",
        "carrier_count<=2; all three Boolean endpoint/link flags",
        "One carrier cannot instantiate a distinct source/target pair; two carriers suffice.",
        "CSTTT.Countermodels.cm01_endpointSnapshotEqualityWithoutLineage",
        _gen_cm01,
        _check_cm01,
    ),
    CountermodelSpec(
        "CM-02",
        "Detached exact temporal copy",
        "TTN-01",
        "TTM-02",
        "detached-copy",
        ("S-R", "S-L", "A"),
        "Exact endpoint, package-like, and autonomy-like success do not imply a strict overlap corridor.",
        "(carrier_count, stage_count, copy_edge_count, mixed_stage_count)",
        "carrier_count<=2; stage_count<=3; one copy edge; one possible mixed stage; all endpoint flags",
        "Distinct transport needs two carriers; source derivation needs one copy edge; a detached model has zero mixed stages.",
        "CSTTT.Countermodels.cm02_detachedExactTemporalCopy",
        _gen_cm02,
        _check_cm02,
    ),
    CountermodelSpec(
        "CM-03",
        "Holonomy without endogenous arrow",
        "TTN-03",
        "TTM-16",
        "reversible-permutation-holonomy",
        ("S-T", "S-R"),
        "Noncommuting reversible route updates do not supply an endogenous record arrow.",
        "(state_count)",
        "all ordered permutation pairs on 1..3 states",
        "Permutation groups on one and two points are abelian; three points are the first possible noncommuting case.",
        "CSTTT.Countermodels.cm03_holonomyWithoutArrow",
        _gen_cm03,
        _check_cm03,
    ),
    CountermodelSpec(
        "CM-04",
        "Externally scheduled temporal shadow",
        "TTN-06",
        "TTM-04",
        "external-support-shadow",
        ("A", "S-R"),
        "Runtime temporal progress maintained by an essential scheduler collapses after withdrawal.",
        "(state_count)",
        "all deterministic supported/withdrawn transition tables on 1..3 states",
        "One state cannot exhibit nontrivial progress; two states suffice for supported motion and withdrawn stasis.",
        "CSTTT.Countermodels.cm04_externalSchedulerShadow",
        _gen_cm04,
        _check_cm04,
    ),
    CountermodelSpec(
        "CM-05",
        "Stable tick phase without genuine progress",
        "TTN-07",
        "TTM-14",
        "stalled-clock",
        ("S-R",),
        "Tick viability and phase stability do not imply temporal progress.",
        "(state_count, phase_count)",
        "all transition tables on <=2 states and <=2 phases",
        "A one-state, one-phase self-loop is the smallest stable system and already lacks progress.",
        "CSTTT.Countermodels.cm05_stableTickWithoutProgress",
        _gen_cm05,
        _check_cm05,
    ),
    CountermodelSpec(
        "CM-06",
        "Current-equal but predictively different routes",
        "TTN-04",
        "TTM-17",
        "predictive-memory-collision",
        ("S-T",),
        "A present quotient can collide while a continuation probe separates routes; route memory repairs the collision.",
        "(hidden_state_count, current_symbol_count)",
        "all current-observation and binary continuation-output maps on <=3 hidden states and <=2 public symbols",
        "At least two hidden states are required for a collision with different futures; one current symbol suffices.",
        "CSTTT.Countermodels.cm06_currentEqualPredictivelyDifferent",
        _gen_cm06,
        _check_cm06,
    ),
    CountermodelSpec(
        "CM-07",
        "Nonzero clock-translation holonomy",
        "TTN-05",
        "TTM-05",
        "clock-translation-loop",
        ("S-T",),
        "A nonzero cycle translation obstructs one route-independent global now.",
        "(node_count, clock_modulus)",
        "one or two nodes; cyclic clocks of modulus 1..4; all loop translations",
        "Modulus one has no nonzero translation; one node with a modulus-two loop is the smallest obstruction.",
        "CSTTT.Countermodels.cm07_noCanonicalGlobalNow",
        _gen_cm07,
        _check_cm07,
    ),
    CountermodelSpec(
        "CM-08",
        "Local clause success without a global package witness",
        "TTN-08",
        "TTM-11",
        "local-global-gluing-obstruction",
        ("S-R",),
        "Individually accepted local witnesses can disagree on a shared coordinate.",
        "(clause_count, coordinate_count, value_count)",
        "1..3 clauses, 1..2 coordinates, 1..2 values, all shared-coordinate assignments",
        "One clause always glues; two clauses and two values are the first possible overlap disagreement.",
        "CSTTT.Countermodels.cm08_localGlobalObstruction",
        _gen_cm08,
        _check_cm08,
    ),
    CountermodelSpec(
        "CM-09",
        "Public/report-perfect collision with hidden mismatch",
        "TTN-02",
        "TTM-12",
        "public-shadow-collision",
        ("S-R", "S-L", "R"),
        "The same finite public report can be emitted by states with different hidden structural facts.",
        "(state_count, public_symbol_count)",
        "all observation maps and hidden Boolean facts on <=3 states and <=2 public symbols",
        "Two internal states are necessary for a collision with opposite hidden facts; one public symbol suffices.",
        "CSTTT.Countermodels.cm09_publicShadowCollision",
        _gen_cm09,
        _check_cm09,
    ),
    CountermodelSpec(
        "CM-10",
        "Small scalar residual hiding a failed hard gate",
        "TTN-10",
        "TTM-13",
        "scalar-residual",
        ("S-R", "A"),
        "A mean binary defect at or below one tenth can coexist with a nonnegotiable failed gate.",
        "(component_count, failed_gate_count)",
        "all binary defect vectors of length 1..10",
        "At a fixed one-tenth threshold, one failed binary gate needs at least ten components: 1/n <= 1/10 first holds at n=10.",
        "CSTTT.Countermodels.cm10_scalarResidualHardGateFailure",
        _gen_cm10,
        _check_cm10,
    ),
    CountermodelSpec(
        "CM-11",
        "Exact symmetric fork without an invariant unique selector",
        "TTN-11",
        "TTM-07",
        "symmetric-fork",
        ("S-L", "O"),
        "A fixed-point-free target-swap symmetry supports relation-valued branches but no invariant singleton choice.",
        "(target_count)",
        "all permutations on 1..4 targets",
        "A fixed-point-free symmetry needs at least two targets; the two-cycle is minimal.",
        "CSTTT.Countermodels.cm11_symmetryNoUniqueSelector",
        _gen_cm11,
        _check_cm11,
    ),
    CountermodelSpec(
        "CM-12",
        "Temporal gap followed by an equivalent resumed stream",
        "TTN-09",
        "TTM-08",
        "gap-resume",
        ("S-L",),
        "Equivalent realized endpoints do not satisfy the strict no-gap temporal corridor when an internal stage is unrealized.",
        "(stage_count)",
        "all temporal-realization bit traces of length 1..4",
        "A source endpoint, an internal gap, and a target endpoint require at least three stages.",
        "CSTTT.Countermodels.cm12_gapResume",
        _gen_cm12,
        _check_cm12,
    ),
    CountermodelSpec(
        "CM-13",
        "Finite successful trace without indefinite liveness",
        "TTN-12",
        "TTM-10",
        "budget-countdown",
        ("A",),
        "A deterministic system can satisfy a nontrivial finite live prefix and still inevitably exhaust its budget.",
        "(state_count, claimed_horizon)",
        "countdown budgets 0..4 and horizons 1..3",
        "A one-transition live prefix followed by failure requires budgets 2->1->0, hence three states.",
        "CSTTT.Countermodels.cm13_finiteTraceNotUnbounded",
        _gen_cm13,
        _check_cm13,
    ),
    CountermodelSpec(
        "CM-14",
        "Same-carrier re-encoding control",
        "TTN-13",
        "TTM-15",
        "same-carrier-reencoding",
        ("S-T",),
        "A nonidentity representation map on one fixed carrier is not a distinct-carrier transport instance.",
        "(carrier_count, representation_count)",
        "one or two carriers; one to three representations; all representation permutations",
        "A nonidentity re-encoding needs two representations, while the negative control fixes one carrier.",
        "CSTTT.Countermodels.cm14_sameCarrierReencoding",
        _gen_cm14,
        _check_cm14,
    ),
    CountermodelSpec(
        "CM-15",
        "Branchwise preservation without recombination preservation",
        "TTN-14",
        "TFM-04",
        "recombination-marginal-collision",
        ("S-R", "S-L"),
        "Two joint relations can have identical branch marginals while differing in their recombination structure.",
        "(alphabet_size, maximum_joint_support_size)",
        "all pairs of binary relations over alphabets of size 1..2",
        "A one-symbol alphabet or singleton support is determined by its marginals; two binary support points are minimal.",
        "CSTTT.Countermodels.cm15_branchwiseRecombinationFailure",
        _gen_cm15,
        _check_cm15,
    ),
)

SPEC_BY_ID: dict[str, CountermodelSpec] = {spec.countermodel_id: spec for spec in SPECS}


def enumerate_all() -> tuple[SearchOutcome, ...]:
    return tuple(exhaustive_search(spec) for spec in SPECS)


def recheck(countermodel_id: str, model: Mapping[str, Any]) -> CheckResult:
    return SPEC_BY_ID[countermodel_id].checker(model)
