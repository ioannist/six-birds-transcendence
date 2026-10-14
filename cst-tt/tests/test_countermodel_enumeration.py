from __future__ import annotations

from cst_tt.countermodels import enumerate_all, recheck

EXPECTED_SIZES = {
    "CM-01": (2, 0),
    "CM-02": (2, 2, 1, 0),
    "CM-03": (3,),
    "CM-04": (2,),
    "CM-05": (1, 1),
    "CM-06": (2, 1),
    "CM-07": (1, 2),
    "CM-08": (2, 1, 2),
    "CM-09": (2, 1),
    "CM-10": (10, 1),
    "CM-11": (2,),
    "CM-12": (3,),
    "CM-13": (3, 1),
    "CM-14": (1, 2),
    "CM-15": (2, 2),
}


def test_all_fifteen_countermodels_are_found_and_recheck() -> None:
    outcomes = enumerate_all()
    assert tuple(outcome.spec.countermodel_id for outcome in outcomes) == tuple(EXPECTED_SIZES)
    assert sum(outcome.candidates_explored for outcome in outcomes) == 3657
    for outcome in outcomes:
        assert outcome.witness.size_vector == EXPECTED_SIZES[outcome.spec.countermodel_id]
        assert outcome.check.qualifies
        assert recheck(outcome.spec.countermodel_id, outcome.witness.model) == outcome.check
        assert outcome.smaller_candidates_explored >= 0
        assert outcome.same_size_qualifying_candidates >= 1
        assert outcome.minimality_status == "proved-by-exhaustive-bounded-search"


def test_detached_copy_preserves_endpoint_package_and_autonomy_but_not_strict_corridor() -> None:
    outcome = next(item for item in enumerate_all() if item.spec.countermodel_id == "CM-02")
    model = outcome.witness.model
    assert model["source_target_distinct"] is True
    assert model["source_derived"] is True
    assert model["exact_temporal_copy"] is True
    assert model["target_package_pass"] is True
    assert model["target_post_copy_autonomous"] is True
    assert model["mixed_stage_count"] == 0
    assert model["strict_overlap_corridor"] is False
    assert outcome.check.conclusion_failures["strict_overlap_corridor_absent"] is True


def test_holonomy_and_arrow_are_separated() -> None:
    outcome = next(item for item in enumerate_all() if item.spec.countermodel_id == "CM-03")
    assert outcome.witness.model["state_count"] == 3
    assert outcome.check.premises["nonzero_route_holonomy"] is True
    assert outcome.check.conclusion_failures["endogenous_arrow_absent"] is True


def test_predictive_collision_is_repaired_by_route_memory() -> None:
    outcome = next(item for item in enumerate_all() if item.spec.countermodel_id == "CM-06")
    assert outcome.check.premises["current_classes_collide"] is True
    assert outcome.check.conclusion_failures["predictive_equality_fails"] is True
    assert outcome.witness.model["memory_repair_separates_witness"] is True
    assert outcome.check.conclusion_failures["unaugmented_state_has_neither_memory_nor_flatness"] is True


def test_branchwise_marginals_do_not_fix_recombination_relation() -> None:
    outcome = next(item for item in enumerate_all() if item.spec.countermodel_id == "CM-15")
    model = outcome.witness.model
    assert model["source_marginals"] == model["target_marginals"]
    assert model["source_relation"] != model["target_relation"]
    assert outcome.check.conclusion_failures["joint_recombination_differs"] is True
