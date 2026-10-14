from __future__ import annotations

from cst_tt.corridor import (
    bounded_corridor_composition_search,
    bounded_corridor_support_search,
    bounded_direct_path_composition_search,
    bounded_direct_successor_search,
    bounded_nonredundancy_truth_table_search,
)


def test_bounded_corridor_support_search_freezes_copy_and_gap_exclusions() -> None:
    result = bounded_corridor_support_search()
    assert result == {
        "max_stages": 4,
        "candidates_examined": 12_384,
        "strict_passes": 6,
        "detached_candidates_examined": 2_688,
        "detached_passes": 0,
        "gapped_candidates_examined": 11_448,
        "gapped_passes": 0,
        "smallest_positive_stage_count": 3,
        "definition_nonuniversal": True,
        "detached_copy_excluded": True,
        "temporal_gap_excluded": True,
    }


def test_nonredundancy_truth_table_search_is_nonempty_and_verdict_free() -> None:
    result = bounded_nonredundancy_truth_table_search()
    assert result["boolean_update_tables_examined"] == 16
    assert result["jointly_nonredundant_table_count"] == 4
    assert result["jointly_nonredundant_table_masks"] == [6, 7, 8, 9]
    assert result["and_table_is_jointly_nonredundant"] is True


def test_composition_and_direct_searches_freeze_the_key_boundaries() -> None:
    composition = bounded_corridor_composition_search()
    assert composition["candidate_pairs_examined"] == 16
    assert composition["carrier_chain_composition_failures"] == 0
    assert composition["old_endpoint_mixed_rule_failures"] == 16
    assert composition["carrier_chain_rule_composes_all_compatible_pairs"] is True
    assert composition["endpoint_mixedness_is_not_composition_stable"] is True

    direct = bounded_direct_successor_search()
    assert direct["candidates_examined"] == 2_048
    assert direct["valid_direct_successor_shapes"] == 1
    assert direct["detached_like_passes"] == 0
    assert direct["arbitrary_data_edge_passes"] == 0

    paths = bounded_direct_path_composition_search()
    assert paths["candidate_pairs_examined"] == 27
    assert paths["compatible_atomic_pairs"] == 1
    assert paths["valid_composed_paths"] == 1
    assert paths["falsely_atomic_composites"] == 0
