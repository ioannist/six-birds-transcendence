from __future__ import annotations

import hashlib
import json
from pathlib import Path

from cst_tt.strengthenings import audit_generalized_continuity_path, audit_overlap_direct_relation, bounded_relation_truth_table

ROOT = Path(__file__).resolve().parents[1]


def load(rel: str) -> dict:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def digest(rel: str) -> str:
    return hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()


def test_overlap_direct_relation_replays_and_keeps_strict_fiach_unchanged() -> None:
    cert = load("formal/certificates/strengthenings/continuity/ODR-01.certificate.json")
    model = load(cert["model_ref"])
    assert digest(cert["model_ref"]) == cert["model_sha256"]
    audit = audit_overlap_direct_relation(model, ROOT)
    assert audit.to_dict() == cert["audit"]
    assert audit.relation_result_valid
    assert audit.overlap_direct_incomparable
    assert audit.overlap_embeds_generalized
    assert audit.direct_embeds_generalized
    assert audit.generalized_strictly_broader_than_overlap
    assert audit.primary_definition_unchanged
    assert audit.fallback_remains_locked
    assert audit.detached_copy_excluded
    assert audit.temporal_gap_excluded
    assert audit.same_carrier_excluded


def test_generalized_paths_cover_overlap_direct_and_mixed_modes() -> None:
    expected = {
        "GCP-OVERLAP-01": (["overlap"], True),
        "GCP-DIRECT-01": (["direct"], False),
        "GCP-MIXED-01": (["overlap", "direct"], False),
    }
    for path_id, (modes, primary_eligible) in expected.items():
        cert = load(f"formal/certificates/strengthenings/continuity/{path_id}.certificate.json")
        spec = load(cert["model_ref"])
        audit = audit_generalized_continuity_path(spec, ROOT)
        assert audit.to_dict() == cert["audit"]
        assert audit.generalized_path_valid
        assert list(audit.mode_sequence) == modes
        assert audit.primary_fiach_eligible is primary_eligible
        assert audit.no_temporal_gap
        assert audit.exact_carrier_frontiers
        assert audit.exact_signature_frontiers
        assert audit.exact_ownership_frontiers


def test_exact_relation_truth_table_has_both_embeddings_and_one_strict_witness() -> None:
    result = bounded_relation_truth_table()
    frozen = load("formal/certificates/search/OVERLAP_DIRECT_RELATION_TRUTH_TABLE.json")
    assert result == frozen
    assert result["candidates_examined"] == 4
    assert result["overlap_embedding_violations"] == 0
    assert result["direct_embedding_violations"] == 0
    assert result["strict_broadening_witnesses"] == 1
