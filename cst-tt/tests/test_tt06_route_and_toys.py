from __future__ import annotations

import hashlib
import json
from pathlib import Path

from cst_tt.handoff_composition import audit_route_completion
from cst_tt.toy_suite import audit_toy_suite

ROOT = Path(__file__).resolve().parents[1]


def load(rel: str) -> dict:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def digest(rel: str) -> str:
    return hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()


def test_route_indexed_completion_retains_memory() -> None:
    cert = load("formal/certificates/route_completion/ROUTE-COMP-INDEXED-01.certificate.json")
    audit = audit_route_completion(cert, ROOT)
    assert audit.route_completion_valid is True
    assert audit.output_route_status == "route-indexed"
    assert audit.route_indexed_residue_retained is True
    assert audit.flatness_independently_certified is False


def test_flat_completion_requires_independent_normalization() -> None:
    cert = load("formal/certificates/route_completion/ROUTE-COMP-FLAT-01.certificate.json")
    audit = audit_route_completion(cert, ROOT)
    assert audit.route_completion_valid is True
    assert audit.output_route_status == "flat"
    assert audit.flatness_independently_certified is True
    assert audit.common_normal_form_present is True
    assert audit.clock_translation_holonomy_zero is True
    assert audit.no_unlicensed_memory_erasure is True


def test_nonflat_route_cannot_be_relabelled_flat() -> None:
    control = load("formal/certificates/route_completion/controls/ROUTE-COMP-C01.certificate.json")
    assert control["audit"]["route_completion_valid"] is False
    assert "RC-O05-route-indexed-or-flat-evidence" in control["audit"]["failed_obligations"]
    assert control["audit"]["no_unlicensed_memory_erasure"] is False


def test_primary_toy_suite_is_hash_bound_and_closed() -> None:
    cert = load("formal/certificates/toy_suite/TOY-SUITE-PRIMARY-01.certificate.json")
    audit = audit_toy_suite(cert, ROOT)
    assert audit.toy_suite_closed is True
    assert audit.to_dict() == cert["audit"]
    assert audit.toy_count == 13
    assert audit.passing_toy_count == 13
    for row in cert["entries"]:
        assert digest(row["evidence_ref"]) == row["evidence_sha256"]


def test_toy_feature_search_exposes_publicly_colliding_structural_cases() -> None:
    search = load("formal/certificates/search/TOY_HIDDEN_EQUIVALENCE_SEARCH.json")
    assert search["toy_count"] == 13
    assert search["pairs_examined"] == 78
    assert search["collision_count"] > 0
    pairs = {(row["left"], row["right"]) for row in search["hidden_equivalence_collisions"]}
    assert ("TTM-01", "TTM-02") in pairs
    assert ("TTM-05", "TTM-06") in pairs
