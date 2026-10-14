from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]


def test_tt06_lean_declarations_are_explicit_and_imported() -> None:
    required = {
        "CSTTT/Targets/Composition.lean": (
            "fullTemporalHandoffComposition",
            "composedHandoffPreservesIndependentLanes",
            "routeIndexedComponentPreventsAutomaticFlatness",
        ),
        "CSTTT/Corridor/Fission.lean": (
            "relationValuedTemporalFission",
            "targetSwapPreservesFissionValidity",
            "targetSwapSymmetryNonselection",
        ),
        "CSTTT/Package/FusionBoundary.lean": (
            "fusionLineageDoesNotImplyIntegratedPackage",
            "fusionBranchwiseDoesNotRepairRecombination",
        ),
        "CSTTT/Targets/RouteCompletion.lean": (
            "noUnlicensedRouteMemoryErasure",
            "retainedRouteMemoryYieldsIndexedStatus",
            "certifiedNormalizationYieldsFlatStatus",
        ),
    }
    root_imports = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    for rel, declarations in required.items():
        text = (ROOT / rel).read_text(encoding="utf-8")
        assert f"import {rel.removesuffix('.lean').replace('/', '.')}" in root_imports
        for declaration in declarations:
            assert f"theorem {declaration}" in text
        for token in ("sorry", "admit", "axiom", "unsafe"):
            assert token not in text


def test_tt06_certificate_schemas_accept_landed_certificates() -> None:
    pairs = {
        "full_handoff_composition_certificate.schema.json": "formal/certificates/composition/FIACH-COMP-01.certificate.json",
        "temporal_fission_certificate.schema.json": "formal/certificates/fission/FISSION-POS-01.certificate.json",
        "fusion_boundary_certificate.schema.json": "formal/certificates/fusion/FUSION-BOUNDARY-01.certificate.json",
        "route_completion_certificate.schema.json": "formal/certificates/route_completion/ROUTE-COMP-FLAT-01.certificate.json",
        "toy_suite_closure_certificate.schema.json": "formal/certificates/toy_suite/TOY-SUITE-PRIMARY-01.certificate.json",
    }
    for schema_name, cert_rel in pairs.items():
        schema = json.loads((ROOT / "schemas/certificates" / schema_name).read_text(encoding="utf-8"))
        cert = json.loads((ROOT / cert_rel).read_text(encoding="utf-8"))
        Draft202012Validator.check_schema(schema)
        assert list(Draft202012Validator(schema).iter_errors(cert)) == []


def test_tt06_assets_remain_present_and_later_phase_keeps_fallback_locked() -> None:
    project = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    assert project["phase"] in {"CST-TT-07A", "CST-TT-08"}
    assert project["fallback_unlocked"] is False
    if project["phase"] == "CST-TT-08":
        assert project["next_phase"] == "none-science-program-closed"
        assert project["fallback_status"] == "Temporal-IAPS remains open and unauthorized; no primary kill fired"
    else:
        assert project["next_phase"] == "CST-TT-08"
        assert project["fallback_status"] == "Temporal-IAPS remains locked"
