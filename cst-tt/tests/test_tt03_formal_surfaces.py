from __future__ import annotations

import csv
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_tt03_lean_sources_have_required_declarations_and_no_placeholders() -> None:
    paths = [
        ROOT / "CSTTT/Transport/FiniteTemporalTransport.lean",
        ROOT / "CSTTT/Transport/RecordArrow.lean",
        ROOT / "CSTTT/Transport/RouteDiscipline.lean",
        ROOT / "CSTTT/Transport/FiniteExamples.lean",
    ]
    text = "\n".join(path.read_text(encoding="utf-8") for path in paths)
    for token in (
        "bundledHeterogeneousTemporalTransport",
        "noCurrentOnlyPredictor",
        "monotoneRecordDescentTransportsArrow",
        "routeIndependentEndpointUnderNormalization",
        "memoryOrFlatness",
        "noCanonicalGlobalNowOfTranslationHolonomy",
        "exactHeterogeneousSignatureAgreement",
        "exampleConfluentEndpoints",
    ):
        assert token in text
    for forbidden in ("sorry", "admit", "axiom", "unsafe"):
        assert forbidden not in text


def test_root_imports_tt03_modules() -> None:
    text = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    for module in (
        "CSTTT.Transport.FiniteTemporalTransport",
        "CSTTT.Transport.RecordArrow",
        "CSTTT.Transport.RouteDiscipline",
        "CSTTT.Transport.FiniteExamples",
    ):
        assert f"import {module}" in text


def test_five_tt03_theorem_surfaces_advanced() -> None:
    rows = {row["theorem_id"]: row for row in csv.DictReader((ROOT / "registries/THEOREM_REGISTRY.csv").open())}
    expected = {
        "TTH-03": "CSTTT.TransportTheory.bundledHeterogeneousTemporalTransport",
        "TTH-09": "CSTTT.RouteTheory.routeIndependentEndpointUnderNormalization",
        "TTH-10": "CSTTT.RecordTheory.monotoneRecordDescentTransportsArrow",
        "TTN-04": "CSTTT.RouteTheory.noCurrentOnlyPredictor",
        "TTN-05": "CSTTT.RouteTheory.noCanonicalGlobalNowOfTranslationHolonomy",
    }
    for theorem_id, declaration in expected.items():
        assert rows[theorem_id]["status"] == "proof-source-and-executable-certificate-landed"
        assert declaration in rows[theorem_id]["lean_statement"]


def test_transport_layer_has_no_later_layer_imports() -> None:
    for path in (ROOT / "CSTTT/Transport").glob("*.lean"):
        text = path.read_text(encoding="utf-8")
        assert "import CSTTT.Autonomy" not in text
        assert "import CSTTT.Targets" not in text
