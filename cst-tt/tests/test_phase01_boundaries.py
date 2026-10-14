from __future__ import annotations

import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_structural_handoff_lands_without_ontological_overclaim() -> None:
    project = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    assert project["phase"] in {"CST-TT-07A", "CST-TT-08"}
    assert project["positive_handoff_witnesses"] == 4
    assert project["checked_full_handoff_composition_certificates"] == 1
    assert project["checked_relation_valued_fission_certificates"] == 1
    assert project["checked_fusion_boundary_certificates"] == 1
    assert project["checked_route_completion_certificates"] == 2
    assert project["checked_primary_common_toy_suite"] == "13/13"
    assert project["checked_generalized_continuity_certificates"] == 4
    assert project["checked_defect_profile_certificates"] == 8
    assert project["checked_robustness_certificates"] == 7
    assert project["checked_unbounded_invariant_certificates"] == 1
    assert project["fallback_unlocked"] is False
    if project["phase"] == "CST-TT-08":
        assert project["next_phase"] == "none-science-program-closed"
    else:
        assert project["next_phase"] == "CST-TT-08"

    cert = json.loads((ROOT / "formal/certificates/composition/FIACH-COMP-01.certificate.json").read_text(encoding="utf-8"))
    text = json.dumps(cert).lower()
    assert cert["claim_ceiling"].startswith("exact finite structural")
    assert cert["audit"]["ontology_absent"] is True
    assert '"numerical_identity": true' not in text
    assert '"survival": true' not in text


def test_exact_tt07a_theorem_surfaces_advance_and_fallback_remains_open() -> None:
    rows = list(csv.DictReader((ROOT / "registries/THEOREM_REGISTRY.csv").open(newline="", encoding="utf-8")))
    by_id = {row["theorem_id"]: row for row in rows}
    executable = {row["theorem_id"] for row in rows if row["status"] == "proof-source-and-executable-certificate-landed"}
    required = {
        "TTH-01", "TTH-02", "TTH-03", "TTH-04", "TTH-05", "TTH-06",
        "TTH-07", "TTH-08", "TTH-09", "TTH-10", "TTN-04", "TTN-05",
        "TTD-01", "TTD-02", "TTD-03", "TTS-01", "TTS-02", "TTS-03", "TTS-04",
    }
    assert required.issubset(executable)
    assert by_id["TTN-10"]["status"] == "proof-source-and-checked-finite-countermodel"
    assert by_id["TTN-12"]["status"] == "proof-source-and-checked-finite-countermodel"
    assert by_id["TTN-14"]["status"] == "proof-source-and-checked-finite-countermodel"
    assert by_id["TTF-01"]["status"] == "open-scaffold"
    assert by_id["TTF-08"]["status"] == "open-scaffold"


def test_negative_kernel_remains_intact() -> None:
    text = (ROOT / "docs/NEGATIVE_KERNEL.md").read_text(encoding="utf-8")
    assert all(f"### CM-{index:02d}" in text for index in range(1, 16))
    assert "branch marginals do not determine recombination structure" in text
    assert "None establishes or refutes consciousness" in text
