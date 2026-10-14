from __future__ import annotations

import csv
import json
from collections import Counter
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
if not (ROOT / "manifests/CST-TT-08_PHASE_SUMMARY.json").is_file():
    pytest.skip("CST-TT-08 final assets are absent in this historical phase rebuild", allow_module_level=True)


def rows(path: str) -> list[dict[str, str]]:
    with (ROOT / path).open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def test_final_status_table_is_complete_and_deflationary() -> None:
    status = rows("registries/FINAL_THEOREM_STATUS.csv")
    assert len(status) == 39
    assert Counter(row["final_status"] for row in status) == Counter(
        {"conditional": 19, "checked finite countermodel": 12, "open": 8}
    )
    assert all(row["declarations_found"] == "true" for row in status)
    assert all(row["missing_declarations"] == "" for row in status)
    assert not any(row["final_status"] == "proved" for row in status)
    assert next(row for row in status if row["theorem_id"] == "TTN-05")["final_status"] == "conditional"


def test_complete_model_certificate_and_toy_indices() -> None:
    models = rows("registries/FINAL_MODEL_INDEX.csv")
    certs = rows("registries/FINAL_CERTIFICATE_INDEX.csv")
    toys = rows("registries/FINAL_TOY_CATALOG.csv")
    assert len(models) == len(list((ROOT / "models").rglob("*.json"))) == 203
    assert len(certs) == len(list((ROOT / "formal/certificates").rglob("*.json"))) == 233
    assert len(toys) == 28


def test_claim_ceiling_and_fallback_are_explicit() -> None:
    ledger = rows("registries/FINAL_CLAIM_ASSUMPTION_NONCLAIM_LEDGER.csv")
    assert len(ledger) == 10
    text = "\n".join(" ".join((row["permitted_claim"], row["nonclaim"], row["bridge_needed"])).lower() for row in ledger)
    for token in ("consciousness", "phenomenal continuity", "personal survival", "numerical identity", "empirical recognition", "a2-p"):
        assert token in text
    project = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    assert project["phase"] == "CST-TT-08"
    assert project["science_program_closed"] is True
    assert project["fallback_unlocked"] is False
    assert "unauthorized" in project["fallback_status"]


def test_rejected_alternatives_and_handoff_are_preserved() -> None:
    rejected = rows("archive/rejected/REJECTED_CONSTRUCTIONS.csv")
    assert Counter(row["status"] for row in rejected) == Counter({"killed": 11, "open": 1})
    handoff = (ROOT / "handoff/CST-TT-08_SCIENCE_HANDOFF.md").read_text(encoding="utf-8")
    for phrase in (
        "Temporal-FIACH plus the mandatory no-go kernel",
        "Temporal-IAPS was not activated",
        "no theorem is marked `proved`",
        "route-indexed",
        "relation-valued",
        "does **not** establish consciousness",
    ):
        assert phrase in handoff
