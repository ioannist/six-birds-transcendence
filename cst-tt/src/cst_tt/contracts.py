from __future__ import annotations

from pathlib import Path

from .registry import read_csv

ROOT = Path(__file__).resolve().parents[2]


def theorem_rows() -> list[dict[str, str]]:
    return read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")


def model_rows() -> list[dict[str, str]]:
    return [
        {
            "model_id": row["toy_id"],
            "name": row["name"],
            "status": "contract_frozen_not_instantiated",
        }
        for row in read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    ]


def target_contract() -> dict[str, object]:
    return {
        "target": "Temporal-FIACH",
        "result_fields": ["S-R", "S-L", "A", "ROUTE"],
        "recognition_separate": True,
        "ontology_separate": True,
        "claim_ceiling": "structural precursor only",
    }
