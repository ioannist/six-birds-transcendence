from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_phase_five_reproducibility_policy_is_deterministic_and_bounded() -> None:
    policy = json.loads((ROOT / "config/REPRODUCIBILITY.json").read_text(encoding="utf-8"))
    assert policy["phase"] == "CST-TT-05"
    assert policy["canonical_seed"] == 0
    assert policy["python_hash_seed"] == 0
    assert policy["randomized_search_enabled"] is False
    assert policy["status"] == "deterministic-withdrawal-autonomy-and-temporal-fiach-frozen"
    assert policy["invariant_search_candidates"] == 4_096
    assert policy["finite_disturbance_words_checked"] == 127
    assert policy["next_phase"] == "CST-TT-06"
    assert "not represented as a Lean proof oracle" in policy["usage_boundary"]
