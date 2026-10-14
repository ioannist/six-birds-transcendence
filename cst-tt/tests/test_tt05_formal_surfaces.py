from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_tt05_lean_sources_have_expected_declarations_and_no_placeholders() -> None:
    files = [
        ROOT / "CSTTT/Autonomy/FiniteAutonomy.lean",
        ROOT / "CSTTT/Targets/FiniteTemporalFIACH.lean",
    ]
    text = "\n".join(path.read_text(encoding="utf-8") for path in files)
    for name in (
        "finiteHorizonRunExists",
        "postWithdrawalFiniteHorizonInvariance",
        "removedEssentialResourceExcludesAutonomy",
        "stalledOnlyResponsesExcludeAutonomy",
        "insolventOnlyResponsesExcludeAutonomy",
        "temporalFIACHCertificateSoundness",
        "temporalFIACHEndpointsLinked",
        "threeLaneAggregateExact",
    ):
        assert name in text
    lowered = text.lower()
    for forbidden in ("sorry", "admit", "axiom", "unsafe"):
        assert forbidden not in lowered


def test_aggregate_module_imports_autonomy_before_fiach_target() -> None:
    lines = (ROOT / "CSTTT.lean").read_text(encoding="utf-8").splitlines()
    autonomy = lines.index("import CSTTT.Autonomy.FiniteAutonomy")
    target = lines.index("import CSTTT.Targets.FiniteTemporalFIACH")
    assert autonomy < target
