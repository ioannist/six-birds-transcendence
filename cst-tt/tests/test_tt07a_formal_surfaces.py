from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

MODULES = (
    "CSTTT/Strengthening/ContinuityClass.lean",
    "CSTTT/Robustness/DefectVector.lean",
    "CSTTT/Robustness/TemporalMargins.lean",
    "CSTTT/Autonomy/UnboundedInvariant.lean",
)


def test_tt07a_lean_modules_are_imported_and_placeholder_free() -> None:
    root_text = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
    for rel in MODULES:
        path = ROOT / rel
        text = path.read_text(encoding="utf-8")
        module = path.with_suffix("").relative_to(ROOT).as_posix().replace("/", ".")
        assert f"import {module}" in root_text
        assert forbidden.search(text) is None


def test_expected_tt07a_proof_source_declarations_are_present() -> None:
    corpus = "\n".join((ROOT / rel).read_text(encoding="utf-8") for rel in MODULES)
    for declaration in (
        "GeneralizedTemporalContinuity",
        "overlapDirectIncomparable",
        "generalizedStrictlyBroaderThanOverlap",
        "generalizedPathComposition",
        "DefectVector",
        "acceptedHardGateIsZero",
        "vectorAcceptanceDownwardClosed",
        "scalarSummaryDoesNotDetermineAcceptance",
        "boundedPerturbationPreservesMargin",
        "failedHardGateCannotBeAveragedAway",
        "ExactAutonomyPolicy",
        "modelRelativeUnboundedControlledInvariant",
        "arbitrarilyLongFinitePrefixStillInsufficient",
    ):
        assert declaration in corpus


def test_strict_temporal_fiach_source_is_not_redefined_by_strengthening_module() -> None:
    strengthening = (ROOT / "CSTTT/Strengthening/ContinuityClass.lean").read_text(encoding="utf-8")
    strict = (ROOT / "CSTTT/Targets/TemporalFIACH.lean").read_text(encoding="utf-8")
    assert "def GeneralizedTemporalContinuity" in strengthening
    assert "def TemporalFIACH" in strict
    assert "GeneralizedTemporalContinuity" not in strict
