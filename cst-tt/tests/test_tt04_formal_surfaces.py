from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def test_tt04_lean_modules_are_imported_and_placeholder_free() -> None:
    modules = [
        ROOT / "CSTTT/Corridor/FiniteTemporalCorridor.lean",
        ROOT / "CSTTT/Corridor/Composition.lean",
        ROOT / "CSTTT/Corridor/FiniteDirectSuccessor.lean",
    ]
    root_text = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    for path in modules:
        text = path.read_text(encoding="utf-8")
        module = path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
        assert f"import {module}" in root_text
        assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", text)


def test_expected_tt04_proof_source_declarations_are_present() -> None:
    corpus = "\n".join(
        (ROOT / rel).read_text(encoding="utf-8")
        for rel in (
            "CSTTT/Corridor/FiniteTemporalCorridor.lean",
            "CSTTT/Corridor/Composition.lean",
            "CSTTT/Corridor/FiniteDirectSuccessor.lean",
        )
    )
    for declaration in (
        "atomicTemporalCorridorCertificateSound",
        "noMixedStageExcludesAtomicCorridor",
        "realizedGapExcludesAtomicCorridor",
        "strictTemporalCorridorComposition",
        "directSuccessorValidity",
        "directSuccessorDetachedCopyExclusion",
        "directSuccessorPathComposition",
    ):
        assert declaration in corpus


def test_primitive_definitions_do_not_encode_verdict_vocabulary() -> None:
    corpus = "\n".join(
        (ROOT / rel).read_text(encoding="utf-8").lower()
        for rel in (
            "CSTTT/Corridor/FiniteTemporalCorridor.lean",
            "CSTTT/Corridor/Composition.lean",
            "CSTTT/Corridor/FiniteDirectSuccessor.lean",
            "src/cst_tt/corridor.py",
        )
    )
    for forbidden in (
        "same subject",
        "same person",
        "personal identity",
        "numerical identity",
        "survival predicate",
        "consciousness predicate",
    ):
        assert forbidden not in corpus
