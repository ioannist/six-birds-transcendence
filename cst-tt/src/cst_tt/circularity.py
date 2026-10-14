from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class CircularityFinding:
    path: str
    line: int
    token: str
    text: str


# Applied only to primitive-definition modules, never to target or policy documents.
FORBIDDEN_PRIMITIVE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("FIACH", re.compile(r"\bFIACH\b", re.IGNORECASE)),
    ("IAPS", re.compile(r"\bIAPS\b", re.IGNORECASE)),
    ("continuation", re.compile(r"\bcontinuation\b", re.IGNORECASE)),
    ("same-subject", re.compile(r"same[_ -]?subject", re.IGNORECASE)),
    ("same-person", re.compile(r"same[_ -]?person", re.IGNORECASE)),
    ("survival", re.compile(r"\bsurvival\b", re.IGNORECASE)),
    ("numerical-identity", re.compile(r"numerical[_ -]?identity", re.IGNORECASE)),
    ("consciousness", re.compile(r"\bconsciousness\b", re.IGNORECASE)),
)


def scan_text(path: Path, root: Path) -> list[CircularityFinding]:
    findings: list[CircularityFinding] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        for token, pattern in FORBIDDEN_PRIMITIVE_PATTERNS:
            if pattern.search(line):
                findings.append(
                    CircularityFinding(
                        path=str(path.relative_to(root)),
                        line=line_number,
                        token=token,
                        text=line.strip(),
                    )
                )
    return findings


def scan_primitive_tree(root: Path) -> list[CircularityFinding]:
    paths = [
        root / "CSTTT/Core",
        root / "CSTTT/Temporal",
        root / "CSTTT/Package",
        root / "CSTTT/Transport",
        root / "CSTTT/Corridor",
        root / "CSTTT/Autonomy",
    ]
    findings: list[CircularityFinding] = []
    for directory in paths:
        for path in sorted(directory.rglob("*.lean")):
            findings.extend(scan_text(path, root))
    return findings
