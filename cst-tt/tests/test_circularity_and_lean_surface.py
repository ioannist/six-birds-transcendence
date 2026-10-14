from __future__ import annotations

import re
from pathlib import Path

from cst_tt.circularity import scan_primitive_tree
from cst_tt.registry import read_csv

ROOT = Path(__file__).resolve().parents[1]


def test_primitive_lean_tree_passes_verdict_vocabulary_scan() -> None:
    assert scan_primitive_tree(ROOT) == []


def test_lean_scaffold_has_no_unproved_placeholder_commands() -> None:
    pattern = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
    for path in sorted((ROOT / "CSTTT").rglob("*.lean")):
        assert pattern.search(path.read_text(encoding="utf-8")) is None, path


def test_every_registered_definition_is_present_in_its_lean_module() -> None:
    for row in read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv"):
        module = ROOT / row["module"]
        assert module.exists(), module
        text = module.read_text(encoding="utf-8")
        assert row["name"] in text, (row["definition_id"], module)


def test_every_registered_lean_statement_is_present() -> None:
    lean_text = "\n".join(
        path.read_text(encoding="utf-8")
        for path in sorted((ROOT / "CSTTT").rglob("*.lean"))
    )
    for row in read_csv(ROOT / "registries/THEOREM_REGISTRY.csv"):
        for declaration in row["lean_statement"].split(";"):
            name = declaration.split(".")[-1]
            assert name in lean_text, (row["theorem_id"], name)


def test_primitive_import_graph_does_not_reverse_layers() -> None:
    forbidden = {
        "CSTTT/Temporal": ("CSTTT.Corridor", "CSTTT.Targets"),
        "CSTTT/Package": ("CSTTT.Corridor", "CSTTT.Autonomy", "CSTTT.Targets"),
        "CSTTT/Transport": ("CSTTT.Corridor", "CSTTT.Targets"),
        "CSTTT/Corridor": ("CSTTT.Targets",),
        "CSTTT/Autonomy": ("CSTTT.Corridor", "CSTTT.Targets"),
    }
    for directory, prefixes in forbidden.items():
        for path in (ROOT / directory).rglob("*.lean"):
            text = path.read_text(encoding="utf-8")
            for prefix in prefixes:
                assert f"import {prefix}" not in text, (path, prefix)


def test_countermodel_kernel_has_all_certificate_declarations_and_no_verdict_primitives() -> None:
    kernel_path = ROOT / "CSTTT/Countermodels/Kernel.lean"
    text = kernel_path.read_text(encoding="utf-8")
    assert "namespace CSTTT.Countermodels" in text
    assert text.count("theorem cm") >= 15
    for row in read_csv(ROOT / "registries/COUNTERMODEL_REGISTRY.csv"):
        name = row["lean_declaration"].split(".")[-1]
        assert f"theorem {name}" in text
    forbidden = ("sameSubject", "personalIdentity", "survivesAs", "isConscious")
    assert all(token not in text for token in forbidden)
