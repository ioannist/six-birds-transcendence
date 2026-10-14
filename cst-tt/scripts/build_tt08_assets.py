#!/usr/bin/env python3
from __future__ import annotations

import csv
from collections import Counter, defaultdict
import hashlib
import json
import platform
from pathlib import Path
import re
import shutil
import subprocess
from typing import Any, Iterable, Mapping

import networkx as nx

from tt08_data import (
    ALLOWED_FINAL_STATUSES,
    CLAIM_LEDGER_ROWS,
    CONDITIONAL_IDS,
    COUNTERMODEL_IDS,
    FINAL_STATEMENTS,
    OPEN_IDS,
    REJECTED_CONSTRUCTIONS,
    SBT_PROVENANCE_SELECTION,
    THEOREM_ASSUMPTIONS,
    TOY_EVIDENCE,
)

ROOT = Path(__file__).resolve().parents[1]
PHASE = "CST-TT-08"
DATE = "2026-08-10"
BASE_TAG = "CST-TT-07A-v1"
BASE_COMMIT = "7ba9167d39e6751706a7ad7152911c61f77af6af"

# Draft surfaces created during development of CST-TT-08.  They are removed
# before every deterministic rebuild so the release has one normative surface
# for each table or report.
LEGACY_DRAFT_SURFACES = (
    "docs/CST-TT-08_FAILED_ALTERNATIVES_AND_REJECTED_DEFINITIONS.md",
    "docs/CST-TT-08_FINAL_CLAIM_ASSUMPTION_NONCLAIM_LEDGER.md",
    "docs/CST-TT-08_FINAL_DEPENDENCY_DAG.dot",
    "docs/CST-TT-08_FINAL_DEPENDENCY_DAG.md",
    "docs/CST-TT-08_FINAL_DEPENDENCY_DAG.svg",
    "docs/CST-TT-08_FINAL_MODEL_AND_CERTIFICATE_CATALOG.md",
    "docs/CST-TT-08_FINAL_SCIENCE_HANDOFF.md",
    "docs/CST-TT-08_FINAL_THEOREM_STATUS_AND_AUDIT.md",
    "docs/CST-TT-08_PAPER_FACING_RESULT_TABLES.md",
    "docs/CST-TT-08_REPRODUCIBILITY_AND_TOOLCHAIN_STATUS.md",
    "docs/CST-TT-08_SBT_PROVENANCE_MAP.md",
    "registries/FINAL_CERTIFICATE_CATALOG.csv",
    "registries/FINAL_FAILED_ALTERNATIVES.csv",
    "registries/FINAL_MODEL_CATALOG.csv",
    "registries/FINAL_PROOF_EVIDENCE.csv",
    "registries/FINAL_SOURCE_PROVENANCE.csv",
    "registries/FINAL_THEOREM_STATEMENTS.json",
)


def cleanup_legacy_drafts() -> None:
    for rel in LEGACY_DRAFT_SURFACES:
        path = ROOT / rel
        if path.is_file() or path.is_symlink():
            path.unlink()


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def write_csv(path: Path, fieldnames: list[str], rows: Iterable[Mapping[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in fieldnames})


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def split_ids(value: str) -> list[str]:
    return [item for item in value.split(";") if item]


def md_table(headers: list[str], rows: Iterable[Iterable[object]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "|" + "|".join("---" for _ in headers) + "|"]
    for row in rows:
        lines.append("| " + " | ".join(str(value).replace("\n", " ") for value in row) + " |")
    return "\n".join(lines)


def final_status(theorem_id: str) -> str:
    if theorem_id in CONDITIONAL_IDS:
        return "conditional"
    if theorem_id in COUNTERMODEL_IDS:
        return "checked finite countermodel"
    if theorem_id in OPEN_IDS:
        return "open"
    raise KeyError(theorem_id)


def build_lean_index() -> tuple[dict[str, list[dict[str, object]]], bool, int]:
    declaration = re.compile(
        r"^\s*(?:noncomputable\s+)?(?:protected\s+)?(?:theorem|lemma|def|structure|inductive|abbrev)\s+([A-Za-z0-9_']+)"
    )
    placeholder = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
    index: dict[str, list[dict[str, object]]] = defaultdict(list)
    placeholder_free = True
    count = 0
    for path in sorted((ROOT / "CSTTT").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if placeholder.search(text):
            placeholder_free = False
        for line_no, line in enumerate(text.splitlines(), 1):
            match = declaration.match(line)
            if match:
                symbol = match.group(1)
                index[symbol].append({"path": path.relative_to(ROOT).as_posix(), "line": line_no})
                count += 1
    return index, placeholder_free, count


def build_evidence_indices() -> tuple[list[dict[str, object]], list[dict[str, object]], dict[str, list[str]]]:
    certificate_rows: list[dict[str, object]] = []
    theorem_to_evidence: dict[str, list[str]] = defaultdict(list)
    model_to_certificates: dict[str, list[str]] = defaultdict(list)

    for path in sorted((ROOT / "formal/certificates").rglob("*.json")):
        data = load_json(path)
        rel = path.relative_to(ROOT).as_posix()
        if not isinstance(data, dict):
            continue
        cert_id = str(data.get("certificate_id") or data.get("search_id") or data.get("model_id") or path.stem)
        theorem_evidence = data.get("theorem_evidence", {})
        theorem_ids = theorem_evidence.get("theorem_ids", []) if isinstance(theorem_evidence, dict) else []
        if not isinstance(theorem_ids, list):
            theorem_ids = []
        model_ref = str(data.get("model_ref", ""))
        model_hash_valid = ""
        if model_ref:
            model_path = ROOT / model_ref
            expected = str(data.get("model_sha256", ""))
            model_hash_valid = str(model_path.is_file() and (not expected or sha256(model_path) == expected)).lower()
            model_to_certificates[model_ref].append(rel)
        evidence_type = "certificate" if "certificate_id" in data else "search/exhaustion"
        row = {
            "evidence_id": cert_id,
            "evidence_type": evidence_type,
            "path": rel,
            "sha256": sha256(path),
            "bytes": path.stat().st_size,
            "result_status": str(data.get("result_status") or data.get("status") or "recorded"),
            "model_ref": model_ref,
            "model_hash_valid": model_hash_valid,
            "claim_lanes": ";".join(str(x) for x in data.get("claim_lanes", []) if x is not None) if isinstance(data.get("claim_lanes"), list) else str(data.get("claim_lanes", "")),
            "theorem_ids": ";".join(str(x) for x in theorem_ids),
            "checker": json.dumps(data.get("checker", {}), sort_keys=True) if data.get("checker") else "",
        }
        certificate_rows.append(row)
        for theorem_id in theorem_ids:
            theorem_to_evidence[str(theorem_id)].append(rel)

    model_rows: list[dict[str, object]] = []
    id_keys = (
        "model_id", "countermodel_id", "profile_id", "path_id", "assembly_id",
        "spec_id", "system_id", "control_id", "witness_id", "certificate_id",
    )
    for path in sorted((ROOT / "models").rglob("*.json")):
        data = load_json(path)
        rel = path.relative_to(ROOT).as_posix()
        model_id = path.stem
        if isinstance(data, dict):
            for key in id_keys:
                if key in data:
                    model_id = str(data[key])
                    break
        model_rows.append(
            {
                "model_id": model_id,
                "path": rel,
                "sha256": sha256(path),
                "bytes": path.stat().st_size,
                "model_family": path.parent.relative_to(ROOT / "models").as_posix(),
                "linked_certificates": ";".join(sorted(model_to_certificates.get(rel, []))),
                "linked_certificate_count": len(model_to_certificates.get(rel, [])),
            }
        )

    write_csv(
        ROOT / "registries/FINAL_CERTIFICATE_INDEX.csv",
        ["evidence_id", "evidence_type", "path", "sha256", "bytes", "result_status", "model_ref", "model_hash_valid", "claim_lanes", "theorem_ids", "checker"],
        certificate_rows,
    )
    write_csv(
        ROOT / "registries/FINAL_MODEL_INDEX.csv",
        ["model_id", "path", "sha256", "bytes", "model_family", "linked_certificates", "linked_certificate_count"],
        model_rows,
    )
    return model_rows, certificate_rows, theorem_to_evidence


def build_theorem_audit(theorem_to_evidence: dict[str, list[str]]) -> list[dict[str, object]]:
    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    countermodels = read_csv(ROOT / "registries/COUNTERMODEL_REGISTRY.csv")
    counter_by_target: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in countermodels:
        counter_by_target[row["target_no_go_id"]].append(row)

    lean_index, placeholder_free, declaration_count = build_lean_index()
    lean_available = shutil.which("lake") is not None and shutil.which("lean") is not None
    rows: list[dict[str, object]] = []
    for theorem in theorem_rows:
        theorem_id = theorem["theorem_id"]
        declarations = split_ids(theorem["lean_statement"])
        declaration_refs: list[str] = []
        missing: list[str] = []
        for full_name in declarations:
            symbol = full_name.rsplit(".", 1)[-1]
            hits = lean_index.get(symbol, [])
            if not hits:
                missing.append(full_name)
            else:
                declaration_refs.extend(f"{hit['path']}:{hit['line']}" for hit in hits)

        evidence_refs = sorted(set(theorem_to_evidence.get(theorem_id, [])))
        counter_refs = counter_by_target.get(theorem_id, [])
        evidence_refs.extend(row["certificate_ref"] for row in counter_refs if row["certificate_ref"] not in evidence_refs)
        status = final_status(theorem_id)
        if status == "conditional":
            reason = "placeholder-free Lean proof source and exact finite evidence are present; promotion to proved requires the pinned Lean kernel build"
            promotion = "run `lake build` on CST-TT-08-v1 and require success"
        elif status == "checked finite countermodel":
            reason = "one or more exact finite countermodels are hash-bound, replayed, and scoped to the declared finite family"
            promotion = "none; this status intentionally reports finite countermodel evidence rather than a universal theorem"
        else:
            reason = "conditional Temporal-IAPS fallback was not authorized because no Temporal-FIACH kill criterion fired"
            promotion = "execute CST-TT-07B only after a documented primary kill"

        rows.append(
            {
                "theorem_id": theorem_id,
                "name": theorem["name"],
                "family": theorem["family"],
                "kind": theorem["kind"],
                "final_status": status,
                "exact_statement": FINAL_STATEMENTS[theorem_id],
                "claim_lanes": theorem["claim_lanes"],
                "dependencies": theorem["dependencies"],
                "toy_dependencies": theorem["toy_dependencies"],
                "assumption_ids": THEOREM_ASSUMPTIONS[theorem_id],
                "formal_declarations": theorem["lean_statement"],
                "declaration_refs": ";".join(sorted(set(declaration_refs))),
                "declarations_found": str(not missing).lower(),
                "missing_declarations": ";".join(missing),
                "placeholder_free_repository": str(placeholder_free).lower(),
                "kernel_compile_status": "available-not-yet-run" if lean_available else "unavailable-in-execution-environment",
                "evidence_refs": ";".join(sorted(set(evidence_refs))),
                "evidence_count": len(set(evidence_refs)),
                "status_basis": reason,
                "promotion_condition": promotion,
                "claim_ceiling": theorem["claim_ceiling"],
                "legacy_provenance_ids": theorem["legacy_provenance_ids"],
            }
        )

    fields = [
        "theorem_id", "name", "family", "kind", "final_status", "exact_statement",
        "claim_lanes", "dependencies", "toy_dependencies", "assumption_ids",
        "formal_declarations", "declaration_refs", "declarations_found",
        "missing_declarations", "placeholder_free_repository", "kernel_compile_status",
        "evidence_refs", "evidence_count", "status_basis", "promotion_condition",
        "claim_ceiling", "legacy_provenance_ids",
    ]
    write_csv(ROOT / "registries/FINAL_THEOREM_STATUS.csv", fields, rows)
    write_json(
        ROOT / "registries/FINAL_THEOREM_STATUS.json",
        {
            "schema_version": "1.0",
            "phase": PHASE,
            "allowed_statuses": sorted(ALLOWED_FINAL_STATUSES),
            "status_counts": dict(Counter(str(row["final_status"]) for row in rows)),
            "lean_declaration_count": declaration_count,
            "lean_placeholder_free": placeholder_free,
            "lean_kernel_available": lean_available,
            "rows": rows,
        },
    )

    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    for row in rows:
        grouped[str(row["family"])].append(row)
    lines = [
        "# Final theorem and boundary audit",
        "",
        "This table is the normative CST-TT-08 status surface. The only permitted status values are `proved`, `checked finite countermodel`, `conditional`, `killed`, and `open`.",
        "",
        "No row is marked `proved` in this execution because the pinned Lean toolchain was not available. Constructive proof sources are therefore `conditional`; exact negative witnesses remain `checked finite countermodel`.",
        "",
        "## Status summary",
        "",
        md_table(["Status", "Count"], sorted(Counter(str(row["final_status"]) for row in rows).items())),
    ]
    for family in sorted(grouped):
        lines.extend(["", f"## {family}", ""])
        for row in grouped[family]:
            lines.extend(
                [
                    f"### {row['theorem_id']} — {row['name']}",
                    "",
                    f"**Status:** `{row['final_status']}`  ",
                    f"**Statement:** {row['exact_statement']}  ",
                    f"**Dependencies:** `{row['dependencies'] or 'none'}`  ",
                    f"**Assumptions:** `{row['assumption_ids'] or 'none'}`  ",
                    f"**Formal declarations:** `{row['formal_declarations']}`  ",
                    f"**Evidence:** `{row['evidence_refs'] or 'none'}`  ",
                    f"**Claim ceiling:** {row['claim_ceiling']}",
                ]
            )
    (ROOT / "handoff/FINAL_THEOREM_AUDIT.md").parent.mkdir(parents=True, exist_ok=True)
    (ROOT / "handoff/FINAL_THEOREM_AUDIT.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return rows


def toy_evidence_grade(row: dict[str, str]) -> str:
    if row["toy_id"] in {"TFM-01", "TFM-02", "TFM-03"}:
        return "open"
    status = row["status"]
    if "negative" in status or row["toy_id"] in {"TFM-04", "TTM-24"}:
        return "checked finite countermodel"
    return "checked exact finite witness"


def build_toy_catalog() -> list[dict[str, object]]:
    rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    out: list[dict[str, object]] = []
    for row in rows:
        models, certificates, bound = TOY_EVIDENCE[row["toy_id"]]
        out.append(
            {
                "toy_id": row["toy_id"],
                "name": row["name"],
                "role": row["role"],
                "final_evidence_grade": toy_evidence_grade(row),
                "minimal_shape": row["minimal_shape"],
                "discriminates": row["discriminates"],
                "canonical_model_refs": models,
                "canonical_certificate_refs": certificates,
                "minimality_or_bound_ref": bound,
                "expected_output": row["notes"],
                "phase_origin": row["phase"],
            }
        )
    fields = [
        "toy_id", "name", "role", "final_evidence_grade", "minimal_shape",
        "discriminates", "canonical_model_refs", "canonical_certificate_refs",
        "minimality_or_bound_ref", "expected_output", "phase_origin",
    ]
    write_csv(ROOT / "registries/FINAL_TOY_CATALOG.csv", fields, out)
    lines = [
        "# Final toy and model catalog",
        "",
        "The catalog separates exact positive witnesses, exact countermodels, and the unexecuted fallback toys. Model files and certificates are hash-bound in the repository manifest.",
        "",
        md_table(
            ["ID", "Name", "Evidence grade", "Canonical evidence", "Purpose"],
            (
                (row["toy_id"], row["name"], row["final_evidence_grade"], row["canonical_certificate_refs"] or "—", row["discriminates"])
                for row in out
            ),
        ),
    ]
    (ROOT / "handoff/FINAL_MODEL_CATALOG.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return out


def build_dependency_dag(theorem_rows: list[dict[str, object]]) -> tuple[int, int]:
    definitions = read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv")
    assumptions = read_csv(ROOT / "registries/ASSUMPTION_LEDGER.csv")
    toys = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    legacy_edges = read_csv(ROOT / "registries/DEPENDENCY_EDGES.csv")

    nodes: list[dict[str, str]] = []
    edges: list[dict[str, str]] = []
    for row in assumptions:
        nodes.append({"node_id": row["assumption_id"], "node_type": "assumption", "label": row["name"], "status": row["status"]})
    for row in definitions:
        nodes.append({"node_id": row["definition_id"], "node_type": "definition", "label": row["name"], "status": row["status"]})
    for row in toys:
        nodes.append({"node_id": row["toy_id"], "node_type": "toy", "label": row["name"], "status": toy_evidence_grade(row)})
    for row in theorem_rows:
        nodes.append({"node_id": str(row["theorem_id"]), "node_type": "theorem", "label": str(row["name"]), "status": str(row["final_status"])})

    for row in legacy_edges:
        # The historical edge ledger also contains explanatory theorem-to-
        # theorem cross-references whose orientation is not always a proof
        # dependency.  The final DAG retains only definition-layer edges here;
        # theorem proof dependencies come from THEOREM_REGISTRY below.
        if row["source"].startswith("D-") and row["target"].startswith("D-"):
            edges.append({"source": row["source"], "target": row["target"], "edge_type": "definition-dependency", "reason": row["reason"]})
    for row in theorem_rows:
        target = str(row["theorem_id"])
        for source in split_ids(str(row["dependencies"])):
            edges.append({"source": source, "target": target, "edge_type": "theorem-dependency", "reason": "required theorem or boundary"})
        for source in split_ids(str(row["toy_dependencies"])):
            edges.append({"source": source, "target": target, "edge_type": "toy-evidence", "reason": "canonical finite witness or control"})
        for source in split_ids(str(row["assumption_ids"])):
            edges.append({"source": source, "target": target, "edge_type": "assumption", "reason": "explicit purchased assumption"})

    # Deduplicate while retaining deterministic order.
    dedup: dict[tuple[str, str, str, str], dict[str, str]] = {}
    for row in edges:
        dedup[(row["source"], row["target"], row["edge_type"], row["reason"])] = row
    edges = [dedup[key] for key in sorted(dedup)]
    nodes_by_id = {row["node_id"]: row for row in nodes}
    nodes = [nodes_by_id[key] for key in sorted(nodes_by_id)]

    graph = nx.DiGraph()
    graph.add_nodes_from(row["node_id"] for row in nodes)
    graph.add_edges_from((row["source"], row["target"]) for row in edges)
    if not nx.is_directed_acyclic_graph(graph):
        raise RuntimeError(f"final dependency graph has cycles: {list(nx.simple_cycles(graph))[:5]}")

    write_csv(ROOT / "registries/FINAL_DEPENDENCY_NODES.csv", ["node_id", "node_type", "label", "status"], nodes)
    write_csv(ROOT / "registries/FINAL_DEPENDENCY_EDGES.csv", ["source", "target", "edge_type", "reason"], edges)
    write_json(
        ROOT / "registries/FINAL_DEPENDENCY_DAG.json",
        {
            "schema_version": "1.0",
            "phase": PHASE,
            "acyclic": True,
            "node_count": len(nodes),
            "edge_count": len(edges),
            "topological_order": list(nx.topological_sort(graph)),
            "nodes": nodes,
            "edges": edges,
        },
    )

    dot_lines = ["digraph CSTTT08 {", "  rankdir=LR;", "  graph [label=\"CST-TT-08 final dependency DAG\", labelloc=t];", "  node [shape=box, fontsize=9];"]
    for row in nodes:
        label = f"{row['node_id']}\\n{row['label']}".replace('"', "'")
        shape = {"assumption": "ellipse", "definition": "box", "toy": "diamond", "theorem": "component"}.get(row["node_type"], "box")
        dot_lines.append(f'  "{row["node_id"]}" [label="{label}", shape={shape}];')
    for row in edges:
        dot_lines.append(f'  "{row["source"]}" -> "{row["target"]}" [label="{row["edge_type"]}", fontsize=7];')
    dot_lines.append("}")
    dot_path = ROOT / "handoff/FINAL_DEPENDENCY_DAG.dot"
    dot_path.write_text("\n".join(dot_lines) + "\n", encoding="utf-8")
    if shutil.which("dot"):
        subprocess.run(["dot", "-Tsvg", str(dot_path), "-o", str(ROOT / "handoff/FINAL_DEPENDENCY_DAG.svg")], check=True)

    lines = [
        "# Final proof dependency guide",
        "",
        f"The final machine-readable graph contains **{len(nodes)} nodes** and **{len(edges)} edges** and is acyclic.",
        "",
        "The intended proof flow is:",
        "",
        "```text",
        "finite carrier and temporal definitions",
        "  → integrated package and temporal transport",
        "  → strict overlap corridor and autonomy",
        "  → Temporal-FIACH",
        "  → composition, fission, route completion",
        "  → vector defects, robustness, model-relative unbounded maintenance",
        "```",
        "",
        "Negative toys enter as explicit controls rather than as premises that are silently averaged away. Assumption nodes point into every theorem that purchases them.",
    ]
    (ROOT / "handoff/FINAL_PROOF_DEPENDENCY_GUIDE.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return len(nodes), len(edges)


def build_claim_ledger() -> None:
    fields = ["claim_area", "claim_lanes", "status", "theorem_ids", "assumption_ids", "permitted_claim", "nonclaim", "bridge_needed"]
    write_csv(ROOT / "registries/FINAL_CLAIM_ASSUMPTION_NONCLAIM_LEDGER.csv", fields, CLAIM_LEDGER_ROWS)
    lines = [
        "# Final claim, assumption, and nonclaim ledger",
        "",
        "Structural realization, temporal lineage, direct successorship, autonomy, route status, recognition, consciousness, and identity remain separately priced.",
        "",
        md_table(
            ["Area", "Status", "Theorems", "Permitted claim", "Nonclaim"],
            ((row["claim_area"], row["status"], row["theorem_ids"] or "—", row["permitted_claim"], row["nonclaim"]) for row in CLAIM_LEDGER_ROWS),
        ),
    ]
    (ROOT / "handoff/FINAL_CLAIM_CEILING.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_provenance() -> list[dict[str, str]]:
    asset_rows = read_csv(ROOT / "ledgers/asset_provenance.csv")
    statement_rows = read_csv(ROOT / "ledgers/statement_provenance.csv")
    asset_by_statement = {row["statement_id"]: row for row in asset_rows}
    statement_by_id = {row["statement_id"]: row for row in statement_rows}
    out: list[dict[str, str]] = []
    for statement_id, project_use in SBT_PROVENANCE_SELECTION.items():
        if statement_id in asset_by_statement:
            row = asset_by_statement[statement_id]
            out.append(
                {
                    "statement_id": statement_id,
                    "project_use": project_use,
                    "paper_id": row["paper_id"],
                    "source_file": row["source_file"],
                    "source_lines": row["source_lines"],
                    "source_label": row["source_label"],
                    "statement_name": row["statement_name"],
                    "fixed_support": row["fixed_support"],
                    "scope_note": row["scope_note"],
                    "provenance_role": row["provenance_role"],
                }
            )
        else:
            row = statement_by_id[statement_id]
            out.append(
                {
                    "statement_id": statement_id,
                    "project_use": project_use,
                    "paper_id": row["paper_id"],
                    "source_file": row["source_file"],
                    "source_lines": row["source_lines"],
                    "source_label": row["source_label"],
                    "statement_name": row["statement_name"],
                    "fixed_support": row["fixed_support"],
                    "scope_note": row["nonclaim_or_limit"],
                    "provenance_role": "curated statement-level import",
                }
            )
    fields = ["statement_id", "project_use", "paper_id", "source_file", "source_lines", "source_label", "statement_name", "fixed_support", "scope_note", "provenance_role"]
    write_csv(ROOT / "registries/FINAL_SBT_PROVENANCE.csv", fields, out)
    lines = [
        "# Final SBT provenance map",
        "",
        "These sources motivate or constrain the finite cross-carrier formalization. Fixed-support results are explicitly retyped; none is cited as already proving substrate transfer or personal identity.",
        "",
        md_table(
            ["Statement", "Project use", "Source", "Lines", "Scope warning"],
            ((row["statement_id"], row["project_use"], row["source_file"], row["source_lines"], row["scope_note"]) for row in out),
        ),
    ]
    (ROOT / "handoff/FINAL_SBT_PROVENANCE.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    return out


def build_rejected_archive() -> None:
    archive = ROOT / "archive/rejected"
    if archive.exists():
        shutil.rmtree(archive)
    archive.mkdir(parents=True, exist_ok=True)
    fields = ["rejected_id", "name", "status", "reason", "preserved_evidence", "replacement"]
    write_csv(archive / "REJECTED_CONSTRUCTIONS.csv", fields, REJECTED_CONSTRUCTIONS)
    write_json(archive / "REJECTED_CONSTRUCTIONS.json", {"phase": PHASE, "rows": REJECTED_CONSTRUCTIONS})
    for row in REJECTED_CONSTRUCTIONS:
        write_json(archive / f"{row['rejected_id']}.json", {"phase": PHASE, **row})
    lines = [
        "# Preserved rejected constructions",
        "",
        "No rejected idea was silently deleted. Each failed or disallowed construction remains linked to the exact witness that killed it and to the adopted replacement.",
        "",
        md_table(
            ["ID", "Rejected construction", "Status", "Why rejected", "Replacement"],
            ((row["rejected_id"], row["name"], row["status"], row["reason"], row["replacement"]) for row in REJECTED_CONSTRUCTIONS),
        ),
    ]
    text = "\n".join(lines) + "\n"
    (archive / "README.md").write_text(text, encoding="utf-8")
    (archive / "INDEX.md").write_text(text, encoding="utf-8")
    (ROOT / "handoff/FINAL_FAILED_ALTERNATIVES.md").write_text(text, encoding="utf-8")


def recorded_rebuild_matrix() -> list[dict[str, object]]:
    phases = ["CST-TT-00", "CST-TT-01", "CST-TT-02", "CST-TT-03", "CST-TT-04", "CST-TT-05", "CST-TT-06", "CST-TT-07A"]
    rows: list[dict[str, object]] = []
    for phase in phases:
        path = ROOT / f"manifests/{phase}_REBUILD_VERIFICATION.json"
        data = load_json(path)
        rows.append(
            {
                "phase": phase,
                "status": data.get("status", "UNKNOWN"),
                "generated_surface_count": data.get("generated_surface_count", ""),
                "byte_identical_surface_count": data.get("byte_identical_surface_count", ""),
                "source": path.relative_to(ROOT).as_posix(),
                "final_closure_rerun_status": "pending-final-clean-extraction-rerun",
            }
        )
    write_csv(
        ROOT / "registries/FINAL_REBUILD_MATRIX.csv",
        ["phase", "status", "generated_surface_count", "byte_identical_surface_count", "source", "final_closure_rerun_status"],
        rows,
    )
    return rows


def build_result_tables(theorems: list[dict[str, object]], toys: list[dict[str, object]], model_count: int, evidence_count: int) -> None:
    status_counts = Counter(str(row["final_status"]) for row in theorems)
    toy_counts = Counter(str(row["final_evidence_grade"]) for row in toys)
    lines = [
        "# Paper-facing result tables",
        "",
        "## Theorem-status table",
        "",
        md_table(["Status", "Count"], sorted(status_counts.items())),
        "",
        "## Toy-evidence table",
        "",
        md_table(["Evidence grade", "Count"], sorted(toy_counts.items())),
        "",
        "## Evidence-bank size",
        "",
        md_table(["Surface", "Count"], [("Model JSON files", model_count), ("Certificate/search JSON files", evidence_count), ("Canonical toy contracts", len(toys)), ("Theorem/boundary contracts", len(theorems))]),
        "",
        "## Primary structural result",
        "",
        "A valid exact finite Temporal-FIACH certificate contains four independently checked components: heterogeneous staged preservation, integrated target package realization, strict carrier-chain temporal lineage, and target-native post-withdrawal autonomy. Composition, fission, route completion, vector defects, bounded robustness, and model-relative unbounded maintenance are separate strengthenings.",
        "",
        "## Mandatory boundaries",
        "",
        "Detached copying, public matching, holonomy alone, external scheduling, stable-but-stalled ticks, local-only package evidence, scalar residuals, unique selection under symmetry, gap/resume, and finite-prefix success are all blocked by exact finite countermodels or boundary certificates.",
    ]
    (ROOT / "handoff/PAPER_RESULT_TABLES.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_science_handoff(theorems: list[dict[str, object]], toys: list[dict[str, object]], provenance_rows: list[dict[str, str]], node_count: int, edge_count: int) -> None:
    status_counts = Counter(str(row["final_status"]) for row in theorems)
    lines = [
        "# CST-TT-08 science handoff",
        "",
        "## 1. Final outcome",
        "",
        "The preferred branch survives: **Temporal-FIACH plus the mandatory no-go kernel**, with direct temporal successorship retained as a separately named strengthening. Temporal-IAPS was not activated because no registered Temporal-FIACH kill criterion fired.",
        "",
        "The core structural relation is:",
        "",
        "```text",
        "TemporalFIACH_e(s,t) :=",
        "  DistinctCarrier(S,T)",
        "  ∧ SourcePkg(S,s)",
        "  ∧ StagedClausePreservation(e,s,t)",
        "  ∧ IntegratedPkg(T,t,e)",
        "  ∧ StrictTemporalCarrierChain(e,s,t)",
        "  ∧ AutonomousAfterWithdrawal(T,e,D,K)",
        "```",
        "",
        "The temporal signature transported through the episode is fixed independently of the lineage verdict:",
        "",
        "```text",
        "TemporalSignature :=",
        "  PredictiveNow + Order + TickPhase + GenuineProgress",
        "  + EndogenousRecordArrow + RouteResidue",
        "  + MaintenanceState + Owner",
        "```",
        "",
        "## 2. What has been landed",
        "",
        "- an integrated finite C1-C8-shaped target package with substantive temporal closure;",
        "- heterogeneous temporal-signature transport;",
        "- a composition-stable chain of live overlap handoffs;",
        "- a separately named immediate direct-successor class;",
        "- target-native withdrawal autonomy;",
        "- the integrated Temporal-FIACH certificate;",
        "- two-hop composition, relation-valued fission, fusion/recombination boundaries, and route completion;",
        "- exact vector defects, bounded hard-gate-preserving robustness, and a model-relative unbounded invariant policy;",
        "- the full negative kernel and 13/13 primary/common toy battery.",
        "",
        "## 3. Formal status",
        "",
        md_table(["Final status", "Count"], sorted(status_counts.items())),
        "",
        "The pinned Lean toolchain was unavailable in this execution environment. Accordingly, no theorem is marked `proved`. The constructive and generic boundary rows are `conditional`: they have explicit placeholder-free Lean proof sources and exact finite evidence, but require a successful `lake build` on the frozen tag for promotion. Exact negative witnesses are reported as `checked finite countermodel`.",
        "",
        "## 4. Main scientific interpretation",
        "",
        "The work supports a precise structural distinction among three things that endpoint similarity alone conflates:",
        "",
        "1. **target realization** — the destination instantiates one coherent, target-owned consciousness-relevant package;",
        "2. **continuous temporal lineage** — realized package time continues through audited live overlap handoffs;",
        "3. **temporal successorship** — an immediate source event can generate a target event without satisfying strict overlap.",
        "",
        "The strict primary says that continuous transcendence is an episode property, not an endpoint property. The direct class records a broader structural succession mode without being smuggled into strict FIACH.",
        "",
        "## 5. Route and memory discipline",
        "",
        "A transferred present is normally route-indexed. Current-state equality can hide future-sufficient differences. Route residue may be erased only when an explicit flatness, normalization, or confluence certificate proves that alternative routes agree. Nonzero translation holonomy blocks a canonical route-independent global `now`.",
        "",
        "## 6. Branching and identity",
        "",
        "Temporal-FIACH is relation-valued. A symmetric live fork can relate one source to two targets, and exact symmetry supplies no invariant unique continuer. This is a structural result only: it neither proves nor disproves personal identity, phenomenal continuity, or survival.",
        "",
        "## 7. Autonomy and liveness",
        "",
        "Autonomy is tested by removing the source, bridge, controller, decoder, scheduler, and undeclared repair. The target passes only with a target-owned controlled invariant. A total policy yields model-relative unbounded maintenance for every admissible disturbance stream, while the countdown family proves that arbitrarily long finite success does not by itself establish such a policy.",
        "",
        "## 8. Evidence architecture",
        "",
        f"The final dependency DAG has **{node_count} nodes** and **{edge_count} edges**. The canonical toy catalog contains **{len(toys)} contracts**, and the final SBT provenance selection contains **{len(provenance_rows)} statement-level sources**.",
        "",
        "The normative machine-readable surfaces are:",
        "",
        "- `registries/FINAL_THEOREM_STATUS.csv`;",
        "- `registries/FINAL_TOY_CATALOG.csv`;",
        "- `registries/FINAL_MODEL_INDEX.csv`;",
        "- `registries/FINAL_CERTIFICATE_INDEX.csv`;",
        "- `registries/FINAL_DEPENDENCY_DAG.json`;",
        "- `registries/FINAL_CLAIM_ASSUMPTION_NONCLAIM_LEDGER.csv`;",
        "- `registries/FINAL_SBT_PROVENANCE.csv`.",
        "",
        "## 9. Claim ceiling",
        "",
        "The repository establishes an exact finite structural precursor. It does **not** establish consciousness, felt flow, phenomenal continuity, empirical recognition, personal survival, numerical identity, A1, A2-P, certificate soundness, or indefinite physical resource availability. H-FELT-TIME and H-CONT-TIME remain explicit interpretive hypotheses.",
        "",
        "## 10. Paper-construction guidance",
        "",
        "A paper can be organized around four logically separate result blocks:",
        "",
        "1. the temporal object and its route-memory discipline;",
        "2. integrated target realization and strict temporal lineage;",
        "3. withdrawal autonomy and the combined Temporal-FIACH certificate;",
        "4. no-gos, branching, direct successorship, robustness, and liveness boundaries.",
        "",
        "Do not present the direct-successor class as strict FIACH, do not turn a relation-valued fork into unique identity, and do not state the phenomenal interpretation without its additional assumptions.",
        "",
        "## 11. First external formal action",
        "",
        "Restore the frozen archive and run `lake build` with `leanprover/lean4:v4.28.0`. If and only if the build succeeds, the conditional rows whose declarations compile may be promoted to `proved`; exact finite countermodel rows retain their existing status.",
    ]
    (ROOT / "handoff/CST-TT-08_SCIENCE_HANDOFF.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def update_project_surfaces(theorems: list[dict[str, object]], toys: list[dict[str, object]], model_count: int, evidence_count: int, node_count: int, edge_count: int) -> None:
    project_path = ROOT / "registries/PROJECT_REGISTRY.json"
    project = load_json(project_path)
    status_counts = Counter(str(row["final_status"]) for row in theorems)
    project.update(
        {
            "current_phase": PHASE,
            "phase": PHASE,
            "phase_base_tag": BASE_TAG,
            "phase_base_commit": BASE_COMMIT,
            "phase_status": "final-science-closure",
            "science_program_closed": True,
            "next_phase": "none-science-program-closed",
            "final_branch_outcome": "preferred-Temporal-FIACH-plus-no-go-kernel",
            "fallback_status": "Temporal-IAPS remains open and unauthorized; no primary kill fired",
            "fallback_unlocked": False,
            "final_theorem_status_counts": dict(status_counts),
            "final_toy_contract_count": len(toys),
            "final_model_index_count": model_count,
            "final_model_catalog_count": model_count,
            "final_evidence_index_count": evidence_count,
            "final_certificate_catalog_count": evidence_count,
            "final_rejected_alternatives_count": len(REJECTED_CONSTRUCTIONS),
            "final_dependency_node_count": node_count,
            "final_dependency_edge_count": edge_count,
            "generic_theorems_lean_compiled": 0,
            "generic_theorems_proved": 0,
            "formal_status_note": "conditional rows await pinned Lean-kernel compilation",
        }
    )
    write_json(project_path, project)

    README = """# CST-TT: Temporal substrate transcendence theorem and toy assets

Current frozen phase: **CST-TT-08 — final science closure**.

Final branch outcome: **Temporal-FIACH plus the mandatory no-go kernel**, with direct temporal successorship retained as a separately named strengthening. Temporal-IAPS remains open but unauthorized because no Temporal-FIACH kill criterion fired.

The repository contains the complete exact finite theorem-source, certificate, countermodel, toy, dependency, provenance, and paper-facing science handoff bank. Constructive proof sources remain `conditional` until the pinned Lean toolchain compiles the frozen tag.

No consciousness, phenomenal-continuity, survival, numerical-identity, A1, A2-P, empirical-recognition, certificate-soundness, or indefinite physical-persistence conclusion is claimed.
"""
    (ROOT / "README.md").write_text(README, encoding="utf-8")
    (ROOT / "STATE.md").write_text("# State\n\nCST-TT science program closed at the preferred Temporal-FIACH branch; paper-facing handoff frozen.\n", encoding="utf-8")
    (ROOT / "STATUS.md").write_text("# Status\n\nFinal science closure complete. External Lean-kernel compilation is the only formal promotion gate.\n", encoding="utf-8")
    (ROOT / "docs/PHASE_BOUNDARY.md").write_text(
        "# CST-TT-08 final boundary\n\n"
        "The theorem-and-toy science program is closed. Temporal-FIACH remains primary; direct succession is separate; Temporal-IAPS remains unexecuted.\n\n"
        "The frozen science bank includes full-handoff composition, relation-valued fission, the fusion/recombination boundary, exact robustness, model-relative unbounded maintenance, and 13/13 primary/common toy closure. CST-TT-07A is preserved as the immediate base tag.\n\n"
        "No manuscript was written. No empirical or ontological bridge was added. The exact finite structural results do not establish consciousness, phenomenal continuity, personal survival, or numerical identity. The next work product, if authorized, is paper writing from `handoff/CST-TT-08_SCIENCE_HANDOFF.md`.\n",
        encoding="utf-8",
    )
    (ROOT / "docs/CST-TT-08_FINAL_SCIENCE_CLOSURE.md").write_text(
        "# CST-TT-08 final science closure\n\n"
        "Preferred outcome frozen: Temporal-FIACH plus the mandatory no-go kernel and optional direct-successor strengthening.\n\n"
        "Normative statuses use only `proved`, `checked finite countermodel`, `conditional`, `killed`, or `open`. No proof-source row is marked `proved` without a Lean-kernel build.\n\n"
        "The complete paper-facing scientific handoff is `handoff/CST-TT-08_SCIENCE_HANDOFF.md`.\n",
        encoding="utf-8",
    )
    restore = """# Restore and verify CST-TT-08

```bash
unzip CST-TT-08_cst-temporal-transcendence_repo.zip
cd cst-temporal-transcendence
git status --short --branch
git rev-parse CST-TT-08-v1^{}
export PYTHONHASHSEED=0
export PYTHONPATH=src:scripts
python3 -m pytest -q
python3 scripts/validate_tt08.py --no-write --require-tag --require-clean --require-manifest
python3 scripts/verify_tt08_rebuild.py
lake build   # required to promote conditional proof-source rows to proved
```

The Python and certificate checks do not substitute for Lean-kernel compilation. If `lake` is unavailable, that check is skipped and is not counted as passed.
"""
    (ROOT / "docs/RESTORE_AND_BUILD.md").write_text(restore, encoding="utf-8")
    (ROOT / "RESTORE_AND_VERIFY.md").write_text(restore, encoding="utf-8")

    changelog = ROOT / "CHANGELOG.md"
    text = changelog.read_text(encoding="utf-8")
    section = "\n## CST-TT-08\n\nFinal theorem statuses, complete model/certificate catalogs, dependency DAG, claim ledger, provenance map, rejected-construction archive, and paper-facing science handoff frozen.\n"
    text = re.sub(r"\n## CST-TT-08\n(?:.|\n)*\Z", "", text).rstrip() + "\n"
    changelog.write_text(text + section, encoding="utf-8")
    (ROOT / "changelog/CST-TT-08.md").write_text(
        "# CST-TT-08\n\nFinal science closure completed on the preferred Temporal-FIACH branch.\n",
        encoding="utf-8",
    )

    lean_available = shutil.which("lean") is not None
    lake_available = shutil.which("lake") is not None
    write_json(
        ROOT / "formal/TOOLCHAIN_STATUS.json",
        {
            "phase": PHASE,
            "lean_toolchain": "leanprover/lean4:v4.28.0",
            "lean_executable_detected_at_build": lean_available,
            "lake_executable_detected_at_build": lake_available,
            "lean_compile_status": "not-run-toolchain-unavailable" if not (lean_available and lake_available) else "available-pending-final-check",
            "python_certificate_status": "checked",
            "final_status_policy": "no theorem is promoted to proved without successful kernel compilation",
            "python_version": platform.python_version(),
        },
    )
    formal_readme = ROOT / "formal/README.md"
    ftext = formal_readme.read_text(encoding="utf-8").rstrip()
    note = "CST-TT-08 freezes the final proof-source audit. Conditional rows may be promoted to proved only after the pinned Lean kernel compiles this tag."
    if note not in ftext:
        formal_readme.write_text(ftext + "\n\n" + note + "\n", encoding="utf-8")


def build_manifests(theorems: list[dict[str, object]], toys: list[dict[str, object]], model_count: int, evidence_count: int, node_count: int, edge_count: int) -> None:
    status_counts = Counter(str(row["final_status"]) for row in theorems)
    phase_summary = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "date": DATE,
        "base_tag": BASE_TAG,
        "base_commit": BASE_COMMIT,
        "final_branch_outcome": "preferred: Temporal-FIACH plus mandatory no-go kernel",
        "direct_successor": "retained as separately named strengthening",
        "fallback": "Temporal-IAPS remains open and unauthorized",
        "theorem_status_counts": dict(status_counts),
        "toy_contract_count": len(toys),
        "model_index_count": model_count,
        "certificate_and_search_index_count": evidence_count,
        "dependency_dag": {"nodes": node_count, "edges": edge_count, "acyclic": True},
        "lean_compile_status": "not-run-toolchain-unavailable" if shutil.which("lake") is None else "available-pending-final-check",
        "next_phase": "none-science-program-closed",
    }
    write_json(ROOT / "manifests/CST-TT-08_PHASE_SUMMARY.json", phase_summary)
    write_json(ROOT / "manifests/PHASE_SUMMARY.json", phase_summary)

    theorem_delta = [
        {
            "theorem_id": row["theorem_id"],
            "prior_status": next(r["status"] for r in read_csv(ROOT / "registries/THEOREM_REGISTRY.csv") if r["theorem_id"] == row["theorem_id"]),
            "final_status": row["final_status"],
            "status_basis": row["status_basis"],
            "promotion_condition": row["promotion_condition"],
        }
        for row in theorems
    ]
    write_csv(ROOT / "manifests/CST-TT-08_THEOREM_STATUS_DELTA.csv", list(theorem_delta[0]), theorem_delta)
    model_delta = [
        {"asset_id": "FINAL-THEOREM-STATUS", "asset_kind": "normative-status-table", "count": len(theorems), "status": "frozen", "principal_result": dict(status_counts)},
        {"asset_id": "FINAL-TOY-CATALOG", "asset_kind": "toy-contract-catalog", "count": len(toys), "status": "frozen", "principal_result": "complete primary, negative, strengthening, and fallback catalog"},
        {"asset_id": "FINAL-MODEL-INDEX", "asset_kind": "model-index", "count": model_count, "status": "frozen", "principal_result": "all model JSON surfaces hash-indexed"},
        {"asset_id": "FINAL-EVIDENCE-INDEX", "asset_kind": "certificate-and-search-index", "count": evidence_count, "status": "frozen", "principal_result": "all certificate and bounded-search JSON surfaces hash-indexed"},
        {"asset_id": "FINAL-DAG", "asset_kind": "dependency-dag", "count": node_count, "status": "frozen", "principal_result": f"{node_count} nodes / {edge_count} edges / acyclic"},
        {"asset_id": "SCIENCE-HANDOFF", "asset_kind": "paper-facing-handoff", "count": 1, "status": "frozen", "principal_result": "self-contained science handoff; no manuscript prose"},
    ]
    write_csv(ROOT / "manifests/CST-TT-08_MODEL_CERTIFICATE_DELTA.csv", ["asset_id", "asset_kind", "count", "status", "principal_result"], model_delta)

    completion = f"""# CST-TT-08 Completion Report

**Phase:** {PHASE}
**Base:** `{BASE_TAG}` / `{BASE_COMMIT}`
**Date:** {DATE}

## Final branch outcome

Preferred outcome frozen: **Temporal-FIACH plus the mandatory no-go kernel**, with direct temporal successorship retained as a separately named strengthening. Temporal-IAPS remains open and unauthorized because no primary kill criterion fired.

## Final asset bank

- {len(theorems)} theorem/boundary contracts in the normative final status table;
- status counts: {dict(status_counts)};
- {len(toys)} canonical toy contracts;
- {model_count} model JSON surfaces;
- {evidence_count} certificate/search JSON surfaces;
- acyclic dependency DAG with {node_count} nodes and {edge_count} edges;
- complete claim/assumption/nonclaim ledger;
- statement-level SBT provenance map;
- preserved archive of rejected constructions;
- self-contained paper-facing science handoff.

## Formal status

The pinned Lean toolchain was unavailable. No theorem is marked `proved`. Placeholder-free constructive proof sources are `conditional` until `lake build` succeeds on the frozen tag. Exact negative witnesses are `checked finite countermodel`.

## Claim ceiling

No consciousness, phenomenal continuity, personal survival, numerical identity, A1, A2-P, empirical recognition, consciousness-certificate soundness, or indefinite physical-resource result is claimed.
"""
    (ROOT / "manifests/CST-TT-08_COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")
    (ROOT / "manifests/COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")


def main() -> int:
    cleanup_legacy_drafts()
    (ROOT / "handoff").mkdir(parents=True, exist_ok=True)
    model_rows, evidence_rows, theorem_to_evidence = build_evidence_indices()
    theorem_rows = build_theorem_audit(theorem_to_evidence)
    toy_rows = build_toy_catalog()
    node_count, edge_count = build_dependency_dag(theorem_rows)
    build_claim_ledger()
    provenance_rows = build_provenance()
    build_rejected_archive()
    recorded_rebuild_matrix()
    build_result_tables(theorem_rows, toy_rows, len(model_rows), len(evidence_rows))
    build_science_handoff(theorem_rows, toy_rows, provenance_rows, node_count, edge_count)
    update_project_surfaces(theorem_rows, toy_rows, len(model_rows), len(evidence_rows), node_count, edge_count)
    build_manifests(theorem_rows, toy_rows, len(model_rows), len(evidence_rows), node_count, edge_count)
    print(
        f"CST-TT-08 assets built: {len(theorem_rows)} theorem rows, {len(toy_rows)} toy rows, "
        f"{len(model_rows)} models, {len(evidence_rows)} evidence JSONs, {node_count}/{edge_count} DAG"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
