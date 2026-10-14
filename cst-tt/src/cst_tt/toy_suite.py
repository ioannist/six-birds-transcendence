from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import combinations
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping


REQUIRED_TOYS = tuple(f"TTM-{index:02d}" for index in range(1, 14))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(root: Path, rel: str) -> dict[str, Any]:
    value = json.loads((root / rel).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(rel)
    return value


def _evidence_passes(toy_id: str, evidence: Mapping[str, Any]) -> bool:
    audit = evidence.get("audit", {})
    if not isinstance(audit, Mapping):
        audit = {}
    if toy_id == "TTM-01":
        return audit.get("aggregate_valid") is True
    if toy_id == "TTM-02":
        return evidence.get("countermodel_id") in {"CM-01", "CM-02"} and evidence.get("conclusion_failure_status") == "certified"
    if toy_id == "TTM-03":
        return audit.get("direct_successor_valid") is True or audit.get("path_valid") is True
    if toy_id == "TTM-04":
        return evidence.get("countermodel_id") == "CM-04" or audit.get("autonomy_valid") is False
    if toy_id == "TTM-05":
        return audit.get("nonzero_translation_holonomy_witnessed") is True
    if toy_id == "TTM-06":
        return audit.get("flatness_valid") is True and audit.get("temporal_endpoints_route_independent") is True
    if toy_id == "TTM-07":
        return audit.get("relation_valued_fission_valid") is True
    if toy_id == "TTM-08":
        return evidence.get("countermodel_id") == "CM-12"
    if toy_id == "TTM-09":
        return audit.get("anti_stall_on_invariant") is False and audit.get("autonomy_valid") is False
    if toy_id == "TTM-10":
        return evidence.get("countermodel_id") == "CM-13" or (audit.get("budget_solvent_on_invariant") is False and audit.get("collapse_trace_length") is not None)
    if toy_id == "TTM-11":
        return evidence.get("countermodel_id") == "CM-08"
    if toy_id == "TTM-12":
        return evidence.get("countermodel_id") == "CM-09"
    if toy_id == "TTM-13":
        return evidence.get("countermodel_id") == "CM-10"
    return False


@dataclass(frozen=True)
class ToySuiteAudit:
    certificate_id: str
    exact_required_coverage: bool
    unique_toy_ids: bool
    evidence_files_exist: bool
    evidence_hashes_valid: bool
    every_evidence_contract_passes: bool
    every_toy_crosslinked_to_theorem: bool
    positive_negative_boundary_roles_present: bool
    reproduction_commands_present: bool
    claim_ceilings_present: bool
    toy_suite_closed: bool
    failed_obligations: tuple[str, ...]
    toy_count: int
    passing_toy_count: int

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["failed_obligations"] = list(self.failed_obligations)
        return value


def audit_toy_suite(spec: Mapping[str, Any], root: Path) -> ToySuiteAudit:
    entries = spec.get("entries", [])
    entries = [row for row in entries if isinstance(row, Mapping)] if isinstance(entries, list) else []
    ids = [str(row.get("toy_id", "")) for row in entries]
    coverage = set(ids) == set(REQUIRED_TOYS) and len(entries) == len(REQUIRED_TOYS)
    unique = len(ids) == len(set(ids))
    exist_checks = []
    hash_checks = []
    pass_checks = []
    theorem_checks = []
    command_checks = []
    ceiling_checks = []
    roles = set()
    for row in entries:
        rel = row.get("evidence_ref")
        exists = isinstance(rel, str) and (root / rel).is_file()
        exist_checks.append(exists)
        hash_checks.append(bool(exists and row.get("evidence_sha256") == sha256(root / rel)))
        evidence = _load(root, rel) if exists else {}
        pass_checks.append(_evidence_passes(str(row.get("toy_id", "")), evidence))
        theorem_ids = row.get("theorem_ids", [])
        theorem_checks.append(isinstance(theorem_ids, list) and bool(theorem_ids) and all(isinstance(value, str) and value for value in theorem_ids))
        command_checks.append(isinstance(row.get("reproduction_command"), str) and bool(str(row.get("reproduction_command")).strip()))
        ceiling_checks.append(isinstance(row.get("claim_ceiling"), str) and bool(str(row.get("claim_ceiling")).strip()))
        roles.add(str(row.get("role", "")))
    roles_present = {"positive", "negative", "boundary"}.issubset(roles)
    obligations = {
        "TOY-O01-exact-required-coverage": coverage,
        "TOY-O02-unique-toy-ids": unique,
        "TOY-O03-evidence-files-exist": all(exist_checks),
        "TOY-O04-evidence-hashes-valid": all(hash_checks),
        "TOY-O05-evidence-contracts-pass": all(pass_checks),
        "TOY-O06-theorem-crosslinks": all(theorem_checks),
        "TOY-O07-role-diversity": roles_present,
        "TOY-O08-reproduction-commands": all(command_checks),
        "TOY-O09-claim-ceilings": all(ceiling_checks),
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return ToySuiteAudit(
        certificate_id=str(spec.get("certificate_id", "")),
        exact_required_coverage=coverage,
        unique_toy_ids=unique,
        evidence_files_exist=all(exist_checks),
        evidence_hashes_valid=all(hash_checks),
        every_evidence_contract_passes=all(pass_checks),
        every_toy_crosslinked_to_theorem=all(theorem_checks),
        positive_negative_boundary_roles_present=roles_present,
        reproduction_commands_present=all(command_checks),
        claim_ceilings_present=all(ceiling_checks),
        toy_suite_closed=not failed,
        failed_obligations=failed,
        toy_count=len(entries),
        passing_toy_count=sum(pass_checks),
    )


def hidden_equivalence_search(feature_rows: list[Mapping[str, Any]]) -> dict[str, Any]:
    collisions = []
    for left, right in combinations(feature_rows, 2):
        public_left = (left.get("public_signature"), left.get("endpoint_signature"))
        public_right = (right.get("public_signature"), right.get("endpoint_signature"))
        structural_left = tuple(left.get("structural_signature", []))
        structural_right = tuple(right.get("structural_signature", []))
        if public_left == public_right and structural_left != structural_right:
            collisions.append(
                {
                    "left": left.get("toy_id"),
                    "right": right.get("toy_id"),
                    "shared_public_signature": list(public_left),
                    "left_structural_signature": list(structural_left),
                    "right_structural_signature": list(structural_right),
                }
            )
    return {
        "schema_version": "CST-TT-06",
        "algorithm": "pairwise-public-signature-collision-search",
        "toy_count": len(feature_rows),
        "pairs_examined": len(feature_rows) * (len(feature_rows) - 1) // 2,
        "hidden_equivalence_collisions": collisions,
        "collision_count": len(collisions),
        "claim_ceiling": "finite feature-level discriminator audit; no empirical identifiability conclusion",
    }
