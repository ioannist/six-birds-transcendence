from __future__ import annotations

from copy import deepcopy
from typing import Any

from cst_tt.types import ClauseId

C1 = ClauseId.C1_OBJECTHOOD.value
C2 = ClauseId.C2_STRICT_PROMOTION.value
C3 = ClauseId.C3_REFLEXIVE_SELF_COORDINATE.value
C4 = ClauseId.C4_INTERFACE_NONEXPOSURE.value
C5 = ClauseId.C5_ACTION_CREDIT.value
C6 = ClauseId.C6_TEMPORAL_CLOSURE.value
C7 = ClauseId.C7_BINDING_RECOMBINATION.value
C8 = ClauseId.C8_VIABILITY_REPAIR.value
CLAUSES = (C1, C2, C3, C4, C5, C6, C7, C8)


def _clause(clause: str, assignment: dict[str, Any], resources: list[str]) -> dict[str, Any]:
    return {
        "clause": clause,
        "scope": list(assignment),
        "assignment": assignment,
        "essential_resources": resources,
    }


def package_model(*, model_id: str, code: int, label: str, variant: str) -> dict[str, Any]:
    if variant not in {"source", "target"}:
        raise ValueError(variant)
    token = "S" if variant == "source" else "T"
    predictive = f"predictive:{token}"
    epoch = 3 if variant == "source" else 7
    route = [f"route:{token}:0", f"route:{token}:1"]
    clauses = [
        _clause(
            C1,
            {
                "package_owner": code,
                "cross_predictive_tag": predictive,
                "object_token": f"object:{token}",
                "boundary_closed": True,
                "c1_audit_sealed": True,
            },
            [f"{token.lower()}-object-register", f"{token.lower()}-boundary"],
        ),
        _clause(
            C2,
            {
                "package_owner": code,
                "episode_epoch": epoch,
                "promotion_rank_before": 1,
                "promotion_rank_after": 2,
                "strict_test_pass": True,
                "promotion_audit_sealed": True,
            },
            [f"{token.lower()}-promotion-audit"],
        ),
        _clause(
            C3,
            {
                "package_owner": code,
                "cross_predictive_tag": predictive,
                "self_coordinate": f"self:{token}",
                "self_model_reflexive": True,
                "self_audit_sealed": True,
            },
            [f"{token.lower()}-self-register"],
        ),
        _clause(
            C4,
            {
                "package_owner": code,
                "public_shadow": "report:stable",
                "hidden_state_nonexposed": True,
                "interface_leak": False,
            },
            [f"{token.lower()}-private-state", f"{token.lower()}-public-interface"],
        ),
        _clause(
            C5,
            {
                "package_owner": code,
                "episode_epoch": epoch,
                "control_owner": code,
                "action_token": f"action:{token}:maintain",
                "action_credit_owner": code,
                "credit_source_internal": True,
                "credit_audit_sealed": True,
            },
            [f"{token.lower()}-policy", f"{token.lower()}-credit-ledger"],
        ),
        _clause(
            C6,
            {
                "package_owner": code,
                "cross_predictive_tag": predictive,
                "episode_epoch": epoch,
                "control_owner": code,
                "future_sufficient": True,
                "route_residue": route,
                "order_stable": True,
                "successor_total_on_viable": True,
                "tick_viable": True,
                "tick_phase": 1,
                "tick_progress": 1,
                "record_before": 3,
                "record_after": 4,
                "arrow_endogenous": True,
                "external_scheduler": False,
                "temporal_owner": code,
                "maintenance_owner": code,
            },
            [f"{token.lower()}-clock", f"{token.lower()}-record", f"{token.lower()}-maintenance"],
        ),
        _clause(
            C7,
            {
                "package_owner": code,
                "episode_epoch": epoch,
                "binding_integrated": True,
                "left_branch": f"{token}:L",
                "right_branch": f"{token}:R",
                "recombination_pairs": [[f"{token}:L", f"{token}:R"], [f"{token}:R", f"{token}:L"]],
                "recombination_relation_preserved": True,
                "joint_relation_tag": f"xor:{token}",
            },
            [f"{token.lower()}-binding-bus", f"{token.lower()}-recombination-table"],
        ),
        _clause(
            C8,
            {
                "package_owner": code,
                "control_owner": code,
                "viable": True,
                "repair_enabled": True,
                "repair_budget": 3,
                "repair_owner": code,
            },
            [f"{token.lower()}-repair-loop", f"{token.lower()}-budget"],
        ),
    ]
    global_assignment: dict[str, Any] = {}
    for item in clauses:
        for coord, value in item["assignment"].items():
            if coord in global_assignment and global_assignment[coord] != value:
                raise RuntimeError(f"positive model conflict at {coord}")
            global_assignment[coord] = value
    return {
        "schema_version": "CST-TT-02",
        "model_id": model_id,
        "target": {"code": code, "label": label},
        "package_vocabulary_id": f"finite-C-package-{variant}-v1",
        "clauses": clauses,
        "join_tree": {
            "root": C6,
            "edges": [{"child": clause, "parent": C6} for clause in CLAUSES if clause != C6],
        },
        "declared_global_assignment": dict(sorted(global_assignment.items())),
        "claim_lane": "S-R",
        "claim_ceiling": "finite structural target realization only",
    }


def source_package() -> dict[str, Any]:
    return package_model(model_id="PKG-POS-02-SOURCE", code=17, label="source-package-carrier", variant="source")


def target_package() -> dict[str, Any]:
    return package_model(model_id="PKG-POS-01-TARGET", code=101, label="independent-target-package-carrier", variant="target")


def _by_clause(model: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {item["clause"]: item for item in model["clauses"]}


def _resync_global(model: dict[str, Any]) -> None:
    global_assignment: dict[str, Any] = {}
    for item in model["clauses"]:
        for coord, value in item["assignment"].items():
            if coord not in global_assignment:
                global_assignment[coord] = value
    model["declared_global_assignment"] = dict(sorted(global_assignment.items()))


def staged_assembly(source: dict[str, Any], target: dict[str, Any]) -> dict[str, Any]:
    src = _by_clause(source)
    tgt = _by_clause(target)
    maps = []
    for clause in CLAUSES:
        entries = []
        for coord in src[clause]["scope"]:
            entries.append(
                {
                    "source_coordinate": coord,
                    "target_coordinate": coord,
                    "source_value": src[clause]["assignment"][coord],
                    "target_value": tgt[clause]["assignment"][coord],
                    "translation_attested": True,
                }
            )
        maps.append({"clause": clause, "entries": entries})
    return {
        "schema_version": "CST-TT-02",
        "assembly_id": "STG-POS-01",
        "source_vocabulary_id": source["package_vocabulary_id"],
        "target_vocabulary_id": target["package_vocabulary_id"],
        "separately_typed_carrier_vocabularies": True,
        "hard_gates_never_averaged": True,
        "clause_maps": maps,
        "claim_lanes": ["S-T", "S-R"],
        "claim_ceiling": "finite typed clause preservation and target assembly only",
    }


def package_controls(positive: dict[str, Any]) -> list[dict[str, Any]]:
    controls: list[dict[str, Any]] = []

    def add(control_id: str, title: str, primary: str, mutate, *, resync: bool = True) -> None:
        model = deepcopy(positive)
        model["model_id"] = control_id
        model["control_title"] = title
        model["expected_primary_failure"] = primary
        mutate(model)
        if resync:
            _resync_global(model)
        controls.append(model)

    add(
        "PC-01",
        "missing one required clause slot",
        "PKG-O01-exact-C1-C8-coverage",
        lambda model: (
            model.__setitem__("clauses", [item for item in model["clauses"] if item["clause"] != C1]),
            model["join_tree"].__setitem__("edges", [edge for edge in model["join_tree"]["edges"] if edge["child"] != C1]),
        ),
    )
    add("PC-02", "C1 object boundary failure", "PKG-O02-local-scope-and-clause-acceptance", lambda m: _by_clause(m)[C1]["assignment"].__setitem__("boundary_closed", False))
    add("PC-03", "C2 non-strict promotion", "PKG-O02-local-scope-and-clause-acceptance", lambda m: _by_clause(m)[C2]["assignment"].__setitem__("promotion_rank_after", 1))
    add("PC-04", "C3 non-reflexive self-coordinate", "PKG-O02-local-scope-and-clause-acceptance", lambda m: _by_clause(m)[C3]["assignment"].__setitem__("self_model_reflexive", False))
    add("PC-05", "C4 hidden-state exposure", "PKG-O02-local-scope-and-clause-acceptance", lambda m: _by_clause(m)[C4]["assignment"].__setitem__("hidden_state_nonexposed", False))
    add("PC-06", "C5 externally credited action", "PKG-O02-local-scope-and-clause-acceptance", lambda m: _by_clause(m)[C5]["assignment"].__setitem__("credit_source_internal", False))
    add("PC-07", "C6 stopped tick", "PKG-O08-substantive-C6-temporal-closure", lambda m: _by_clause(m)[C6]["assignment"].__setitem__("tick_progress", 0))
    add("PC-08", "C7 branchwise data without joint recombination", "PKG-O03-nonnegotiable-hard-gates", lambda m: _by_clause(m)[C7]["assignment"].__setitem__("recombination_relation_preserved", False))
    add("PC-09", "C8 viability failure", "PKG-O02-local-scope-and-clause-acceptance", lambda m: _by_clause(m)[C8]["assignment"].__setitem__("viable", False))
    add("PC-10", "tree-edge overlap conflict", "PKG-O06-edge-overlap-compatibility", lambda m: _by_clause(m)[C2]["assignment"].__setitem__("episode_epoch", 99), resync=False)
    add(
        "PC-11",
        "disconnected join-tree certificate",
        "PKG-O04-rooted-join-tree-shape",
        lambda m: m["join_tree"].__setitem__("edges", [edge for edge in m["join_tree"]["edges"] if edge["child"] != C4]),
    )

    def break_running_intersection(model: dict[str, Any]) -> None:
        by = _by_clause(model)
        by[C1]["assignment"]["cross_predictive_tag"] = "route:A"
        by[C3]["assignment"]["cross_predictive_tag"] = "route:B"
        by[C6]["assignment"].pop("cross_predictive_tag")
        by[C6]["scope"].remove("cross_predictive_tag")

    add("PC-12", "running-intersection break hides a nonedge conflict", "PKG-O05-running-intersection", break_running_intersection, resync=False)
    add(
        "PC-13",
        "declared global witness disagrees with every valid local restriction",
        "PKG-O07-global-gluing-and-restriction",
        lambda m: m["declared_global_assignment"].__setitem__("object_token", "wrong-global-token"),
        resync=False,
    )
    add("PC-14", "externally scheduled temporal shadow", "PKG-O08-substantive-C6-temporal-closure", lambda m: _by_clause(m)[C6]["assignment"].__setitem__("external_scheduler", True))

    def wrong_package_owner(model: dict[str, Any]) -> None:
        for item in model["clauses"]:
            item["assignment"]["package_owner"] = 999

    add("PC-15", "globally coherent package owned by the wrong carrier", "PKG-O09-target-local-package-ownership", wrong_package_owner)
    add("PC-16", "temporal maintenance owned by another carrier", "PKG-O08-substantive-C6-temporal-closure", lambda m: _by_clause(m)[C6]["assignment"].__setitem__("maintenance_owner", 999))
    add("PC-17", "verdict-loaded package record", "PKG-O10-verdict-field-separation", lambda m: m.__setitem__("lineage", "smuggled-verdict"))
    return controls


def staged_control(positive_assembly: dict[str, Any]) -> dict[str, Any]:
    control = deepcopy(positive_assembly)
    control["assembly_id"] = "SC-01"
    control["control_title"] = "one mapped target value is falsely attested"
    control["expected_primary_failure"] = "STG-O07-value-translation-soundness"
    entry = control["clause_maps"][1]["entries"][0]
    entry["target_value"] = "deliberately-wrong-target-value"
    return control


PACKAGE_OBLIGATIONS = [
    ("PKG-O01", "exact C1-C8 coverage", "Exactly one independently audited witness slot exists for every clause C1-C8."),
    ("PKG-O02", "local scope and clause acceptance", "Every local assignment exactly covers its declared scope and satisfies its clause-specific predicate."),
    ("PKG-O03", "nonnegotiable hard gates", "Every hard gate passes individually; no average or scalar score can compensate for a failed gate."),
    ("PKG-O04", "rooted join-tree shape", "The declared parent graph is connected, acyclic, rooted, and has exactly one parent per nonroot clause."),
    ("PKG-O05", "running intersection", "For every shared coordinate, all clauses containing it induce a connected subtree."),
    ("PKG-O06", "edge overlap compatibility", "Assignments agree on every coordinate shared across a join-tree edge."),
    ("PKG-O07", "global gluing and restriction", "A canonical global assignment exists, matches the declared witness, and restricts to every local assignment."),
    ("PKG-O08", "substantive C6 temporal closure", "C6 includes future sufficiency, stable order, available successor, viable progressing tick, endogenous arrow/record, retained route residue, no external scheduler, and target-local ownership."),
    ("PKG-O09", "target-local package ownership", "The package and temporal maintenance are owned by the declared target carrier."),
    ("PKG-O10", "verdict-field separation", "The integrated package record contains no ancestry, corridor, autonomy, consciousness, survival, or identity verdict."),
]

STAGED_OBLIGATIONS = [
    ("STG-O01", "source package valid"),
    ("STG-O02", "target package valid"),
    ("STG-O03", "distinct carrier types"),
    ("STG-O04", "exactly eight clause maps"),
    ("STG-O05", "separately typed vocabularies"),
    ("STG-O06", "total coordinate maps"),
    ("STG-O07", "value translation soundness"),
    ("STG-O08", "hard gates never averaged"),
    ("STG-O09", "target global assembly"),
    ("STG-O10", "no lineage or autonomy verdict fields"),
]
