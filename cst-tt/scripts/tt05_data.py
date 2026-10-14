from __future__ import annotations

from copy import deepcopy
from typing import Any, Mapping

from tt02_data import C1, C2, C3, C4, C5, C6, C7, C8, package_model, staged_assembly

SOURCE = {"code": 17, "label": "source-substrate"}
TARGET = {"code": 101, "label": "target-substrate"}
EXTERNAL = {"code": 901, "label": "external-support"}


def _by_clause(model: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {item["clause"]: item for item in model["clauses"]}


def _resync_global(model: dict[str, Any]) -> None:
    assignment: dict[str, Any] = {}
    for clause in model["clauses"]:
        for key, value in clause["assignment"].items():
            if key in assignment and assignment[key] != value:
                raise RuntimeError(f"package conflict at {key}")
            assignment[key] = value
    model["declared_global_assignment"] = dict(sorted(assignment.items()))


def _rename_resources(model: dict[str, Any], prefix: str) -> None:
    for clause in model["clauses"]:
        clause["essential_resources"] = [
            f"{prefix}-{resource.split('-', 1)[-1]}" for resource in clause["essential_resources"]
        ]


def aligned_source_package() -> dict[str, Any]:
    model = package_model(
        model_id="PKG-POS-03-FIACH-SOURCE",
        code=SOURCE["code"],
        label=SOURCE["label"],
        variant="source",
    )
    model["schema_version"] = "CST-TT-05-model-v1"
    model["package_vocabulary_id"] = "finite-C-package-fiach-source-v1"
    by = _by_clause(model)
    for clause in (C1, C3, C6):
        by[clause]["assignment"]["cross_predictive_tag"] = "predictive:S:rank0"
    for clause in (C2, C5, C6, C7):
        by[clause]["assignment"]["episode_epoch"] = 0
    by[C6]["assignment"].update(
        {
            "route_residue": ["route-root"],
            "tick_phase": 0,
            "tick_progress": 1,
            "record_before": 0,
            "record_after": 1,
        }
    )
    by[C8]["assignment"]["repair_budget"] = 1
    _rename_resources(model, "source")
    _resync_global(model)
    model["handoff_alignment"] = {
        "corridor_model_ref": "models/corridors/COR-POS-01.model.json",
        "corridor_stage": 0,
        "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"],
    }
    return model


def aligned_target_package() -> dict[str, Any]:
    model = package_model(
        model_id="PKG-POS-04-FIACH-TARGET",
        code=TARGET["code"],
        label=TARGET["label"],
        variant="target",
    )
    model["schema_version"] = "CST-TT-05-model-v1"
    model["package_vocabulary_id"] = "finite-C-package-fiach-target-v1"
    by = _by_clause(model)
    for clause in (C1, C3, C6):
        by[clause]["assignment"]["cross_predictive_tag"] = "predictive:T:rank2"
    for clause in (C2, C5, C6, C7):
        by[clause]["assignment"]["episode_epoch"] = 2
    by[C6]["assignment"].update(
        {
            "route_residue": ["route-root", "leg-S-T-mixed", "leg-S-T-target"],
            "tick_phase": 2,
            "tick_progress": 1,
            "record_before": 3,
            "record_after": 4,
        }
    )
    by[C8]["assignment"]["repair_budget"] = 1
    _rename_resources(model, "target")
    _resync_global(model)
    model["handoff_alignment"] = {
        "corridor_model_ref": "models/corridors/COR-POS-01.model.json",
        "corridor_stage": 2,
        "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"],
    }
    return model


def aligned_staged_assembly(source: dict[str, Any], target: dict[str, Any]) -> dict[str, Any]:
    model = staged_assembly(source, target)
    model["schema_version"] = "CST-TT-05-model-v1"
    model["assembly_id"] = "STG-POS-02-FIACH"
    model["handoff_alignment"] = {
        "corridor_model_ref": "models/corridors/COR-POS-01.model.json",
        "source_stage": 0,
        "target_stage": 2,
    }
    return model


def package_resources(target_package: Mapping[str, Any]) -> list[str]:
    resources: set[str] = set()
    for clause in target_package.get("clauses", []):
        if isinstance(clause, Mapping):
            values = clause.get("essential_resources", [])
            if isinstance(values, list):
                resources.update(str(value) for value in values)
    resources.update({"target-regenerator", "target-disturbance-sensor"})
    return sorted(resources)


def _resource(resource_id: str, owner: Mapping[str, Any], role: str) -> dict[str, Any]:
    return {"resource_id": resource_id, "owner": dict(owner), "role": role}


def _action(
    action_id: str,
    *,
    required: list[str],
    progress: int = 1,
    record: int = 1,
    cost: int = 0,
    regeneration: int = 0,
    owner: Mapping[str, Any] = TARGET,
    regeneration_resource: str | None = None,
    regeneration_owner: Mapping[str, Any] = TARGET,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "action_id": action_id,
        "owner": dict(owner),
        "required_resources": required,
        "progress_delta": progress,
        "record_delta": record,
        "budget_cost": cost,
        "budget_regeneration": regeneration,
    }
    if regeneration > 0 or regeneration_resource is not None:
        row["regeneration_resource"] = regeneration_resource or "target-regenerator"
        row["regeneration_owner"] = dict(regeneration_owner)
    return row


def positive_autonomy_model(
    *,
    package_certificate_ref: str,
    package_certificate_sha256: str,
    target_package: Mapping[str, Any],
) -> dict[str, Any]:
    retained_ids = package_resources(target_package)
    retained = [_resource(resource_id, TARGET, "target-internal") for resource_id in retained_ids]
    removed = [
        _resource("source-core", SOURCE, "source"),
        _resource("migration-bridge", EXTERNAL, "bridge"),
        _resource("migration-controller", EXTERNAL, "migration-controller"),
        _resource("external-decoder", EXTERNAL, "external-decoder"),
        _resource("external-scheduler", EXTERNAL, "external-scheduler"),
        _resource("external-repair", EXTERNAL, "undeclared-repair"),
    ]
    package_required = sorted(
        resource_id
        for resource_id in retained_ids
        if resource_id not in {"target-regenerator", "target-disturbance-sensor"}
    )
    states = [
        {
            "state_id": f"T-{health.upper()}-{phase}",
            "health": health,
            "tick_phase": phase,
            "budget": 1,
            "package_valid": True,
            "maintenance_owner": dict(TARGET),
            "required_resources": package_required,
            "public_state": "report:stable",
        }
        for health in ("safe", "warning")
        for phase in (0, 1)
    ]
    actions: list[dict[str, Any]] = []
    transitions: list[dict[str, Any]] = []
    for health in ("safe", "warning"):
        for phase in (0, 1):
            source = f"T-{health.upper()}-{phase}"
            next_phase = 1 - phase
            for disturbance in ("nominal", "hit"):
                if health == "safe" and disturbance == "nominal":
                    successor = f"T-SAFE-{next_phase}"
                    action_id = f"advance-{health}-{phase}-{disturbance}"
                    action = _action(
                        action_id,
                        required=["target-clock", "target-record", "target-maintenance"],
                    )
                elif health == "safe" and disturbance == "hit":
                    successor = f"T-WARNING-{next_phase}"
                    action_id = f"absorb-{health}-{phase}-{disturbance}"
                    action = _action(
                        action_id,
                        required=["target-clock", "target-record", "target-maintenance", "target-disturbance-sensor"],
                    )
                else:
                    successor = f"T-SAFE-{next_phase}"
                    action_id = f"repair-{health}-{phase}-{disturbance}"
                    action = _action(
                        action_id,
                        required=["target-clock", "target-record", "target-maintenance", "target-repair-loop", "target-regenerator"],
                        cost=1,
                        regeneration=1,
                        regeneration_resource="target-regenerator",
                    )
                actions.append(action)
                transitions.append(
                    {
                        "from_state": source,
                        "disturbance_id": disturbance,
                        "action_id": action_id,
                        "to_state": successor,
                    }
                )
    return {
        "schema_version": "CST-TT-05-model-v1",
        "model_id": "AUT-POS-01",
        "title": "target-owned post-withdrawal temporal package controller",
        "source": dict(SOURCE),
        "target": dict(TARGET),
        "boundary": {
            "boundary_id": "target-boundary-v1",
            "fixed_before_evaluation": True,
            "disturbance_class_id": "nominal-or-single-hit",
            "disturbance_class_fixed_before_evaluation": True,
        },
        "withdrawal": {
            "removed_resources": removed,
            "retained_resources": retained,
            "source_removed": True,
            "bridge_removed": True,
            "migration_controller_removed": True,
            "external_decoder_removed": True,
            "external_scheduler_removed": True,
            "undeclared_repair_removed": True,
        },
        "package_contract": {
            "package_certificate_ref": package_certificate_ref,
            "package_certificate_sha256": package_certificate_sha256,
            "package_owner": TARGET["code"],
            "package_predicate_id": "PKG-POS-04-FIACH-TARGET::IntegratedPkg",
        },
        "handoff_endpoint_event_id": "t-exit",
        "endpoint_state_id": "T-SAFE-0",
        "declared_invariant_state_ids": sorted(state["state_id"] for state in states),
        "tick_modulus": 2,
        "finite_horizon": 6,
        "disturbances": [
            {"disturbance_id": "nominal", "predeclared": True},
            {"disturbance_id": "hit", "predeclared": True},
        ],
        "states": states,
        "actions": actions,
        "transitions": transitions,
        "supported_public_trace": ["report:stable"] * 7,
        "claim_lane": "A",
        "claim_ceiling": "model-relative post-withdrawal autonomy over the declared disturbance class",
        "nonclaims": [
            "no source-target lineage conclusion",
            "no consciousness or felt-continuity conclusion",
            "no indefinite physical persistence outside the model",
        ],
    }


def autonomy_controls(positive: dict[str, Any]) -> list[dict[str, Any]]:
    controls: list[dict[str, Any]] = []

    def add(control_id: str, title: str, expected: str, mutate) -> None:
        model = deepcopy(positive)
        model["model_id"] = control_id
        model["title"] = title
        model["expected_primary_failure"] = expected
        mutate(model)
        controls.append(model)

    add(
        "AUT-C01",
        "external decoder/scheduler/repair shadow collapses after withdrawal",
        "AUT-O11-target-owned-total-response-law",
        lambda m: [
            action.update(
                {
                    "owner": dict(EXTERNAL),
                    "required_resources": ["external-decoder", "external-scheduler", "external-repair"],
                }
            )
            for action in m["actions"]
        ],
    )
    add(
        "AUT-C02",
        "withdrawal leaves the scheduler in place",
        "AUT-O04-withdrawal-shape-and-completeness",
        lambda m: m["withdrawal"].__setitem__("external_scheduler_removed", False),
    )
    add(
        "AUT-C03",
        "removed and retained resources overlap",
        "AUT-O04-withdrawal-shape-and-completeness",
        lambda m: m["withdrawal"]["retained_resources"].append(_resource("external-scheduler", TARGET, "target-internal")),
    )
    add(
        "AUT-C04",
        "one response action is owned by the migration controller",
        "AUT-O11-target-owned-total-response-law",
        lambda m: m["actions"][0].__setitem__("owner", dict(EXTERNAL)),
    )
    add(
        "AUT-C05",
        "stable self-loop has no tick or record progress",
        "AUT-O12-anti-stall-progress-and-arrow",
        lambda m: [
            m.__setitem__("states", [deepcopy(m["states"][0])]),
            m["states"][0].__setitem__("state_id", "T-STALL-0"),
            m.__setitem__("endpoint_state_id", "T-STALL-0"),
            m.__setitem__("declared_invariant_state_ids", ["T-STALL-0"]),
            m.__setitem__("disturbances", [{"disturbance_id": "nominal", "predeclared": True}]),
            m.__setitem__("actions", [_action("stall", required=["target-clock"], progress=0, record=0)]),
            m.__setitem__("transitions", [{"from_state": "T-STALL-0", "disturbance_id": "nominal", "action_id": "stall", "to_state": "T-STALL-0"}]),
        ],
    )

    def budget_failure(model: dict[str, Any]) -> None:
        base_required = model["states"][0]["required_resources"]
        model["states"] = [
            {
                "state_id": "B2",
                "health": "warning",
                "tick_phase": 0,
                "budget": 2,
                "package_valid": True,
                "maintenance_owner": dict(TARGET),
                "required_resources": base_required,
                "public_state": "report:stable",
            },
            {
                "state_id": "B1",
                "health": "warning",
                "tick_phase": 1,
                "budget": 1,
                "package_valid": True,
                "maintenance_owner": dict(TARGET),
                "required_resources": base_required,
                "public_state": "report:stable",
            },
            {
                "state_id": "B0",
                "health": "failed",
                "tick_phase": 0,
                "budget": 0,
                "package_valid": False,
                "maintenance_owner": dict(TARGET),
                "required_resources": base_required,
                "public_state": "report:stable",
            },
        ]
        model["endpoint_state_id"] = "B2"
        model["declared_invariant_state_ids"] = []
        model["disturbances"] = [{"disturbance_id": "nominal", "predeclared": True}]
        model["actions"] = [
            _action("spend-B2", required=["target-maintenance"], cost=1),
            _action("spend-B1", required=["target-maintenance"], cost=1),
            _action("stuck-B0", required=["target-maintenance"], progress=0, record=0),
        ]
        model["transitions"] = [
            {"from_state": "B2", "disturbance_id": "nominal", "action_id": "spend-B2", "to_state": "B1"},
            {"from_state": "B1", "disturbance_id": "nominal", "action_id": "spend-B1", "to_state": "B0"},
            {"from_state": "B0", "disturbance_id": "nominal", "action_id": "stuck-B0", "to_state": "B0"},
        ]
        model["finite_horizon"] = 1

    add("AUT-C06", "finite prefix followed by target-budget insolvency", "AUT-O08-endpoint-in-computed-controlled-invariant", budget_failure)
    add(
        "AUT-C07",
        "declared invariant includes a package-invalid state",
        "AUT-O09-declared-invariant-is-maximal-fixed-point",
        lambda m: [
            m["states"].append(
                {
                    "state_id": "T-FAILED",
                    "health": "failed",
                    "tick_phase": 0,
                    "budget": 0,
                    "package_valid": False,
                    "maintenance_owner": dict(TARGET),
                    "required_resources": [],
                    "public_state": "report:stable",
                }
            ),
            m["declared_invariant_state_ids"].append("T-FAILED"),
        ],
    )
    add(
        "AUT-C08",
        "allowed hit disturbance has no response from one invariant state",
        "AUT-O08-endpoint-in-computed-controlled-invariant",
        lambda m: m.__setitem__(
            "transitions",
            [
                row
                for row in m["transitions"]
                if not (row["from_state"] == "T-SAFE-0" and row["disturbance_id"] == "hit")
            ],
        ),
    )
    add(
        "AUT-C09",
        "disturbance class chosen after evaluating the target",
        "AUT-O03-disturbance-class-fixed-before-evaluation",
        lambda m: m["boundary"].__setitem__("disturbance_class_fixed_before_evaluation", False),
    )
    add(
        "AUT-C10",
        "maintenance ownership remains external",
        "AUT-O10-package-and-resource-closure",
        lambda m: m["states"][0].__setitem__("maintenance_owner", dict(EXTERNAL)),
    )
    add(
        "AUT-C11",
        "retained maintenance resource is external-owned",
        "AUT-O05-target-owned-retained-resources",
        lambda m: m["withdrawal"]["retained_resources"][0].__setitem__("owner", dict(EXTERNAL)),
    )
    add(
        "AUT-C12",
        "verdict-loaded autonomy record",
        "AUT-O15-verdict-field-separation",
        lambda m: m.__setitem__("lineage", "smuggled-success"),
    )
    return controls


def fiach_lane_control_specs(
    *,
    source_package_ref: str,
    staged_ref: str,
    positive_package_ref: str,
    negative_package_ref: str,
    positive_corridor_ref: str,
    negative_corridor_ref: str,
    positive_autonomy_ref: str,
    negative_autonomy_ref: str,
) -> list[dict[str, Any]]:
    combinations = [
        ("FIACH-C01", "package only", True, False, False),
        ("FIACH-C02", "lineage only", False, True, False),
        ("FIACH-C03", "autonomy only", False, False, True),
        ("FIACH-C04", "package plus lineage", True, True, False),
        ("FIACH-C05", "package plus autonomy", True, False, True),
        ("FIACH-C06", "lineage plus autonomy", False, True, True),
    ]
    rows: list[dict[str, Any]] = []
    for control_id, title, package, corridor, autonomy in combinations:
        rows.append(
            {
                "schema_version": "CST-TT-05-model-v1",
                "certificate_id": control_id,
                "title": title,
                "source": dict(SOURCE),
                "target": dict(TARGET),
                "component_refs": {
                    "source_package": source_package_ref,
                    "staged_assembly": staged_ref,
                    "target_package": positive_package_ref if package else negative_package_ref,
                    "corridor": positive_corridor_ref if corridor else negative_corridor_ref,
                    "autonomy": positive_autonomy_ref if autonomy else negative_autonomy_ref,
                },
                "expected_lane_statuses": {"S-R": package, "S-L": corridor, "A": autonomy},
                "route_status": "route-indexed",
                "recognition_status": "not-addressed",
                "claim_ceiling": "lane-independence control only",
            }
        )
    return rows
