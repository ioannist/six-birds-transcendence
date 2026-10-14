from __future__ import annotations

from copy import deepcopy
from typing import Any, Mapping

from tt02_data import C1, C2, C3, C4, C5, C6, C7, C8, package_model, staged_assembly
from tt04_data import atomic_corridor_model, positive_composition_left, positive_composition_right
from cst_tt.corridor import compose_corridor_models

SOURCE = {"code": 17, "label": "source-substrate"}
MIDDLE = {"code": 55, "label": "intermediate-substrate"}
TARGET = {"code": 101, "label": "target-substrate"}
LEFT = {"code": 201, "label": "left-branch-substrate"}
RIGHT = {"code": 202, "label": "right-branch-substrate"}
FUSION_LEFT = {"code": 301, "label": "fusion-left-source"}
FUSION_RIGHT = {"code": 302, "label": "fusion-right-source"}
FUSED = {"code": 303, "label": "fused-target-substrate"}
EXTERNAL = {"code": 901, "label": "external-support"}


def _code(value: Mapping[str, Any]) -> int:
    return int(value["code"])


def _by_clause(model: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(item["clause"]): item for item in model["clauses"]}


def _resync_global(model: dict[str, Any]) -> None:
    assignment: dict[str, Any] = {}
    for clause in model["clauses"]:
        for key, value in clause["assignment"].items():
            if key in assignment and assignment[key] != value:
                raise RuntimeError(f"package conflict at {key}: {assignment[key]!r} != {value!r}")
            assignment[key] = value
    model["declared_global_assignment"] = dict(sorted(assignment.items()))


def _stage(model: Mapping[str, Any], index: int) -> Mapping[str, Any]:
    return model["episode"]["stages"][index]


def aligned_package(
    *,
    model_id: str,
    carrier: Mapping[str, Any],
    symbol: str,
    resource_prefix: str,
    stage_signature: Mapping[str, Any],
    alignments: list[dict[str, Any]],
) -> dict[str, Any]:
    code = _code(carrier)
    model = package_model(
        model_id=model_id,
        code=code,
        label=str(carrier["label"]),
        variant="target",
    )
    model["schema_version"] = "CST-TT-06-model-v1"
    model["package_vocabulary_id"] = f"finite-C-package-{symbol.lower()}-v1"
    by = _by_clause(model)
    rank = int(stage_signature["predictive_rank"])
    predictive = f"predictive:{symbol}:rank{rank}"
    epoch = int(stage_signature["tick_index"])
    for clause in (C1, C3, C6):
        by[clause]["assignment"]["cross_predictive_tag"] = predictive
    for clause in (C2, C5, C6, C7):
        by[clause]["assignment"]["episode_epoch"] = epoch
    for clause in model["clauses"]:
        assignment = clause["assignment"]
        for key in (
            "package_owner",
            "control_owner",
            "action_credit_owner",
            "temporal_owner",
            "maintenance_owner",
            "repair_owner",
        ):
            if key in assignment:
                assignment[key] = code
        clause["essential_resources"] = [
            f"{resource_prefix}-{resource.split('-', 1)[-1]}"
            for resource in clause["essential_resources"]
        ]
    by[C1]["assignment"]["object_token"] = f"object:{symbol}"
    by[C3]["assignment"]["self_coordinate"] = f"self:{symbol}"
    by[C5]["assignment"]["action_token"] = f"action:{symbol}:maintain"
    by[C6]["assignment"].update(
        {
            "route_residue": list(stage_signature["route_residue"]),
            "tick_phase": int(stage_signature["tick_index"]),
            "tick_progress": 1,
            "record_before": int(stage_signature["record_value"]),
            "record_after": int(stage_signature["record_value"]) + 1,
            "future_sufficient": True,
            "order_stable": True,
            "successor_total_on_viable": True,
            "tick_viable": True,
            "arrow_endogenous": True,
            "external_scheduler": False,
        }
    )
    by[C2]["assignment"].update(
        {
            "promotion_rank_before": rank,
            "promotion_rank_after": rank + 1,
            "strict_test_pass": True,
            "promotion_audit_sealed": True,
        }
    )
    by[C7]["assignment"].update(
        {
            "left_branch": f"{symbol}:L",
            "right_branch": f"{symbol}:R",
            "recombination_pairs": [[f"{symbol}:L", f"{symbol}:R"], [f"{symbol}:R", f"{symbol}:L"]],
            "joint_relation_tag": f"xor:{symbol}",
            "binding_integrated": True,
            "recombination_relation_preserved": True,
        }
    )
    by[C8]["assignment"].update({"repair_budget": 1, "viable": True, "repair_enabled": True})
    model["handoff_alignments"] = deepcopy(alignments)
    model["handoff_alignment"] = deepcopy(alignments[0])
    model["claim_ceiling"] = "finite structural package aligned to declared temporal frontier(s)"
    _resync_global(model)
    return model


def composition_corridors() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    left = positive_composition_left()
    right = positive_composition_right()
    composite = compose_corridor_models(
        left,
        right,
        model_id="COR-POS-03-FULL-COMPOSITE",
        title="two-hop strict temporal carrier-chain corridor for full FIACH composition",
    )
    composite["schema_version"] = "CST-TT-06-model-v1"
    return left, right, composite


def composition_packages(
    left_corridor: Mapping[str, Any],
    right_corridor: Mapping[str, Any],
    composite_corridor: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    source = aligned_package(
        model_id="PKG-POS-05-COMP-SOURCE",
        carrier=SOURCE,
        symbol="S0",
        resource_prefix="source-comp",
        stage_signature=_stage(left_corridor, 0)["signature"],
        alignments=[
            {
                "corridor_model_ref": "models/corridors/COR-POS-02A.model.json",
                "corridor_stage": 0,
                "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"],
            },
            {
                "corridor_model_ref": "models/corridors/COR-POS-03-FULL-COMPOSITE.model.json",
                "corridor_stage": 0,
                "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"],
            },
        ],
    )
    middle = aligned_package(
        model_id="PKG-POS-06-COMP-MIDDLE",
        carrier=MIDDLE,
        symbol="M1",
        resource_prefix="middle-comp",
        stage_signature=_stage(left_corridor, -1)["signature"],
        alignments=[
            {
                "corridor_model_ref": "models/corridors/COR-POS-02A.model.json",
                "corridor_stage": 2,
                "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"],
            },
            {
                "corridor_model_ref": "models/corridors/COR-POS-02B.model.json",
                "corridor_stage": 0,
                "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"],
            },
            {
                "corridor_model_ref": "models/corridors/COR-POS-03-FULL-COMPOSITE.model.json",
                "corridor_stage": 2,
                "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"],
            },
        ],
    )
    target = aligned_package(
        model_id="PKG-POS-07-COMP-TARGET",
        carrier=TARGET,
        symbol="T2",
        resource_prefix="target-comp",
        stage_signature=_stage(right_corridor, -1)["signature"],
        alignments=[
            {
                "corridor_model_ref": "models/corridors/COR-POS-02B.model.json",
                "corridor_stage": 2,
                "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"],
            },
            {
                "corridor_model_ref": "models/corridors/COR-POS-03-FULL-COMPOSITE.model.json",
                "corridor_stage": 4,
                "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"],
            },
        ],
    )
    return source, middle, target


def staged_with_id(source: dict[str, Any], target: dict[str, Any], assembly_id: str) -> dict[str, Any]:
    assembly = staged_assembly(source, target)
    assembly["schema_version"] = "CST-TT-06-model-v1"
    assembly["assembly_id"] = assembly_id
    assembly["composition_role"] = "full-handoff-composable"
    return assembly


def _package_resources(target_package: Mapping[str, Any]) -> list[str]:
    resources: set[str] = set()
    for clause in target_package.get("clauses", []):
        if isinstance(clause, Mapping):
            values = clause.get("essential_resources", [])
            if isinstance(values, list):
                resources.update(str(value) for value in values)
    return sorted(resources)


def _resource(resource_id: str, owner: Mapping[str, Any], role: str) -> dict[str, Any]:
    return {"resource_id": resource_id, "owner": dict(owner), "role": role}


def positive_autonomy(
    *,
    model_id: str,
    source: Mapping[str, Any],
    target: Mapping[str, Any],
    target_package: Mapping[str, Any],
    package_certificate_ref: str,
    package_certificate_sha256: str,
    handoff_endpoint_event_id: str,
    prefix: str,
) -> dict[str, Any]:
    target_code = _code(target)
    retained_ids = _package_resources(target_package)
    regenerator = f"{prefix}-regenerator"
    sensor = f"{prefix}-disturbance-sensor"
    retained_ids = sorted(set(retained_ids) | {regenerator, sensor})
    retained = [_resource(resource_id, target, "target-internal") for resource_id in retained_ids]
    removed = [
        _resource(f"{prefix}-upstream-source", source, "source"),
        _resource(f"{prefix}-migration-bridge", EXTERNAL, "bridge"),
        _resource(f"{prefix}-migration-controller", EXTERNAL, "migration-controller"),
        _resource(f"{prefix}-external-decoder", EXTERNAL, "external-decoder"),
        _resource(f"{prefix}-external-scheduler", EXTERNAL, "external-scheduler"),
        _resource(f"{prefix}-external-repair", EXTERNAL, "undeclared-repair"),
    ]
    package_required = sorted(resource for resource in retained_ids if resource not in {regenerator, sensor})
    states = [
        {
            "state_id": f"{prefix.upper()}-{health.upper()}-{phase}",
            "health": health,
            "tick_phase": phase,
            "budget": 1,
            "package_valid": True,
            "maintenance_owner": dict(target),
            "required_resources": package_required,
            "public_state": "report:stable",
        }
        for health in ("safe", "warning")
        for phase in (0, 1)
    ]
    actions: list[dict[str, Any]] = []
    transitions: list[dict[str, Any]] = []
    core_clock = next(resource for resource in retained_ids if resource.endswith("-clock"))
    core_record = next(resource for resource in retained_ids if resource.endswith("-record"))
    core_maintenance = next(resource for resource in retained_ids if resource.endswith("-maintenance"))
    repair_loop = next(resource for resource in retained_ids if resource.endswith("-repair-loop"))
    for health in ("safe", "warning"):
        for phase in (0, 1):
            source_state = f"{prefix.upper()}-{health.upper()}-{phase}"
            next_phase = 1 - phase
            for disturbance in ("nominal", "hit"):
                if health == "safe" and disturbance == "nominal":
                    successor = f"{prefix.upper()}-SAFE-{next_phase}"
                    required = [core_clock, core_record, core_maintenance]
                    cost = regeneration = 0
                elif health == "safe":
                    successor = f"{prefix.upper()}-WARNING-{next_phase}"
                    required = [core_clock, core_record, core_maintenance, sensor]
                    cost = regeneration = 0
                else:
                    successor = f"{prefix.upper()}-SAFE-{next_phase}"
                    required = [core_clock, core_record, core_maintenance, repair_loop, regenerator]
                    cost = regeneration = 1
                action_id = f"{prefix}-{health}-{phase}-{disturbance}"
                action: dict[str, Any] = {
                    "action_id": action_id,
                    "owner": dict(target),
                    "required_resources": required,
                    "progress_delta": 1,
                    "record_delta": 1,
                    "budget_cost": cost,
                    "budget_regeneration": regeneration,
                }
                if regeneration:
                    action["regeneration_resource"] = regenerator
                    action["regeneration_owner"] = dict(target)
                actions.append(action)
                transitions.append(
                    {
                        "from_state": source_state,
                        "disturbance_id": disturbance,
                        "action_id": action_id,
                        "to_state": successor,
                    }
                )
    return {
        "schema_version": "CST-TT-06-model-v1",
        "model_id": model_id,
        "title": f"{prefix} target-owned post-withdrawal controller",
        "source": dict(source),
        "target": dict(target),
        "boundary": {
            "boundary_id": f"{prefix}-boundary-v1",
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
            "package_owner": target_code,
            "package_predicate_id": f"{target_package['model_id']}::IntegratedPkg",
        },
        "handoff_endpoint_event_id": handoff_endpoint_event_id,
        "endpoint_state_id": f"{prefix.upper()}-SAFE-0",
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
        "claim_ceiling": "model-relative post-withdrawal autonomy over the declared finite disturbance class",
        "nonclaims": [
            "no consciousness or felt-continuity conclusion",
            "no personal survival or numerical identity conclusion",
            "no indefinite physical persistence outside the model",
        ],
    }


def fission_corridors() -> tuple[dict[str, Any], dict[str, Any]]:
    left = atomic_corridor_model(
        "COR-FIS-LEFT",
        SOURCE,
        LEFT,
        base_rank=0,
        base_record=0,
        start_route=["fission-root"],
        start_event_id="fission-source-entry",
        boundary_event_id="fission-left-exit",
        leg_id="leg-S-L",
        title="left branch of symmetric temporal fission",
    )
    right = atomic_corridor_model(
        "COR-FIS-RIGHT",
        SOURCE,
        RIGHT,
        base_rank=0,
        base_record=0,
        start_route=["fission-root"],
        start_event_id="fission-source-entry",
        boundary_event_id="fission-right-exit",
        leg_id="leg-S-R",
        title="right branch of symmetric temporal fission",
    )
    left["schema_version"] = right["schema_version"] = "CST-TT-06-model-v1"
    # The fork has one exact source frontier; branch asymmetry begins only after the split.
    right["episode"]["stages"][0]["signature"] = deepcopy(left["episode"]["stages"][0]["signature"])
    return left, right


def fission_packages(left_corridor: Mapping[str, Any], right_corridor: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    source = aligned_package(
        model_id="PKG-FIS-SOURCE",
        carrier=SOURCE,
        symbol="FS",
        resource_prefix="fission-source",
        stage_signature=_stage(left_corridor, 0)["signature"],
        alignments=[
            {"corridor_model_ref": "models/fission/COR-FIS-LEFT.model.json", "corridor_stage": 0, "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"]},
            {"corridor_model_ref": "models/fission/COR-FIS-RIGHT.model.json", "corridor_stage": 0, "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"]},
        ],
    )
    left = aligned_package(
        model_id="PKG-FIS-LEFT",
        carrier=LEFT,
        symbol="FB",
        resource_prefix="fission-branch",
        stage_signature=_stage(left_corridor, -1)["signature"],
        alignments=[{"corridor_model_ref": "models/fission/COR-FIS-LEFT.model.json", "corridor_stage": 2, "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"]}],
    )
    right = aligned_package(
        model_id="PKG-FIS-RIGHT",
        carrier=RIGHT,
        symbol="FB",
        resource_prefix="fission-branch",
        stage_signature=_stage(right_corridor, -1)["signature"],
        alignments=[{"corridor_model_ref": "models/fission/COR-FIS-RIGHT.model.json", "corridor_stage": 2, "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"]}],
    )
    return source, left, right


def fusion_corridors() -> tuple[dict[str, Any], dict[str, Any]]:
    left = atomic_corridor_model(
        "COR-FUS-LEFT",
        FUSION_LEFT,
        FUSED,
        base_rank=0,
        base_record=0,
        start_route=["fusion-left-root"],
        start_event_id="fusion-left-entry",
        boundary_event_id="fusion-target-left-arrival",
        leg_id="leg-FL-F",
        title="left temporal lineage into a fused target",
    )
    right = atomic_corridor_model(
        "COR-FUS-RIGHT",
        FUSION_RIGHT,
        FUSED,
        base_rank=0,
        base_record=0,
        start_route=["fusion-right-root"],
        start_event_id="fusion-right-entry",
        boundary_event_id="fusion-target-right-arrival",
        leg_id="leg-FR-F",
        title="right temporal lineage into a fused target",
    )
    left["schema_version"] = right["schema_version"] = "CST-TT-06-model-v1"
    return left, right


def fusion_target_packages(left_corridor: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    positive = aligned_package(
        model_id="PKG-FUS-CONTROL-VALID",
        carrier=FUSED,
        symbol="FUSED",
        resource_prefix="fused-target",
        stage_signature=_stage(left_corridor, -1)["signature"],
        alignments=[{"corridor_model_ref": "models/fusion/COR-FUS-LEFT.model.json", "corridor_stage": 2, "alignment_fields": ["route_residue", "tick_phase", "record_before", "maintenance_owner"]}],
    )
    negative = deepcopy(positive)
    negative["model_id"] = "PKG-FUS-NEG-01"
    negative["fusion_inputs"] = [deepcopy(FUSION_LEFT), deepcopy(FUSION_RIGHT)]
    negative["expected_failures"] = ["C5_ACTION_CREDIT", "C7_BINDING_RECOMBINATION"]
    by = _by_clause(negative)
    by[C5]["assignment"]["action_credit_owner"] = _code(FUSION_LEFT)
    by[C5]["assignment"]["credit_source_internal"] = False
    by[C7]["assignment"]["recombination_relation_preserved"] = False
    by[C7]["assignment"]["joint_relation_tag"] = ""
    _resync_global(negative)
    return negative, positive


def toy_feature_rows() -> list[dict[str, Any]]:
    # Public and endpoint signatures are intentionally coarse; structural signatures retain the audited discriminators.
    return [
        {"toy_id": "TTM-01", "public_signature": "stable-report", "endpoint_signature": "package-autonomous", "structural_signature": [1, 1, 1, 0, 1]},
        {"toy_id": "TTM-02", "public_signature": "stable-report", "endpoint_signature": "package-autonomous", "structural_signature": [1, 0, 1, 0, 1]},
        {"toy_id": "TTM-03", "public_signature": "stable-report", "endpoint_signature": "temporal-successor", "structural_signature": [0, 1, 0, 0, 1]},
        {"toy_id": "TTM-04", "public_signature": "stable-report", "endpoint_signature": "runtime-progress", "structural_signature": [1, 0, 0, 0, 0]},
        {"toy_id": "TTM-05", "public_signature": "same-boundary", "endpoint_signature": "route-endpoint", "structural_signature": [0, 0, 0, 0, 0]},
        {"toy_id": "TTM-06", "public_signature": "same-boundary", "endpoint_signature": "route-endpoint", "structural_signature": [0, 0, 0, 1, 1]},
        {"toy_id": "TTM-07", "public_signature": "symmetric-report", "endpoint_signature": "two-valid-targets", "structural_signature": [1, 1, 1, 0, 1]},
        {"toy_id": "TTM-08", "public_signature": "stable-report", "endpoint_signature": "temporal-successor", "structural_signature": [0, 0, 0, 0, 1]},
        {"toy_id": "TTM-09", "public_signature": "stable-report", "endpoint_signature": "stable-state", "structural_signature": [1, 0, 0, 0, 0]},
        {"toy_id": "TTM-10", "public_signature": "stable-report", "endpoint_signature": "finite-prefix", "structural_signature": [1, 0, 0, 0, 0]},
        {"toy_id": "TTM-11", "public_signature": "all-local-pass", "endpoint_signature": "package-candidate", "structural_signature": [0, 0, 0, 0, 0]},
        {"toy_id": "TTM-12", "public_signature": "stable-report", "endpoint_signature": "public-match", "structural_signature": [0, 0, 0, 0, 0]},
        {"toy_id": "TTM-13", "public_signature": "small-residual", "endpoint_signature": "near-match", "structural_signature": [0, 0, 0, 0, 0]},
    ]
