from __future__ import annotations

import copy
import hashlib
import json
from typing import Any, Callable


SOURCE = {"code": 17, "label": "source-substrate"}
MIDDLE = {"code": 55, "label": "intermediate-substrate"}
TARGET = {"code": 101, "label": "target-substrate"}
BRIDGE = {"code": 999, "label": "archival-mediator"}


def canonical_hash(value: object) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def signature(rank: int, record: int, owner: int, route: list[str], maintenance: str) -> dict[str, Any]:
    return {
        "predictive_rank": rank,
        "order_rank": rank,
        "tick_index": rank,
        "progress_rank": rank,
        "record_value": record,
        "route_residue": route,
        "maintenance_owner": owner,
        "maintenance_state": maintenance,
    }


def stage(index: int, support: list[dict[str, Any]], sig: dict[str, Any], *, realized: bool = True) -> dict[str, Any]:
    return {
        "stage": index,
        "active_support": copy.deepcopy(support),
        "temporal_realized": realized,
        "signature": copy.deepcopy(sig),
    }


def event(event_id: str, owner: dict[str, Any], at: int) -> dict[str, Any]:
    return {
        "event_id": event_id,
        "owner": copy.deepcopy(owner),
        "stage": at,
        "event_kind": "temporal-update",
    }


def dependency(parent: str, child: str, kind: str = "temporal-step") -> dict[str, Any]:
    return {
        "parent_event_id": parent,
        "child_event_id": child,
        "dependency_kind": kind,
    }


def atomic_corridor_model(
    model_id: str,
    source: dict[str, Any],
    target: dict[str, Any],
    *,
    base_rank: int,
    base_record: int,
    start_route: list[str],
    start_event_id: str,
    boundary_event_id: str,
    leg_id: str,
    title: str,
) -> dict[str, Any]:
    source_code = int(source["code"])
    target_code = int(target["code"])
    mixed_route = [*start_route, f"{leg_id}-mixed"]
    end_route = [*mixed_route, f"{leg_id}-target"]
    start_sig = signature(base_rank, base_record, source_code, start_route, f"{leg_id}-source-maint")
    mixed_sig = signature(base_rank + 1, base_record + 1, source_code, mixed_route, f"{leg_id}-mixed-maint")
    end_sig = signature(base_rank + 2, base_record + 3, target_code, end_route, f"{leg_id}-target-maint")
    source_mixed = f"{leg_id}-source-mixed"
    target_mixed = f"{leg_id}-target-mixed"
    return {
        "schema_version": "CST-TT-04-model-v1",
        "model_id": model_id,
        "title": title,
        "kind": "atomic-overlap-temporal-corridor",
        "claim_lanes": ["S-L"],
        "claim_ceiling": "exact finite structural temporal lineage criterion only",
        "carrier_chain": [copy.deepcopy(source), copy.deepcopy(target)],
        "episode": {
            "stages": [
                stage(0, [source], start_sig),
                stage(1, [source, target], mixed_sig),
                stage(2, [target], end_sig),
            ],
            "events": [
                event(start_event_id, source, 0),
                event(source_mixed, source, 1),
                event(target_mixed, target, 1),
                event(boundary_event_id, target, 2),
            ],
            "dependencies": [
                dependency(start_event_id, source_mixed),
                dependency(start_event_id, target_mixed),
                dependency(source_mixed, boundary_event_id, "mixed-update"),
                dependency(target_mixed, boundary_event_id, "mixed-update"),
            ],
        },
        "legs": [
            {
                "leg_id": leg_id,
                "source_carrier": copy.deepcopy(source),
                "target_carrier": copy.deepcopy(target),
                "start_stage": 0,
                "mixed_stage": 1,
                "audit_later_stage": 2,
                "takeover_stage": 2,
                "end_stage": 2,
                "route_status": "route-indexed",
                "transport_evidence": {
                    "evidence_id": f"{leg_id}-bundled-transport",
                    "components": [
                        "predictive-now",
                        "order",
                        "tick-phase",
                        "progress",
                        "arrow-record",
                        "route-memory",
                        "maintenance",
                    ],
                    "representative_independent": True,
                    "ownership_interface_valid": True,
                    "route_status": "route-indexed",
                },
                "counterfactual": {
                    "projection_fields": ["predictive_rank", "tick_index", "record_value"],
                    "base_projection": [base_rank, base_rank, base_record],
                    "source_contribution": [1, 0, 1],
                    "target_contribution": [1, 2, 2],
                    "full_projection": [base_rank + 2, base_rank + 2, base_record + 3],
                    "source_removed_projection": [base_rank + 1, base_rank + 2, base_record + 2],
                    "target_removed_projection": [base_rank + 1, base_rank, base_record + 1],
                },
                "audit_event_ids": {
                    "source_mixed_event": source_mixed,
                    "target_mixed_event": target_mixed,
                    "later_event": boundary_event_id,
                },
            }
        ],
        "nonclaims": [
            "no target-package verdict",
            "no post-withdrawal autonomy verdict",
            "no phenomenal or personal-status conclusion",
        ],
    }


def positive_atomic_corridor() -> dict[str, Any]:
    return atomic_corridor_model(
        "COR-POS-01",
        SOURCE,
        TARGET,
        base_rank=0,
        base_record=0,
        start_route=["route-root"],
        start_event_id="s-entry",
        boundary_event_id="t-exit",
        leg_id="leg-S-T",
        title="strict atomic overlap temporal corridor",
    )


def positive_composition_left() -> dict[str, Any]:
    return atomic_corridor_model(
        "COR-POS-02A",
        SOURCE,
        MIDDLE,
        base_rank=0,
        base_record=0,
        start_route=["route-root"],
        start_event_id="s-chain-entry",
        boundary_event_id="m-boundary",
        leg_id="leg-S-M",
        title="left strict overlap leg for composition",
    )


def positive_composition_right() -> dict[str, Any]:
    left = positive_composition_left()
    boundary = copy.deepcopy(left["episode"]["stages"][-1]["signature"])
    start_route = list(boundary["route_residue"])
    model = atomic_corridor_model(
        "COR-POS-02B",
        MIDDLE,
        TARGET,
        base_rank=int(boundary["predictive_rank"]),
        base_record=int(boundary["record_value"]),
        start_route=start_route,
        start_event_id="m-boundary",
        boundary_event_id="t-chain-exit",
        leg_id="leg-M-T",
        title="right strict overlap leg for composition",
    )
    # The shared temporal frontier and event must be byte-identical after stage shifting.
    model["episode"]["stages"][0]["signature"] = copy.deepcopy(boundary)
    model["episode"]["events"][0] = event("m-boundary", MIDDLE, 0)
    return model


def recalc_counterfactual(leg: dict[str, Any]) -> None:
    c = leg["counterfactual"]
    base = c["base_projection"]
    src = c["source_contribution"]
    dst = c["target_contribution"]
    c["full_projection"] = [a + b + d for a, b, d in zip(base, src, dst, strict=True)]
    c["source_removed_projection"] = [a + d for a, d in zip(base, dst, strict=True)]
    c["target_removed_projection"] = [a + b for a, b in zip(base, src, strict=True)]


def corridor_controls() -> list[dict[str, Any]]:
    controls: list[dict[str, Any]] = []

    def add(control_id: str, name: str, mutate: Callable[[dict[str, Any]], None], expected: str) -> None:
        model = positive_atomic_corridor()
        model["model_id"] = control_id
        model["title"] = name
        model["kind"] = "corridor-control"
        mutate(model)
        controls.append({"control_id": control_id, "name": name, "model": model, "expected_failed_obligation": expected})

    add("COR-C01", "no mixed support", lambda m: m["episode"]["stages"][1].update(active_support=[copy.deepcopy(TARGET)]), "mixed-support-exact")
    add("COR-C02", "realized-time gap", lambda m: m["episode"]["stages"][1].update(temporal_realized=False), "all-stages-temporally-realized")

    def source_redundant(m: dict[str, Any]) -> None:
        leg = m["legs"][0]
        leg["counterfactual"]["source_contribution"] = [0, 0, 0]
        recalc_counterfactual(leg)
        m["episode"]["stages"][2]["signature"]["predictive_rank"] = leg["counterfactual"]["full_projection"][0]
        m["episode"]["stages"][2]["signature"]["tick_index"] = leg["counterfactual"]["full_projection"][1]
        m["episode"]["stages"][2]["signature"]["record_value"] = leg["counterfactual"]["full_projection"][2]

    add("COR-C03", "source contribution redundant", source_redundant, "source-nonredundant")

    def target_redundant(m: dict[str, Any]) -> None:
        leg = m["legs"][0]
        leg["counterfactual"]["target_contribution"] = [0, 0, 0]
        recalc_counterfactual(leg)
        m["episode"]["stages"][2]["signature"]["predictive_rank"] = leg["counterfactual"]["full_projection"][0]
        m["episode"]["stages"][2]["signature"]["tick_index"] = leg["counterfactual"]["full_projection"][1]
        m["episode"]["stages"][2]["signature"]["record_value"] = leg["counterfactual"]["full_projection"][2]

    add("COR-C04", "target contribution redundant", target_redundant, "target-nonredundant")
    add("COR-C05", "wrong initial support", lambda m: m["episode"]["stages"][0].update(active_support=[copy.deepcopy(SOURCE), copy.deepcopy(TARGET)]), "starts-source-only")
    add("COR-C06", "wrong terminal support", lambda m: m["episode"]["stages"][2].update(active_support=[copy.deepcopy(SOURCE), copy.deepcopy(TARGET)]), "ends-target-only")
    add("COR-C07", "source survives takeover", lambda m: m["episode"]["stages"][2].update(active_support=[copy.deepcopy(SOURCE), copy.deepcopy(TARGET)]), "source-absent-after-takeover")
    add("COR-C08", "unresolved route status", lambda m: (m["legs"][0].update(route_status="unresolved"), m["legs"][0]["transport_evidence"].update(route_status="unresolved")), "route-status-valid")
    add("COR-C09", "route residue collapse", lambda m: m["episode"]["stages"][2]["signature"].update(route_residue=[]), "route-memory-valid")
    add("COR-C10", "missing bundled component", lambda m: m["legs"][0]["transport_evidence"].update(components=m["legs"][0]["transport_evidence"]["components"][:-1]), "bundled-transport-evidence")
    add("COR-C11", "representative dependence", lambda m: m["legs"][0]["transport_evidence"].update(representative_independent=False), "bundled-transport-evidence")
    add("COR-C12", "failed ownership interface", lambda m: m["legs"][0]["transport_evidence"].update(ownership_interface_valid=False), "bundled-transport-evidence")
    add("COR-C13", "tick stalls at terminal stage", lambda m: m["episode"]["stages"][2]["signature"].update(tick_index=1), "local-temporal-steps-valid")
    add("COR-C14", "record fails to advance", lambda m: m["episode"]["stages"][2]["signature"].update(record_value=1), "local-temporal-steps-valid")
    add("COR-C15", "predictive step skips frozen successor", lambda m: m["episode"]["stages"][2]["signature"].update(predictive_rank=3), "local-temporal-steps-valid")

    def remove_source_edge(m: dict[str, Any]) -> None:
        m["episode"]["dependencies"] = [row for row in m["episode"]["dependencies"] if row["parent_event_id"] != "leg-S-T-source-mixed"]

    add("COR-C16", "source intervention edge absent", remove_source_edge, "intervention-events-valid")

    def remove_target_edge(m: dict[str, Any]) -> None:
        m["episode"]["dependencies"] = [row for row in m["episode"]["dependencies"] if row["parent_event_id"] != "leg-S-T-target-mixed"]

    add("COR-C17", "target intervention edge absent", remove_target_edge, "intervention-events-valid")
    add("COR-C18", "carrier chain repeats endpoint", lambda m: m.update(carrier_chain=[copy.deepcopy(SOURCE), copy.deepcopy(SOURCE)]), "carrier-chain-valid")
    add("COR-C19", "leg target mismatches chain", lambda m: m["legs"][0].update(target_carrier=copy.deepcopy(MIDDLE)), "frontier-cover-valid")
    add("COR-C20", "extraneous carrier inside atomic leg", lambda m: m["episode"]["stages"][1].update(active_support=[copy.deepcopy(SOURCE), copy.deepcopy(TARGET), copy.deepcopy(MIDDLE)]), "local-support-scoped")
    add("COR-C21", "noncontiguous stage index", lambda m: m["episode"]["stages"][1].update(stage=3), "stage-indices-contiguous")
    add("COR-C22", "verdict-loaded evidence field", lambda m: m["legs"][0].update(lineage_verdict=True), "forbidden-verdict-fields-absent")
    return controls


def temporal_payload(next_rank: int, next_record: int, maintenance_state: str, route: list[str]) -> dict[str, Any]:
    return {
        "predictive_rank": next_rank,
        "order_rank": next_rank,
        "tick_index": next_rank,
        "progress_rank": next_rank,
        "record_value": next_record,
        "route_residue": route,
        "maintenance_state": maintenance_state,
    }


def direct_successor_model(
    model_id: str,
    source: dict[str, Any],
    target: dict[str, Any],
    *,
    source_rank: int,
    source_record: int,
    source_route: list[str],
    source_event_id: str,
    target_event_id: str,
    dependency_id: str,
    target_output_payload: dict[str, Any] | None = None,
    title: str,
) -> dict[str, Any]:
    target_rank = source_rank + 1
    target_record = source_record + 2
    target_route = [*source_route, f"{dependency_id}-edge"]
    source_sig = signature(source_rank, source_record, int(source["code"]), source_route, f"{dependency_id}-source-maint")
    target_sig = signature(target_rank, target_record, int(target["code"]), target_route, f"{dependency_id}-target-maint")
    payload = temporal_payload(target_rank, target_record, target_sig["maintenance_state"], target_route)
    source_event = event(source_event_id, source, 0)
    source_event["output_payload"] = copy.deepcopy(payload)
    target_event = event(target_event_id, target, 1)
    target_event["input_payload"] = copy.deepcopy(payload)
    target_event["output_payload"] = copy.deepcopy(target_output_payload if target_output_payload is not None else payload)
    edge = {
        "dependency_id": dependency_id,
        "parent_event_id": source_event_id,
        "child_event_id": target_event_id,
        "dependency_kind": "live-temporal-handoff",
        "payload": copy.deepcopy(payload),
        "payload_sha256": canonical_hash(payload),
        "counterfactually_necessary": True,
        "storage_mediator": False,
        "replayable_archive": False,
        "alternative_temporal_parent": False,
        "single_use_temporal_token": True,
    }
    return {
        "schema_version": "CST-TT-04-model-v1",
        "model_id": model_id,
        "title": title,
        "kind": "atomic-direct-temporal-successor",
        "claim_lanes": ["S-L"],
        "claim_ceiling": "exact finite structural event-successor criterion only",
        "source_carrier": copy.deepcopy(source),
        "target_carrier": copy.deepcopy(target),
        "last_source_event_id": source_event_id,
        "first_target_event_id": target_event_id,
        "operational_dependency_id": dependency_id,
        "route_status": "route-indexed",
        "episode": {
            "stages": [stage(0, [source], source_sig), stage(1, [target], target_sig)],
            "events": [source_event, target_event],
            "dependencies": [edge],
        },
        "nonclaims": [
            "not a strict overlap corridor",
            "no target-package or autonomy verdict",
            "no phenomenal or personal-status conclusion",
        ],
    }


def positive_direct_successor() -> dict[str, Any]:
    return direct_successor_model(
        "DS-POS-01",
        SOURCE,
        TARGET,
        source_rank=0,
        source_record=0,
        source_route=["direct-root"],
        source_event_id="ds-source-final",
        target_event_id="ds-target-first",
        dependency_id="ds-edge-S-T",
        title="atomic direct temporal successor",
    )


def positive_direct_path_left() -> dict[str, Any]:
    next_payload = temporal_payload(2, 4, "ds-edge-M-T-target-maint", ["direct-root", "ds-edge-S-M-edge", "ds-edge-M-T-edge"])
    return direct_successor_model(
        "DS-POS-02A",
        SOURCE,
        MIDDLE,
        source_rank=0,
        source_record=0,
        source_route=["direct-root"],
        source_event_id="ds-chain-source",
        target_event_id="ds-middle-boundary",
        dependency_id="ds-edge-S-M",
        target_output_payload=next_payload,
        title="left atomic direct successor for path composition",
    )


def positive_direct_path_right() -> dict[str, Any]:
    left = positive_direct_path_left()
    boundary_sig = copy.deepcopy(left["episode"]["stages"][-1]["signature"])
    model = direct_successor_model(
        "DS-POS-02B",
        MIDDLE,
        TARGET,
        source_rank=int(boundary_sig["predictive_rank"]),
        source_record=int(boundary_sig["record_value"]),
        source_route=list(boundary_sig["route_residue"]),
        source_event_id="ds-middle-boundary",
        target_event_id="ds-chain-target",
        dependency_id="ds-edge-M-T",
        title="right atomic direct successor for path composition",
    )
    # Reuse the exact boundary signature, event, and output token.
    model["episode"]["stages"][0]["signature"] = copy.deepcopy(boundary_sig)
    right_source_event = model["episode"]["events"][0]
    left_boundary_event = left["episode"]["events"][1]
    right_source_event["output_payload"] = copy.deepcopy(left_boundary_event["output_payload"])
    edge = model["episode"]["dependencies"][0]
    edge["payload"] = copy.deepcopy(right_source_event["output_payload"])
    edge["payload_sha256"] = canonical_hash(edge["payload"])
    model["episode"]["events"][1]["input_payload"] = copy.deepcopy(edge["payload"])
    return model


def direct_controls() -> list[dict[str, Any]]:
    controls: list[dict[str, Any]] = []

    def add(control_id: str, name: str, mutate: Callable[[dict[str, Any]], None], expected: str) -> None:
        model = positive_direct_successor()
        model["model_id"] = control_id
        model["title"] = name
        model["kind"] = "direct-successor-control"
        mutate(model)
        controls.append({"control_id": control_id, "name": name, "model": model, "expected_failed_obligation": expected})

    edge = lambda m: m["episode"]["dependencies"][0]
    add("DS-C01", "replayable archive", lambda m: edge(m).update(replayable_archive=True), "not-replayable-archive")
    add("DS-C02", "storage mediator", lambda m: edge(m).update(storage_mediator=True), "no-storage-mediator")
    add("DS-C03", "edge is not counterfactually necessary", lambda m: edge(m).update(counterfactually_necessary=False), "edge-counterfactually-necessary")
    add("DS-C04", "alternative temporal parent exists", lambda m: edge(m).update(alternative_temporal_parent=True), "no-alternative-temporal-parent")
    add("DS-C05", "temporal token is replayable", lambda m: edge(m).update(single_use_temporal_token=False), "single-use-temporal-token")

    def incomplete_payload(m: dict[str, Any]) -> None:
        payload = edge(m)["payload"]
        payload.pop("route_residue")
        m["episode"]["events"][0]["output_payload"] = copy.deepcopy(payload)
        m["episode"]["events"][1]["input_payload"] = copy.deepcopy(payload)
        edge(m)["payload_sha256"] = canonical_hash(payload)

    add("DS-C06", "incomplete temporal payload", incomplete_payload, "payload-components-complete")
    add("DS-C07", "payload digest mismatch", lambda m: edge(m).update(payload_sha256="0" * 64), "payload-hashes-match")
    add("DS-C08", "archival data edge", lambda m: edge(m).update(dependency_kind="archival-copy", replayable_archive=True, storage_mediator=True), "edge-kind-valid")

    def stage_gap(m: dict[str, Any]) -> None:
        m["episode"]["stages"].insert(1, stage(1, [BRIDGE], signature(1, 1, int(BRIDGE["code"]), ["archive"], "archive-maint"), realized=False))
        m["episode"]["stages"][2]["stage"] = 2
        m["episode"]["events"][1]["stage"] = 2

    add("DS-C09", "stored interval and temporal gap", stage_gap, "stage-adjacency")
    add("DS-C10", "predictive successor mismatch", lambda m: m["episode"]["stages"][1]["signature"].update(predictive_rank=0), "predictive-step-valid")
    add("DS-C11", "tick does not advance", lambda m: m["episode"]["stages"][1]["signature"].update(tick_index=0), "tick-step-valid")
    add("DS-C12", "record does not advance", lambda m: m["episode"]["stages"][1]["signature"].update(record_value=0), "strict-record-step-valid")
    add("DS-C13", "target temporal maintenance remains source-owned", lambda m: m["episode"]["stages"][1]["signature"].update(maintenance_owner=int(SOURCE["code"])), "ownership-interface-valid")

    def same_carrier(m: dict[str, Any]) -> None:
        m["target_carrier"] = copy.deepcopy(SOURCE)

    add("DS-C14", "same-carrier event succession", same_carrier, "distinct-carriers")

    def endpoint_only(m: dict[str, Any]) -> None:
        edge(m).update(
            dependency_kind="archival-copy",
            replayable_archive=True,
            storage_mediator=True,
            counterfactually_necessary=False,
            alternative_temporal_parent=True,
            single_use_temporal_token=False,
        )

    add("DS-C15", "endpoint-only arbitrary data reachability", endpoint_only, "edge-kind-valid")
    add("DS-C16", "verdict-loaded event evidence", lambda m: edge(m).update(lineage_verdict=True), "forbidden-verdict-fields-absent")
    return controls
