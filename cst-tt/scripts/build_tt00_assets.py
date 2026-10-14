#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from pathlib import Path

import tt00_data as data

ROOT = Path(__file__).resolve().parents[1]


def write_csv(path: Path, rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        raise ValueError(f"cannot write empty registry: {path}")
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def write_json(path: Path, obj: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def md_table(headers: list[str], rows: list[list[str]]) -> str:
    def clean(value: object) -> str:
        return str(value).replace("|", "\\|").replace("\n", " ")
    lines = ["| " + " | ".join(headers) + " |", "|" + "|".join(["---"] * len(headers)) + "|"]
    lines.extend("| " + " | ".join(clean(v) for v in row) + " |" for row in rows)
    return "\n".join(lines)


def build_target_freeze() -> str:
    return """# CST-TT-00 Target Freeze

**Project:** CST-TT — Consciousness Substrate Transcendence: Theorems and Toys  
**Phase:** CST-TT-00  
**Status:** executable semantics and statement scaffold; no scientific theorem or toy witness landed

## Primary relation

The primary structural target is **Temporal-FIACH**:

```text
TemporalFIACH_e(s,t) :=
  DistinctCarrier(S,T)
  ∧ SourcePkg(S,s)
  ∧ StagedClausePreservation(e,s,t)
  ∧ IntegratedPkg(T,t,e)
  ∧ TemporalCorridor(S,T,e,s,t)
  ∧ Autonomous(T,e,D,K)
```

The relation is certificate-existence over three independently validated layers:

1. **S-R — integrated target realization:** eight separately scoped C-shaped witnesses, global gluing, hard gates, substantive C6 temporal closure, and target ownership.
2. **S-L — strict temporal lineage:** a no-gap episode with a genuinely mixed source/target stage, independently specified counterfactual nonredundancy, transport of the frozen temporal signature, takeover, and explicit route status.
3. **A — post-withdrawal autonomy:** source, bridge, migration controller, decoder, scheduler, and undeclared repair are removed; the target remains in a target-owned controlled invariant region under a predeclared disturbance class.

No lane inherits another. The aggregate is not a function, an equivalence relation, a personal-identity predicate, or a consciousness certificate.

## Temporal object frozen before lineage

```text
TemporalSignature :=
  PredictiveNow
  + order state
  + tick phase
  + genuine progress state
  + endogenous arrow/record state
  + route residue
  + maintenance state
  + owner
```

`PredictiveNow` includes both a future-sufficient predictive class and retained route residue. The route residue may be discharged only by a separate flatness/confluence theorem.

This order of definition is normative:

```text
carrier typing
  -> temporal alphabet
  -> temporal signature
  -> carrier-local temporal closure
  -> heterogeneous temporal bridge
  -> operational episode
  -> counterfactual audit
  -> strict temporal corridor
  -> target package and autonomy
  -> Temporal-FIACH aggregate
```

A corridor may not define the signature it claims to preserve.

## Overlap and direct-successor classes

The strict primary requires an operationally mixed stage and no gap in realized package time. A separately named provisional `DirectSuccessorCertificate` permits the last source-owned event to generate the first target-owned event without an extended mixed stage, but only through explicit operational dependency, predictive transport, tick translation, record descent, and ownership-interface evidence.

The direct-successor class does not broaden the strict corridor by definition. Their exact relation remains an open CST-TT-04/CST-TT-07A theorem question.

## Fallback

Temporal-IAPS remains dormant unless a documented FIACH kill criterion is triggered. Its seed is operational provenance, its closure must be monotone and no-ex-nihilo, and it may produce relation-valued structural successorship. It does not establish uninterrupted temporal lineage or numerical identity.

## Claim ceiling

The theorem/toy program may establish exact finite structural realization, transport, episode-indexed lineage, route dependence, and model-relative autonomy. It does not establish:

- that temporal closure is sufficient for consciousness;
- that temporal closure is necessary for felt experience without `H-FELT-TIME`;
- that the strict corridor tracks felt continuity without `H-CONT-TIME` and recognition assumptions;
- A1, A2-P, certificate soundness, or an empirical recognition bridge;
- personal survival or numerical identity.

The interpretive hypotheses are frozen in the assumption ledger and absent from primitive theorem premises.
"""


def build_formalization_contract() -> str:
    rows = [[r["definition_id"], r["name"], r["module"], r["claim_lanes"], r["dependencies"] or "—"] for r in data.DEFINITION_ROWS]
    return f"""# Executable Formalization Contract

## Toolchains

- Lean: `{data.LEAN_TOOLCHAIN}`
- Python: `{data.PYTHON_VERSION}` with the exact observed package versions in `requirements-lock.txt`
- Lean dependency policy for CST-TT-00: core Lean + `Std`; no Mathlib dependency is required by the scaffold

## Trust boundary

Lean is intended to define the semantics and check later proof terms and finite certificates. Python is intended to enumerate finite candidates, canonicalize data, validate schemas, and emit certificates. Python enumeration is never a proof oracle.

CST-TT-00 contains statement and certificate interfaces only. All theorem rows are `open-scaffold`; all toy rows are `specified-not-implemented`; all example certificates are `not-evaluated` or `scaffold-only`.

## Definition registry

{md_table(["ID", "Definition", "Lean module", "Lane", "Depends on"], rows)}

## Module dependency rule

Primitive layers may import only earlier layers. In particular:

- `Temporal` must not import `Corridor` or `Targets`.
- `Package` must not import `Corridor`, `Autonomy`, or `Targets`.
- `Transport` must not import `Corridor` or `Targets`.
- `Corridor` may import transport and episode data but not the aggregate target.
- `Autonomy` must not import corridor or aggregate target definitions.
- Only `Targets` aggregates package, corridor, and autonomy evidence.

The circularity validator scans primitive Lean modules and certificate-schema field names for verdict-equivalent vocabulary.
"""


def build_theorem_toy_registry() -> str:
    theorem_rows = [[r["theorem_id"], r["name"], r["phase"], r["kind"], r["claim_lanes"], r["status"]] for r in data.THEOREM_ROWS]
    toy_rows = [[r["toy_id"], r["name"], r["role"], r["phase"], r["status"]] for r in data.TOY_ROWS]
    return f"""# Frozen Theorem and Toy Registry

## Theorem/no-go statement bank

{md_table(["ID", "Name", "Landing phase", "Kind", "Lanes", "Status"], theorem_rows)}

## Toy-model bank

{md_table(["ID", "Name", "Role", "Landing phase", "Status"], toy_rows)}

## Status vocabulary in CST-TT-00

`open-scaffold` means that an exact Lean proposition interface and dependency row are present but no proof is claimed. `specified-not-implemented` means that a model's discrimination contract is frozen but no finite model instance or program result exists. Checked countermodels begin only in CST-TT-01; positive witnesses begin only after their definitions have survived the negative kernel.
"""


def build_temporal_amendment_map() -> str:
    rows = [
        [
            r["legacy_id"], r["legacy_title"], r["temporal_ids"],
            r["disposition"], r["temporal_amendment"],
        ]
        for r in data.TEMPORAL_AMENDMENT_ROWS
    ]
    return f"""# Temporal Amendment and Legacy Provenance Map

CST-TT-00 preserves every theorem-family identifier frozen in CST-EXP-06. The
new `TTH`/`TTN`/`TTD`/`TTF` identifiers are execution-facing theorem and no-go
contracts; the `PTH`/`FTH` identifiers remain the provenance layer. A split row
means that one exploratory prospect was separated into independently typed
constructive and boundary obligations rather than silently broadened.

{md_table(["Legacy ID", "Legacy prospect", "CST-TT IDs", "Disposition", "Temporal amendment"], rows)}

The normative machine-readable surface is
`registries/TEMPORAL_AMENDMENT_MAP.csv`; the source legacy family remains
`synthesis/FROZEN_THEOREM_FAMILY.csv`.
"""


def build_assumption_claims() -> str:
    structural = [r for r in data.ASSUMPTION_ROWS if r["tier"] in {"structural","optional-structural","fallback-structural"}]
    interpretive = [r for r in data.ASSUMPTION_ROWS if r["tier"] not in {"structural","optional-structural","fallback-structural"}]
    srows = [[r["assumption_id"], r["name"], r["tier"], r["statement"], r["nonclaim"]] for r in structural]
    irows = [[r["assumption_id"], r["name"], r["tier"], r["statement"], r["nonclaim"]] for r in interpretive]
    return f"""# Assumption Ladder and Claim Ceiling

## Structural theorem premises

{md_table(["ID", "Name", "Tier", "Statement", "Boundary"], srows)}

## Interpretive, empirical, and ontological premises

{md_table(["ID", "Name", "Tier", "Statement", "Boundary"], irows)}

## Temporal hypotheses

`H-FELT-TIME` is a necessity hypothesis: the felt aspect requires autonomous layer-realized temporal closure. It does not say temporal closure is sufficient.

`H-CONT-TIME` is a continuity hypothesis: uninterrupted felt continuity requires episode-indexed continuation of realized temporal closure. The structural antecedent can be formalized; the felt conclusion remains outside the theorem core.

Neither hypothesis appears in the primitive Lean definitions of temporal signature, package, bridge, corridor, or autonomy.

## Reporting rule

Every final result must name its structural claim lane and list any additional recognition or ontology assumptions needed for a stronger reading. Terms such as *consciousness transferred*, *same subject*, *survived*, and *numerically identical* are prohibited as theorem conclusions unless the separately priced assumptions are displayed in the same statement.
"""


def build_circularity_policy() -> str:
    krows = [[r["kill_id"], r["target"], r["trigger"], r["action"], r["decision_phase"]] for r in data.KILL_ROWS]
    return f"""# Circularity, Typing, and Kill Policy

## Primitive-definition ban

The circularity scan applies to `CSTTT/Core`, `CSTTT/Temporal`, `CSTTT/Package`, `CSTTT/Transport`, `CSTTT/Corridor`, and `CSTTT/Autonomy`. These modules may not contain verdict-equivalent premises such as FIACH, IAPS, continuation, same subject, same person, survival, numerical identity, or consciousness.

The aggregate target modules and policy documents may name the targets, but they may only combine previously typed evidence.

## Anti-smuggling rules

1. Carrier identities are fixed before state comparison.
2. The temporal signature is frozen before any corridor predicate.
3. Operational dependencies are not lineage edges.
4. Public equality is not predictive equality.
5. Predictive equality is not package realization.
6. Package realization is not lineage.
7. Lineage is not autonomy.
8. Ordinary runtime behavior is not post-withdrawal autonomy.
9. Holonomy is not an endogenous arrow.
10. Route residue is retained unless flatness/confluence is proved.
11. Stable tick phase is not genuine progress.
12. A scalar residual cannot override a failed hard gate.
13. Exact copying does not select a unique branch.
14. Direct successor is not silently identified with strict overlap.
15. Structural lineage is not personal identity.

## Frozen kill criteria

{md_table(["ID", "Target", "Trigger", "Required action", "Decision phase"], krows)}
"""


def build_phase_boundary() -> str:
    return """# CST-TT-00 Phase Boundary

## Completed here

- Restored the exact CST-EXP-06 Git history and verified its frozen base commit/tag.
- Imported the temporal-transcendence audit, its source map, nine relevant source manuscripts, and the theorem/toy execution plan with hashes.
- Pinned the Lean and Python toolchains.
- Created separately typed Lean interfaces for carriers, episodes, temporal signatures, temporal closure, C-shaped clauses, gluing, heterogeneous temporal bridges, strict corridors, direct successors, withdrawal autonomy, Temporal-FIACH, and fallback ancestry.
- Created Python dataclasses and validators mirroring the certificate boundaries.
- Frozen theorem, toy, definition, certificate-schema, assumption, claim-lane, dependency, and kill-criterion registries.
- Preserved all twelve PTH and eight FTH provenance identifiers through an explicit temporal amendment map.
- Added a circularity validator and explicit no-results gate.

## Intentionally absent

- no proved scientific theorem;
- no checked finite countermodel;
- no positive Temporal-FIACH or IAPS witness;
- no toy enumerator or optimizer;
- no empirical recognition protocol;
- no full Six Birds simulation;
- no claim of consciousness, felt continuity, survival, or numerical identity.

## Next authorized phase

`CST-TT-01` lands the negative theorem kernel and minimal exact countermodels before any positive witness is optimized.
"""


def build_restore() -> str:
    return """# Restore, Validate, and Continue

From the extracted repository root:

```bash
git status --short
git tag --list 'CST-TT-00-v1'
python3 scripts/validate_tt00.py
PYTHONPATH=src python3 -m pytest
python3 scripts/verify_tt00_rebuild.py
sha256sum -c manifests/SHA256SUMS
```

If Lean and Lake are installed through the pinned toolchain:

```bash
lake build
```

The source snapshot records whether Lean was available in the execution environment. Lack of a local Lean executable does not authorize changing the pinned version or treating the static source audit as a Lean compilation pass.

To regenerate deterministic CST-TT-00 registry and documentation surfaces:

```bash
python3 scripts/build_tt00_assets.py
```
"""


def main(root: Path | None = None) -> None:
    global ROOT
    if root is not None:
        ROOT = root.resolve()
    ROOT.mkdir(parents=True, exist_ok=True)
    write_csv(ROOT / "registries/CLAIM_LANE_REGISTRY.csv", data.CLAIM_LANES)
    write_csv(ROOT / "registries/DEFINITION_REGISTRY.csv", data.DEFINITION_ROWS)
    write_csv(ROOT / "registries/THEOREM_REGISTRY.csv", data.THEOREM_ROWS)
    write_csv(ROOT / "registries/TEMPORAL_AMENDMENT_MAP.csv", data.TEMPORAL_AMENDMENT_ROWS)
    write_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv", data.TOY_ROWS)
    write_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv", data.SCHEMA_ROWS)
    write_csv(ROOT / "registries/ASSUMPTION_LEDGER.csv", data.ASSUMPTION_ROWS)
    write_csv(ROOT / "registries/KILL_CRITERIA.csv", data.KILL_ROWS)
    write_csv(ROOT / "registries/DEPENDENCY_EDGES.csv", data.DEPENDENCY_ROWS)
    write_csv(ROOT / "manifests/CST-TT-00_THEOREM_STATUS_DELTA.csv", [
        {
            "theorem_id": row["theorem_id"],
            "previous_status": "not-present-in-CST-TT",
            "current_status": row["status"],
            "proof_or_countermodel": "none",
            "landing_phase": row["phase"],
        }
        for row in data.THEOREM_ROWS
    ])
    write_csv(ROOT / "manifests/CST-TT-00_MODEL_CERTIFICATE_DELTA.csv", [
        {
            "asset_id": row["toy_id"],
            "asset_kind": "toy-model-contract",
            "previous_status": "not-present-in-CST-TT",
            "current_status": row["status"],
            "instantiated": "no",
        }
        for row in data.TOY_ROWS
    ] + [
        {
            "asset_id": row["schema_id"],
            "asset_kind": "certificate-schema",
            "previous_status": "not-present-in-CST-TT",
            "current_status": row["status"],
            "instantiated": "scaffold-example-only",
        }
        for row in data.SCHEMA_ROWS
    ])

    write_json(ROOT / "registries/PROJECT_REGISTRY.json", {
        "project": data.PROJECT,
        "phase": data.PHASE,
        "base_commit": data.BASE_COMMIT,
        "base_tag": data.BASE_TAG,
        "primary": "Temporal-FIACH strict overlap",
        "provisional_strengthening": "direct-successor temporal class",
        "conditional_fallback": "Temporal-IAPS",
        "mandatory_companion": "finite no-go kernel",
        "lean_toolchain": data.LEAN_TOOLCHAIN,
        "python_version": data.PYTHON_VERSION,
        "claim_ceiling": "structural precursor only",
        "scientific_results_landed": 0,
    })

    docs = {
        "TARGET_FREEZE.md": build_target_freeze(),
        "FORMALIZATION_CONTRACT.md": build_formalization_contract(),
        "THEOREM_AND_TOY_REGISTRY.md": build_theorem_toy_registry(),
        "TEMPORAL_AMENDMENT_MAP.md": build_temporal_amendment_map(),
        "ASSUMPTION_AND_CLAIM_CEILING.md": build_assumption_claims(),
        "CIRCULARITY_AND_TYPING_POLICY.md": build_circularity_policy(),
        "PHASE_BOUNDARY.md": build_phase_boundary(),
        "RESTORE_AND_BUILD.md": build_restore(),
    }
    for name, text in docs.items():
        (ROOT / "docs" / name).write_text(text.rstrip() + "\n", encoding="utf-8")

    counts = {
        "claim_lanes": len(data.CLAIM_LANES),
        "definitions": len(data.DEFINITION_ROWS),
        "theorem_prospects": len(data.THEOREM_ROWS),
        "legacy_theorem_prospects_mapped": len(data.TEMPORAL_AMENDMENT_ROWS),
        "toy_model_contracts": len(data.TOY_ROWS),
        "certificate_schemas": len(data.SCHEMA_ROWS),
        "assumptions": len(data.ASSUMPTION_ROWS),
        "kill_criteria": len(data.KILL_ROWS),
        "dependency_edges": len(data.DEPENDENCY_ROWS),
        "theorem_kinds": dict(sorted(Counter(r["kind"] for r in data.THEOREM_ROWS).items())),
        "theorem_phases": dict(sorted(Counter(r["phase"] for r in data.THEOREM_ROWS).items())),
    }
    write_json(ROOT / "manifests/TT00_ASSET_SUMMARY.json", counts)
    print(json.dumps(counts, indent=2, sort_keys=True))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Regenerate deterministic CST-TT-00 registries and documentation surfaces.")
    parser.add_argument("--root", type=Path, default=None, help="repository root to populate (defaults to this script's parent)")
    args = parser.parse_args()
    main(args.root)
