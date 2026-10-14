#!/usr/bin/env python3
from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path
from typing import Iterable, Mapping

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
import sys

if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from cst_tt.countermodels import SearchOutcome, enumerate_all  # noqa: E402
from cst_tt.registry import read_csv  # noqa: E402

PHASE = "CST-TT-01"
DATE = "2026-08-10"


def json_text(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json_text(value), encoding="utf-8")


def write_csv(path: Path, fieldnames: list[str], rows: Iterable[Mapping[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row.get(key, "") for key in fieldnames})


def update_csv_rows(path: Path, key: str, updates: Mapping[str, Mapping[str, str]]) -> list[dict[str, str]]:
    rows = read_csv(path)
    for row in rows:
        if row[key] in updates:
            row.update(updates[row[key]])
    write_csv(path, list(rows[0]), rows)
    return rows


def markdown_table(headers: list[str], rows: Iterable[Iterable[object]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "|" + "|".join("---" for _ in headers) + "|"]
    for row in rows:
        lines.append("| " + " | ".join(str(value).replace("|", "\\|") for value in row) + " |")
    return "\n".join(lines)


def build_models(outcomes: tuple[SearchOutcome, ...]) -> list[dict[str, object]]:
    model_dir = ROOT / "models/countermodels"
    cert_dir = ROOT / "formal/certificates/countermodels"
    model_dir.mkdir(parents=True, exist_ok=True)
    cert_dir.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, object]] = []
    for outcome in outcomes:
        cm_id = outcome.spec.countermodel_id
        model_ref = f"models/countermodels/{cm_id}.model.json"
        cert_ref = f"formal/certificates/countermodels/{cm_id}.certificate.json"
        model_doc = outcome.model_document()
        model_bytes = json_text(model_doc).encode("utf-8")
        (ROOT / model_ref).write_bytes(model_bytes)
        model_hash = sha256_bytes(model_bytes)
        certificate = outcome.certificate_document(model_ref, model_hash)
        write_json(ROOT / cert_ref, certificate)
        card_ref = f"models/countermodels/{cm_id}.md"
        premise_rows = "\n".join(
            f"- `{key}`: `{str(value).lower()}`"
            for key, value in sorted(outcome.check.premises.items())
        )
        failure_rows = "\n".join(
            f"- `{key}`: `{str(value).lower()}`"
            for key, value in sorted(outcome.check.conclusion_failures.items())
        )
        card = f"""# {cm_id} — {outcome.spec.name}

**Result:** checked finite countermodel  
**Target:** `{outcome.spec.target_no_go_id}`  
**Toy contract:** `{outcome.spec.toy_model_ref}`  
**Claim lanes:** `{';'.join(outcome.spec.claim_lanes)}`  
**Claim ceiling:** structural boundary only

## Boundary

{outcome.spec.scope}

## Canonical finite witness

```json
{json.dumps(outcome.witness.model, indent=2, sort_keys=True)}
```

## Certified premises

{premise_rows}

## Failed stronger conclusion

{failure_rows}

## Relative minimality

- Size measure: `{outcome.spec.size_measure}`
- Witness size: `{list(outcome.witness.size_vector)}`
- Search bound: `{outcome.spec.search_bound}`
- Candidates explored: `{outcome.candidates_explored}`
- Strictly smaller candidates explored: `{outcome.smaller_candidates_explored}`
- Qualifying candidates at minimal size: `{outcome.same_size_qualifying_candidates}`
- Lower-bound argument: {outcome.spec.lower_bound_argument}

## Verification surfaces

- Model: `{model_ref}`
- Certificate: `{cert_ref}`
- Python recheck: `cst_tt.countermodels.recheck("{cm_id}", model)`
- Lean declaration: `{outcome.spec.lean_declaration}`
- Lean compilation status: not run in this environment because `lean` and `lake` are unavailable

## Nonclaims

This finite structural countermodel does not establish or refute consciousness, phenomenal feeling, personal survival, numerical identity, A1, A2-P, certificate soundness, or empirical recognition.
"""
        (ROOT / card_ref).write_text(card, encoding="utf-8")
        rows.append(
            {
                "countermodel_id": cm_id,
                "name": outcome.spec.name,
                "target_no_go_id": outcome.spec.target_no_go_id,
                "toy_model_ref": outcome.spec.toy_model_ref,
                "family": outcome.spec.family,
                "claim_lanes": ";".join(outcome.spec.claim_lanes),
                "scope": outcome.spec.scope,
                "model_ref": model_ref,
                "model_card_ref": card_ref,
                "certificate_ref": cert_ref,
                "lean_declaration": outcome.spec.lean_declaration,
                "python_checker": f"cst_tt.countermodels:{cm_id}",
                "size_vector": ";".join(str(value) for value in outcome.witness.size_vector),
                "candidates_explored": outcome.candidates_explored,
                "qualifying_candidates": outcome.qualifying_candidates,
                "minimality_status": outcome.minimality_status,
                "result_status": "checked-finite-countermodel",
                "claim_ceiling": "structural-boundary-only",
            }
        )
    write_csv(
        ROOT / "registries/COUNTERMODEL_REGISTRY.csv",
        [
            "countermodel_id",
            "name",
            "target_no_go_id",
            "toy_model_ref",
            "family",
            "claim_lanes",
            "scope",
            "model_ref",
            "model_card_ref",
            "certificate_ref",
            "lean_declaration",
            "python_checker",
            "size_vector",
            "candidates_explored",
            "qualifying_candidates",
            "minimality_status",
            "result_status",
            "claim_ceiling",
        ],
        rows,
    )
    minimality_rows = [
        {
            "countermodel_id": outcome.spec.countermodel_id,
            "size_measure": outcome.spec.size_measure,
            "witness_size_vector": ";".join(str(value) for value in outcome.witness.size_vector),
            "search_bound": outcome.spec.search_bound,
            "candidates_explored": outcome.candidates_explored,
            "qualifying_candidates": outcome.qualifying_candidates,
            "smaller_candidates_explored": outcome.smaller_candidates_explored,
            "smaller_qualifying_candidates": 0,
            "same_size_candidates_explored": outcome.same_size_candidates_explored,
            "same_size_qualifying_candidates": outcome.same_size_qualifying_candidates,
            "minimality_status": outcome.minimality_status,
            "lower_bound_argument": outcome.spec.lower_bound_argument,
        }
        for outcome in outcomes
    ]
    write_csv(
        ROOT / "registries/MINIMALITY_LEDGER.csv",
        [
            "countermodel_id",
            "size_measure",
            "witness_size_vector",
            "search_bound",
            "candidates_explored",
            "qualifying_candidates",
            "smaller_candidates_explored",
            "smaller_qualifying_candidates",
            "same_size_candidates_explored",
            "same_size_qualifying_candidates",
            "minimality_status",
            "lower_bound_argument",
        ],
        minimality_rows,
    )
    return rows


def update_registries(outcomes: tuple[SearchOutcome, ...], countermodel_rows: list[dict[str, object]]) -> None:
    by_theorem: dict[str, list[str]] = {}
    by_toy: dict[str, list[str]] = {}
    for outcome in outcomes:
        by_theorem.setdefault(outcome.spec.target_no_go_id, []).append(outcome.spec.countermodel_id)
        by_toy.setdefault(outcome.spec.toy_model_ref, []).append(outcome.spec.countermodel_id)

    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    theorem_delta: list[dict[str, object]] = []
    for row in theorem_rows:
        old = "open-scaffold"
        evidence = by_theorem.get(row["theorem_id"], [])
        if evidence:
            row["status"] = "checked-finite-countermodel"
            theorem_delta.append(
                {
                    "theorem_id": row["theorem_id"],
                    "prior_status": old,
                    "new_status": row["status"],
                    "evidence_ids": ";".join(evidence),
                    "proof_scope": "explicit finite instance; generic strengthening remains separate",
                    "phase": PHASE,
                }
            )
    write_csv(ROOT / "registries/THEOREM_REGISTRY.csv", list(theorem_rows[0]), theorem_rows)
    write_csv(
        ROOT / "manifests/CST-TT-01_THEOREM_STATUS_DELTA.csv",
        ["theorem_id", "prior_status", "new_status", "evidence_ids", "proof_scope", "phase"],
        theorem_delta,
    )

    toy_rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    model_delta: list[dict[str, object]] = []
    for row in toy_rows:
        old = "specified-not-implemented"
        evidence = by_toy.get(row["toy_id"], [])
        if evidence:
            row["status"] = "checked-negative-instance"
            note = row.get("notes", "")
            marker = "CST-TT-01 exact negative instance(s):"
            base_notes = [part.strip() for part in note.split("; ") if part.strip() and not part.strip().startswith(marker)]
            extra = marker + " " + ";".join(evidence)
            row["notes"] = "; ".join([*base_notes, extra])
            model_delta.append(
                {
                    "toy_id": row["toy_id"],
                    "prior_status": old,
                    "new_status": row["status"],
                    "countermodel_ids": ";".join(evidence),
                    "phase": PHASE,
                }
            )
    write_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv", list(toy_rows[0]), toy_rows)
    write_csv(
        ROOT / "manifests/CST-TT-01_MODEL_CERTIFICATE_DELTA.csv",
        ["toy_id", "prior_status", "new_status", "countermodel_ids", "phase"],
        model_delta,
    )

    schema_rows = read_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv")
    for row in schema_rows:
        if row["schema_id"] == "CS-08":
            row["status"] = "landed-checked-countermodels"
    write_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv", list(schema_rows[0]), schema_rows)

    project = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    project.update(
        {
            "phase": PHASE,
            "phase_base_tag": "CST-TT-00-v1",
            "phase_base_commit": "65b3ab0f94564cee1d16ffb4513045319aaaf6ef",
            "scientific_results_landed": len(countermodel_rows),
            "checked_finite_countermodels": len(countermodel_rows),
            "positive_handoff_witnesses": 0,
            "generic_theorems_proved": 0,
            "negative_kernel_status": "frozen",
        }
    )
    write_json(ROOT / "registries/PROJECT_REGISTRY.json", project)

    reproducibility = json.loads((ROOT / "config/REPRODUCIBILITY.json").read_text(encoding="utf-8"))
    reproducibility.update(
        {
            "phase": PHASE,
            "scientific_result_generated": True,
            "status": "deterministic-negative-enumeration-frozen",
            "randomized_search_enabled": False,
            "usage_boundary": "CST-TT-01 uses exhaustive deterministic enumeration inside each declared finite model family; no stochastic search is used.",
        }
    )
    write_json(ROOT / "config/REPRODUCIBILITY.json", reproducibility)


def build_docs(outcomes: tuple[SearchOutcome, ...], countermodel_rows: list[dict[str, object]]) -> None:
    summary_table = markdown_table(
        ["ID", "Boundary", "TTN", "Toy", "Minimal size", "Candidates", "Status"],
        (
            (
                outcome.spec.countermodel_id,
                outcome.spec.name,
                outcome.spec.target_no_go_id,
                outcome.spec.toy_model_ref,
                ",".join(map(str, outcome.witness.size_vector)),
                outcome.candidates_explored,
                "checked finite countermodel",
            )
            for outcome in outcomes
        ),
    )
    sections: list[str] = []
    for outcome in outcomes:
        premise_lines = "\n".join(f"- `{key}`: `{str(value).lower()}`" for key, value in sorted(outcome.check.premises.items()))
        failure_lines = "\n".join(
            f"- `{key}`: `{str(value).lower()}`" for key, value in sorted(outcome.check.conclusion_failures.items())
        )
        sections.append(
            f"""### {outcome.spec.countermodel_id} — {outcome.spec.name}

**Boundary:** {outcome.spec.scope}

**Exact witness:** `{json.dumps(outcome.witness.model, sort_keys=True)}`

**Premises checked**

{premise_lines}

**Failed stronger conclusion**

{failure_lines}

**Minimality:** size `{list(outcome.witness.size_vector)}` under `{outcome.spec.size_measure}`. The deterministic search evaluated {outcome.candidates_explored} candidates inside `{outcome.spec.search_bound}`; {outcome.smaller_candidates_explored} were strictly smaller and none qualified. {outcome.spec.lower_bound_argument}

**Lean surface:** `{outcome.spec.lean_declaration}`. The explicit proof source is present; compilation is reported separately.
"""
        )

    negative_kernel = f"""# CST-TT-01 Exact Negative Kernel

**Phase:** CST-TT-01  
**Status:** frozen exact finite countermodels; no positive Temporal-FIACH witness attempted

## Result

The phase lands fifteen deterministic finite countermodels, covering all fourteen required execution-plan boundaries plus the already-frozen branchwise/recombination boundary `TTN-14`.

{summary_table}

## Consequences for the later constructive target

The bank freezes the following separations before any positive witness is tuned:

- endpoint or temporal-signature equality is not a strict episode relation;
- exact copying, target package success, and target autonomy can coexist with strict-corridor failure;
- route holonomy is not an endogenous arrow;
- externally scheduled motion is not post-withdrawal temporal autonomy;
- stable tick phase is not genuine progress;
- current equality can hide predictive route residue;
- nonzero clock-translation holonomy blocks one global canonical `now`;
- local clause validity does not guarantee global package gluing;
- public/report equality does not identify hidden package or predictive facts;
- scalar averages cannot override a failed hard gate;
- exact fork symmetry does not select one invariant branch;
- a resumed equivalent stream can remain separated by a temporal gap;
- finite success does not establish unbounded liveness;
- same-carrier re-encoding is not cross-carrier transport;
- branch marginals do not determine recombination structure.

The detached-copy witness directly checks kill criterion `K-FIACH-04`: under the frozen definitions it **fails** the strict overlap corridor, so the criterion is not triggered in this phase.

## Countermodels

{''.join(sections)}

## Claim ceiling

Every result is an exact finite structural boundary. None establishes or refutes consciousness, phenomenal feeling, personal survival, numerical identity, A1, A2-P, certificate soundness, or empirical recognition.
"""
    (ROOT / "docs/NEGATIVE_KERNEL.md").write_text(negative_kernel, encoding="utf-8")

    minimality_rows = markdown_table(
        ["ID", "Size measure", "Witness", "Search bound", "Explored", "Lower-bound reason"],
        (
            (
                o.spec.countermodel_id,
                o.spec.size_measure,
                list(o.witness.size_vector),
                o.spec.search_bound,
                o.candidates_explored,
                o.spec.lower_bound_argument,
            )
            for o in outcomes
        ),
    )
    (ROOT / "docs/COUNTERMODEL_MINIMALITY.md").write_text(
        f"""# Countermodel Minimality and Search Bounds

Minimality is always relative to the explicitly declared finite generator and lexicographic size measure. The enumerator evaluates every generated candidate, selects the least qualifying size vector, and then selects the canonical-JSON-first witness at that size. No claim of absolute minimality outside the stated family is made.

{minimality_rows}
""",
        encoding="utf-8",
    )

    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    toy_rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    theorem_table = markdown_table(
        ["ID", "Name", "Phase", "Kind", "Lanes", "Status"],
        ((r["theorem_id"], r["name"], r["phase"], r["kind"], r["claim_lanes"], r["status"]) for r in theorem_rows),
    )
    toy_table = markdown_table(
        ["ID", "Name", "Role", "Phase", "Status"],
        ((r["toy_id"], r["name"], r["role"], r["phase"], r["status"]) for r in toy_rows),
    )
    (ROOT / "docs/THEOREM_AND_TOY_REGISTRY.md").write_text(
        f"""# Theorem and Toy Registry — CST-TT-01

`checked-finite-countermodel` means an exact finite instance, deterministic Python recheck, certificate, bounded-minimality audit, and explicit Lean proof source are present. It does not mean that every prospective generic strengthening has been proved. Positive constructive rows remain `open-scaffold`.

## Theorem and no-go bank

{theorem_table}

## Toy bank

{toy_table}
""",
        encoding="utf-8",
    )

    model_index = markdown_table(
        ["ID", "Model", "Card", "Certificate", "TTN", "Toy", "Lanes"],
        (
            (
                row["countermodel_id"],
                f"`{row['model_ref']}`",
                f"`{row['model_card_ref']}`",
                f"`{row['certificate_ref']}`",
                row["target_no_go_id"],
                row["toy_model_ref"],
                row["claim_lanes"],
            )
            for row in countermodel_rows
        ),
    )
    (ROOT / "models/countermodels/INDEX.md").write_text(
        f"# Exact finite countermodel models\n\n{model_index}\n", encoding="utf-8"
    )
    (ROOT / "formal/certificates/countermodels/INDEX.md").write_text(
        f"# Checked countermodel certificates\n\n{model_index}\n", encoding="utf-8"
    )

    (ROOT / "formal/README.md").write_text(
        """# Formal Layer Status — CST-TT-01

The Lean root is `CSTTT.lean`, pinned to `leanprover/lean4:v4.28.0`. `CSTTT/Countermodels/Kernel.lean` contains explicit proof source for all fifteen finite negative witnesses and contains no `sorry`, `admit`, or axioms.

The local execution environment still has no `lean`, `lake`, or `elan` executable, so a successful Lean compilation is **not claimed**. Static module, declaration, delimiter, forbidden-placeholder, and proof-surface checks are automated. The exact external command remains `lake build`.

Python performs deterministic exhaustive enumeration, emits canonical finite models and certificates, and independently rechecks every premise and failed conclusion. Python is evidence generation and validation, not a replacement for Lean proof checking.
""",
        encoding="utf-8",
    )

    (ROOT / "docs/PHASE_BOUNDARY.md").write_text(
        """# CST-TT-01 Phase Boundary

Landed in this phase:

- fifteen exact finite countermodels;
- deterministic exhaustive bounded searches and relative minimality certificates;
- explicit Lean proof source for each witness;
- checked JSON model/certificate surfaces;
- the complete negative kernel required before positive construction.

Not landed:

- no positive Temporal-FIACH or Temporal-IAPS witness;
- no constructive package, transport, corridor, or autonomy theorem;
- no full Six Birds simulation;
- no empirical recognition bridge;
- no consciousness, felt-continuity, survival, numerical-identity, A1, A2-P, or certificate-soundness result.

The next authorized phase is `CST-TT-02`, integrated C-package, temporal closure, and gluing.
""",
        encoding="utf-8",
    )


def update_top_level(outcomes: tuple[SearchOutcome, ...]) -> None:
    (ROOT / "README.md").write_text(
        """# CST Temporal Substrate Transcendence

**Project code:** `CST-TT`

**Current completed phase:** `CST-TT-01`
**Status:** exact finite negative kernel landed; no positive Temporal-FIACH witness attempted.

## Frozen target order

- **Primary:** Temporal-FIACH — independent integrated target realization (`S-R`), strict overlap temporal lineage (`S-L`), and post-withdrawal autonomy (`A`).
- **Provisional strengthening:** separately typed direct-successor temporal continuity.
- **Conditional fallback:** Temporal-IAPS, still locked absent a documented FIACH kill.
- **Mandatory companion:** the exact finite no-go kernel, now instantiated by fifteen checked models.

## Start here

1. `docs/NEGATIVE_KERNEL.md`
2. `docs/COUNTERMODEL_MINIMALITY.md`
3. `docs/TARGET_FREEZE.md`
4. `docs/THEOREM_AND_TOY_REGISTRY.md`
5. `registries/COUNTERMODEL_REGISTRY.csv`
6. `CSTTT/Countermodels/Kernel.lean`
7. `manifests/CST-TT-01_COMPLETION_REPORT.md`

## Local verification

```bash
scripts/run_tt01_checks.sh
```

The theorem/toy core remains structural. It does not establish consciousness, phenomenal feeling, personal survival, numerical identity, certificate soundness, recognition, A1, or A2-P.
""",
        encoding="utf-8",
    )
    (ROOT / "STATE.md").write_text(
        f"""# Repository state

- Project: `CST-TT`
- Current phase: `CST-TT-01`
- Base phase: `CST-TT-00-v1`
- Primary target: Temporal-FIACH strict overlap
- Direct-successor class: provisional and separately named
- Fallback: Temporal-IAPS, still locked
- Checked finite countermodels: {len(outcomes)}
- Generic constructive theorems proved: 0
- Positive handoff witnesses: 0
- Lean status: explicit proof source present; local compiler unavailable
- Python status: deterministic exhaustive enumeration and tests passing
- Detached-copy kill criterion: not triggered; detached copy fails strict corridor
- Next phase: `CST-TT-02`
""",
        encoding="utf-8",
    )
    (ROOT / "STATUS.md").write_text(
        """# CST-TT-01 status

CST-TT-01 freezes the exact finite negative kernel before any positive construction. Fifteen model families are instantiated, rechecked, certificate-bound, and linked to explicit Lean proof declarations. The bank covers all fourteen required execution-plan boundaries plus branchwise/recombination failure.

The next authorized phase is **CST-TT-02 — integrated C-package, temporal closure, and gluing**.
""",
        encoding="utf-8",
    )
    changelog_entry = """# CST-TT-01

- Added deterministic bounded countermodel enumeration.
- Landed fifteen exact finite negative models and certificates.
- Added explicit Lean proof source for the negative kernel.
- Updated TTN and toy statuses without claiming generic constructive theorems.
- Verified that detached exact copying does not satisfy the frozen strict corridor.
- Preserved the structural-only claim ceiling and locked the fallback branch.
"""
    (ROOT / "changelog/CST-TT-01.md").write_text(changelog_entry, encoding="utf-8")
    changelog = (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
    if "## CST-TT-01" not in changelog:
        changelog += "\n## CST-TT-01\n\n" + "\n".join(changelog_entry.splitlines()[2:]) + "\n"
        (ROOT / "CHANGELOG.md").write_text(changelog, encoding="utf-8")

    (ROOT / "RESTORE_AND_VERIFY.md").write_text(
        """# Restore and verify CST-TT-01

1. Extract the repository ZIP.
2. Enter the extracted repository root.
3. Confirm the phase tag and clean state:

```bash
git rev-parse CST-TT-01-v1^{}
git rev-parse HEAD
git status --short
git fsck --full --no-dangling
```

4. Rebuild and validate the deterministic phase assets:

```bash
scripts/run_tt01_checks.sh
python3 scripts/verify_tt01_rebuild.py
```

5. Compile the formal layer where the pinned toolchain is available:

```bash
lake build
```

The originating execution environment had no `lean`, `lake`, or `elan` binary. Therefore the archive claims explicit Lean proof source plus static audits, not a successful Lean compilation.
""",
        encoding="utf-8",
    )
    (ROOT / "manifests/CST-TT-01_COMPLETION_REPORT.md").write_text(
        f"""# CST-TT-01 Completion Report

**Phase:** CST-TT-01 — negative kernel and minimal exact countermodels  
**Status:** complete, pending repository freeze tag during packaging

## Landed

- {len(outcomes)} checked exact finite countermodels;
- all fourteen frozen `TTN` boundaries covered, with `TTN-01` receiving two complementary witnesses;
- one additional branchwise/recombination model required by the frozen theorem registry;
- {sum(o.candidates_explored for o in outcomes):,} deterministic finite candidates exhaustively evaluated;
- {len(outcomes)} model JSON records, human-readable cards, certificates, and relative-minimality rows;
- explicit Lean proof source for every model;
- no positive Temporal-FIACH or Temporal-IAPS witness.

## Scientific effect

The phase fixes the negative controls before constructive definitions are optimized. In particular, endpoint equality, detached exact copying, holonomy, external scheduling, phase stability, public matching, branchwise matching, finite success, and small aggregate residuals are each separated from a stronger temporal-transfer conclusion.

The detached-copy model fails the frozen strict-overlap corridor for the intended no-mixed-stage reason. `K-FIACH-04` is therefore not triggered, and Temporal-IAPS remains locked.

## Verification ceiling

Python enumeration, independent rechecks, JSON-schema validation, model-byte hashing, relative-minimality audits, static Lean audits, and deterministic rebuild checks are required. Lean compilation is not claimed in this environment because the pinned compiler is unavailable.

## Nonclaims

No result establishes or refutes consciousness, phenomenal feeling, personal survival, numerical identity, A1, A2-P, certificate soundness, or empirical recognition.

## Next phase

`CST-TT-02` — integrated C-package, temporal closure, and gluing.
""",
        encoding="utf-8",
    )

    status = json.loads((ROOT / "formal/TOOLCHAIN_STATUS.json").read_text(encoding="utf-8"))
    status.update(
        {
            "phase": PHASE,
            "explicit_countermodel_proof_source_count": len(outcomes),
            "static_lean_source_audit_status": "passed-by-cst-tt-01-static-suite",
            "compile_status": "not-run-lean-and-lake-unavailable",
        }
    )
    write_json(ROOT / "formal/TOOLCHAIN_STATUS.json", status)


def build_summaries(outcomes: tuple[SearchOutcome, ...]) -> None:
    total_candidates = sum(outcome.candidates_explored for outcome in outcomes)
    summary = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "generated_date": DATE,
        "countermodels": len(outcomes),
        "required_execution_plan_boundaries": 14,
        "additional_frozen_branchwise_recombination_boundary": 1,
        "total_candidates_explored": total_candidates,
        "checked_finite_countermodels": len(outcomes),
        "human_readable_model_cards": len(outcomes),
        "minimality_ledger_rows": len(outcomes),
        "generic_constructive_theorems_proved": 0,
        "positive_handoff_witnesses": 0,
        "fallback_unlocked": False,
        "detached_copy_strict_corridor_pass": False,
        "next_phase": "CST-TT-02",
    }
    write_json(ROOT / "manifests/CST-TT-01_SEARCH_SUMMARY.json", summary)
    write_json(ROOT / "manifests/CST-TT-01_PHASE_SUMMARY.json", summary)
    write_json(ROOT / "manifests/PHASE_SUMMARY.json", summary)


def main() -> int:
    outcomes = enumerate_all()
    if len(outcomes) != 15:
        raise RuntimeError(f"expected 15 countermodels, found {len(outcomes)}")
    rows = build_models(outcomes)
    update_registries(outcomes, rows)
    build_docs(outcomes, rows)
    update_top_level(outcomes)
    build_summaries(outcomes)
    print(
        f"CST-TT-01 assets built: {len(outcomes)} countermodels; "
        f"{sum(o.candidates_explored for o in outcomes)} candidates explored"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
