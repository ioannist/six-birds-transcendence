#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST_DIR = ROOT / "manifests"
EXCLUDED_PATHS = {
    "manifests/MANIFEST.json",
    "manifests/CST-TT-08_MANIFEST.json",
    "manifests/SHA256SUMS",
    "manifests/CST-TT-08_SHA256SUMS",
    "manifests/REPO_TREE.txt",
}
SKIP_DIR_NAMES = {".git", ".pytest_cache", "__pycache__", ".lake", "build", "dist"}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sync_canonical_surfaces() -> None:
    copies = {
        "CST-TT-08_VALIDATION_REPORT.md": "VALIDATION_REPORT.md",
        "CST-TT-08_VALIDATION_RESULTS.json": "VALIDATION_RESULTS.json",
        "CST-TT-08_REBUILD_VERIFICATION.md": "REBUILD_VERIFICATION.md",
        "CST-TT-08_REBUILD_VERIFICATION.json": "REBUILD_VERIFICATION.json",
        "CST-TT-08_PHASE_SUMMARY.json": "PHASE_SUMMARY.json",
        "CST-TT-08_COMPLETION_REPORT.md": "COMPLETION_REPORT.md",
    }
    for source, target in copies.items():
        source_path = MANIFEST_DIR / source
        if not source_path.is_file():
            raise FileNotFoundError(source_path)
        shutil.copyfile(source_path, MANIFEST_DIR / target)
    shutil.copyfile(ROOT / "RESTORE_AND_VERIFY.md", MANIFEST_DIR / "RESTORE_AND_VERIFY.md")


def repository_files() -> list[Path]:
    paths: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = sorted(name for name in dirnames if name not in SKIP_DIR_NAMES and not name.endswith(".egg-info"))
        base = Path(dirpath)
        for filename in sorted(filenames):
            path = base / filename
            rel = path.relative_to(ROOT).as_posix()
            if rel in EXCLUDED_PATHS:
                continue
            if filename.endswith((".pyc", ".pyo", ".tmp", ".swp", ".bak")):
                continue
            paths.append(path)
    return sorted(paths, key=lambda path: path.relative_to(ROOT).as_posix())


def main() -> int:
    MANIFEST_DIR.mkdir(parents=True, exist_ok=True)
    sync_canonical_surfaces()
    files = repository_files()
    rows = [{"path": path.relative_to(ROOT).as_posix(), "bytes": path.stat().st_size, "sha256": sha256(path)} for path in files]
    manifest = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": "CST-TT-08",
        "generated_date": "2026-08-10",
        "scope": "all non-Git repository files except self-referential manifest/checksum/tree outputs and disposable caches",
        "excluded": sorted(EXCLUDED_PATHS),
        "file_count": len(rows),
        "files": rows,
    }
    text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    for name in ("CST-TT-08_MANIFEST.json", "MANIFEST.json"):
        (MANIFEST_DIR / name).write_text(text, encoding="utf-8")

    checksum_paths = files + [MANIFEST_DIR / "CST-TT-08_MANIFEST.json", MANIFEST_DIR / "MANIFEST.json"]
    checksum_text = "\n".join(
        f"{sha256(path)}  {path.relative_to(ROOT).as_posix()}"
        for path in sorted(checksum_paths, key=lambda item: item.relative_to(ROOT).as_posix())
    ) + "\n"
    for name in ("CST-TT-08_SHA256SUMS", "SHA256SUMS"):
        (MANIFEST_DIR / name).write_text(checksum_text, encoding="utf-8")

    tree_paths = sorted({*(path.relative_to(ROOT).as_posix() for path in repository_files()),
                         "manifests/CST-TT-08_MANIFEST.json", "manifests/MANIFEST.json",
                         "manifests/CST-TT-08_SHA256SUMS", "manifests/SHA256SUMS",
                         "manifests/REPO_TREE.txt"})
    (MANIFEST_DIR / "REPO_TREE.txt").write_text("\n".join(tree_paths) + "\n", encoding="utf-8")
    print(f"CST-TT-08 manifest finalized: {len(rows)} hashed files; {len(checksum_paths)} checksum rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
