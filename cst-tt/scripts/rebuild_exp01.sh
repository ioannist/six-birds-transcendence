#!/usr/bin/env bash
# Rebuild all CST-EXP-01 corpus products from the source archives embedded in the repository.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/cst-exp01-rebuild.XXXXXX")"
cleanup() { rm -rf "$TMP"; }
trap cleanup EXIT

PAPERS="$TMP/papers"
CONSCIOUSNESS="$TMP/consciousness"
PARSED="$TMP/parsed"
mkdir -p "$PAPERS" "$CONSCIOUSNESS" "$PARSED"

unzip -q "$ROOT/inputs/source_archives/six_birds_papers_tex.zip" -d "$PAPERS"
unzip -q "$ROOT/inputs/source_archives/six-birds-consciousness_v41.zip" -d "$CONSCIOUSNESS"

python "$ROOT/scripts/extract_corpus.py" \
  --papers-dir "$PAPERS" \
  --triage "$ROOT/inputs/normative/PAPER_TRIAGE.md" \
  --out-dir "$PARSED"

python "$ROOT/scripts/build_exp01_assets.py" \
  --repo "$ROOT" \
  --papers-dir "$PAPERS" \
  --consciousness-dir "$CONSCIOUSNESS" \
  --parsed-dir "$PARSED" \
  --source-zip "$ROOT/inputs/source_archives/six_birds_papers_tex.zip"

python "$ROOT/scripts/enrich_exp01_assets.py" \
  --repo "$ROOT" \
  --papers-dir "$PAPERS" \
  --parsed-dir "$PARSED"

if command -v dot >/dev/null 2>&1; then
  dot -Tsvg "$ROOT/corpus/asset_atlas/dependency_graph.dot" \
    -o "$ROOT/corpus/asset_atlas/dependency_graph.svg"
  dot -Tpng "$ROOT/corpus/asset_atlas/dependency_graph.dot" \
    -o "$ROOT/corpus/asset_atlas/dependency_graph.png"
else
  printf '%s\n' 'warning: Graphviz dot not available; retained graph sources were rebuilt but PNG/SVG were not regenerated' >&2
fi

python "$ROOT/scripts/validate_exp01.py" --repo "$ROOT"
printf '%s\n' 'CST-EXP-01 rebuild and validation completed.'
