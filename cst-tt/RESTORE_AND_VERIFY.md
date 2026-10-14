# Restore and verify CST-TT-08

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
