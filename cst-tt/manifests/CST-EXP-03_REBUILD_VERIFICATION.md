# CST-EXP-03 Portable-Rebuild Verification

**Status:** PASS
**Date:** 2026-08-09
**Deterministic surfaces compared:** 52
**Byte-identical surfaces:** 52/52
**Rebuilt validator:** 249/249 PASS
**Graphviz regeneration used:** yes

## Method

A clean temporary copy was made without Git metadata or Python caches. The CST-EXP-03 builder regenerated every phase text/CSV/JSON surface. Candidate design-space SVG and PNG files were regenerated when Graphviz was available. The rebuilt copy then ran `scripts/validate_exp03.py --skip-manifest`. SHA-256 hashes for all declared deterministic surfaces were compared against the source snapshot.

## Result

All declared deterministic surfaces reproduced byte-for-byte, and the rebuilt validator passed.

Mismatches: none.

This verifies deterministic repository reconstruction and internal validation. It does not establish the scientific correctness of any candidate schema.
