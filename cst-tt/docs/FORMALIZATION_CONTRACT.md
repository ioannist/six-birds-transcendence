# Executable Formalization Contract

## Toolchains

- Lean: `leanprover/lean4:v4.28.0`
- Python: `3.13.5` with the exact observed package versions in `requirements-lock.txt`
- Lean dependency policy for CST-TT-00: core Lean + `Std`; no Mathlib dependency is required by the scaffold

## Trust boundary

Lean is intended to define the semantics and check later proof terms and finite certificates. Python is intended to enumerate finite candidates, canonicalize data, validate schemas, and emit certificates. Python enumeration is never a proof oracle.

CST-TT-00 contains statement and certificate interfaces only. All theorem rows are `open-scaffold`; all toy rows are `specified-not-implemented`; all example certificates are `not-evaluated` or `scaffold-only`.

## Definition registry

| ID | Definition | Lean module | Lane | Depends on |
|---|---|---|---|---|
| D-001 | CarrierId | CSTTT/Core/Carrier.lean | M | — |
| D-002 | Carrier | CSTTT/Core/Carrier.lean | M | D-001 |
| D-003 | CarrierPair | CSTTT/Core/Carrier.lean | M | D-002 |
| D-004 | Stage | CSTTT/Core/Episode.lean | M | — |
| D-005 | Event | CSTTT/Core/Episode.lean | M | D-001;D-004 |
| D-006 | Dependency | CSTTT/Core/Episode.lean | M | D-005 |
| D-007 | Episode | CSTTT/Core/Episode.lean | M | D-003;D-006 |
| D-008 | TemporalAlphabet | CSTTT/Temporal/Signature.lean | S-T | D-002 |
| D-009 | PredictiveNow | CSTTT/Temporal/Signature.lean | S-T | D-008 |
| D-010 | TemporalSignature | CSTTT/Temporal/Signature.lean | S-T | D-009 |
| D-011 | TemporalClosureSpec | CSTTT/Temporal/Closure.lean | S-R | D-002;D-010 |
| D-012 | TemporalClosureWitness | CSTTT/Temporal/Closure.lean | S-R | D-011 |
| D-013 | ClockTranslation | CSTTT/Temporal/Clock.lean | S-T | D-008 |
| D-014 | RouteComparison | CSTTT/Temporal/Clock.lean | S-T | D-013 |
| D-015 | ClauseId | CSTTT/Package/Clauses.lean | S-R | — |
| D-016 | ClauseSpec | CSTTT/Package/Clauses.lean | S-R | D-015 |
| D-017 | ClauseWitness | CSTTT/Package/Clauses.lean | S-R | D-016 |
| D-018 | ClauseBundle | CSTTT/Package/Clauses.lean | S-R | D-017 |
| D-019 | JoinTree | CSTTT/Package/Gluing.lean | S-R | D-015 |
| D-020 | IntegratedPackageCertificate | CSTTT/Package/Gluing.lean | S-R | D-012;D-018;D-019 |
| D-021 | StagedClausePreservationEvidence | CSTTT/Package/Gluing.lean | S-T;S-R | D-016 |
| D-022 | TemporalBridge | CSTTT/Transport/TemporalBridge.lean | S-T | D-013 |
| D-023 | TemporalTransportCertificate | CSTTT/Transport/TemporalBridge.lean | S-T | D-012;D-022 |
| D-024 | RouteHolonomyAudit | CSTTT/Transport/TemporalBridge.lean | S-T | D-014 |
| D-025 | FlatnessCertificate | CSTTT/Transport/TemporalBridge.lean | S-T | D-024 |
| D-026 | CounterfactualAudit | CSTTT/Corridor/TemporalCorridor.lean | S-L | D-007;D-010 |
| D-027 | TemporalCorridorData | CSTTT/Corridor/TemporalCorridor.lean | S-L | D-007;D-026 |
| D-028 | TemporalCorridorCertificate | CSTTT/Corridor/TemporalCorridor.lean | S-L | D-027 |
| D-029 | DirectSuccessorCertificate | CSTTT/Corridor/DirectSuccessor.lean | S-L | D-006;D-023 |
| D-030 | ControlledSystem | CSTTT/Autonomy/System.lean | A | D-002 |
| D-031 | WithdrawalSpec | CSTTT/Autonomy/System.lean | A | D-001 |
| D-032 | ControlledInvariantCertificate | CSTTT/Autonomy/System.lean | A | D-030 |
| D-033 | AutonomyCertificate | CSTTT/Autonomy/System.lean | A | D-031;D-032 |
| D-034 | ClaimLane | CSTTT/Targets/TemporalFIACH.lean | M | — |
| D-035 | TemporalFIACHCertificate | CSTTT/Targets/TemporalFIACH.lean | S-R;S-L;A | D-020;D-028;D-033 |
| D-036 | TemporalFIACH | CSTTT/Targets/TemporalFIACH.lean | S-L | D-035 |
| D-037 | OperationalSeed | CSTTT/Fallback/Ancestry.lean | S-L | D-006 |
| D-038 | AncestryClosure | CSTTT/Fallback/Ancestry.lean | S-L | D-037 |
| D-039 | IAPSCertificate | CSTTT/Fallback/Ancestry.lean | S-R;S-L;A | D-020;D-033;D-038 |

## Module dependency rule

Primitive layers may import only earlier layers. In particular:

- `Temporal` must not import `Corridor` or `Targets`.
- `Package` must not import `Corridor`, `Autonomy`, or `Targets`.
- `Transport` must not import `Corridor` or `Targets`.
- `Corridor` may import transport and episode data but not the aggregate target.
- `Autonomy` must not import corridor or aggregate target definitions.
- Only `Targets` aggregates package, corridor, and autonomy evidence.

The circularity validator scans primitive Lean modules and certificate-schema field names for verdict-equivalent vocabulary.
