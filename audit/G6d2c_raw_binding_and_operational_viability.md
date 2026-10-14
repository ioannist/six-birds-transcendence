# G6d-2c continuation: operational rule and POS-04 game binding

## Proved boundary

### Generic finite operational C8 rule

`OperationalViability` is polymorphic in state, action, outcome, owner and typed
cell namespace. The raw row numerator scale, prices, recharge, owner and carrier
enumerations vary. It imports no POS-04 definition. The operator checks funded
owned resource availability and existence of a nonempty normalized action row
whose entire positive support is retained. It defines the greatest viable set
using `ViableSet`; monotonicity, fixed-point equality, viability and containment
of **every** viable set are proved. Availability never changes a funded row.

The rule checks a declared ledger protocol, conservation and canonical policy
row reconstruction. This is the context-free finite operational fragment; it is
not a claim that arbitrary context-dependent run recipes factor through it.
The four-cell Option decoder has locality and universal missing-cell rejection.
General row well-formedness remains an independent computed input check.

`POS04OperationalViability.generic_c8_iff` proves both directions for arbitrary
partial POS-04 assignments on both tags. The operator/greatest-set equations are
also exact for arbitrary assigned rows, policies, ledgers and resources. Controls
transfer, including source acceptance after target underfunding and receiver
withdrawal: `withdrawn_control_equivalence`. All four cell families have guards,
including each ledger subfield. No source-presence condition is added to package
C8.

### Shared-assignment POS-04 game binding

`POS04GameBinding` is explicitly a **POS-04 interface specialization**, not the
completed polymorphic RawHandoff. Its only model argument is `RawLaneModel`.
No semantic predicate, code, observer, updater or entry set is a caller argument.

- `data`, `rows`, `update`, `code`, `observer`: defined from the shared withdrawn
  assignment and existing assigned C6 dynamics.
- `Entries`: all activated/realized phase-2 positive-support entries; no reset to
  a selected receiver. Acquisition completeness rejects source-row deletion.
- `Withdrawal`, `ResourceClosed`, `Legal`, `StepLaw`: decoded retained resource,
  owner, availability, ledger and actual updater/observation equations.
- `PackageAt`: the same arrival `PackageLane`, recomputed withdrawn assigned
  clauses, state-view resolution at the actual run factor, and actual readout
  update equations. Historical acquisition cells are not source availability
  for post-withdrawal responses.
- The nominal disturbance type is separate from actions and provably nonempty;
  its explicit list covers every disturbance of that specialization.

`full_soundness` and `operational_soundness` instantiate the independent game
induction theorem with these defined predicates. Their invariant certificates
store only auxiliary inside/response witnesses with proved obligations, not an
autonomy readout. `full_implies_arrival_package` derives AF→P at a genuine entry
using `game_same_package_implies_arrival`.

The response dependency scope is the union of the existing autonomy scope and
the full target C6 scope. Thus absent predictive rows/hazards/positions, ticks,
ledger, writers, routes or other consumed primitives reject before defaults can
support game acceptance. Missing acquisition dependencies independently produce
no entries. The game directly rejects source-absent acquisition and absent
retained recharge; these are readout negations, not failed-check attribution.

`assigned_full_future` preserves assigned C6's **all-state, all-word** sufficiency
quantifier, under its separate computed C6 acceptance. `funded_closure_updates`
proves conserved positive funding, record increment and retained residue on the
entire assigned C6 closure. No autonomy→C6 implication is asserted.

## Argument / field coverage

| Layer / argument | Classification | Check or proof |
|---|---|---|
| C8 types and finite lists | Raw interface | Domain coverage, nodup, nonempty actions, positive scale |
| C8 rows and policy | Raw cells | Exact row closure and policy-P reconstruction; `rows_guard`, `policy_guard` |
| C8 owner and recharge | Raw cells | Availability and ledger; `owner_guard`, `recharge_guard` |
| C8 initial budget, cost, return | Raw cells | Declared ledger and conservation; `budget_guard`, `cost_guard`, `return_guard` |
| C8 namespace and bindings | Raw typed references | Decoder locality and every-scope-cell `missing_rejected` |
| C8 greatest set | Defined object | ViableSet computation, monotonicity/fixed-point/greatest proofs |
| Game `RawLaneModel` | Raw shared assignment and withdrawal fields | Defined staging, withdrawal and acquisition |
| Game disturbance domain | Defined nominal specialization | `disturbance_domain_nonempty`, `disturbance_domain_covers` |
| Game rows, updater, code and observer | Defined assigned C6 objects | `future_owned`, `updater_owned`, `all_run_readout_laws`; row completeness guard |
| Game entries | Defined acquisition execution | `missing_acquisition_dependency_rejects_both`, `source_absent_rejects_both` |
| Game package | Computed same-package/context predicate | `full_implies_arrival_package`; assigned clause completeness |
| Game resources/ownership/funding | Computed from shared withdrawn cells | `missing_rejects_full`, `missing_rejects_operational`, `recharge_withdrawn_rejects_both` |
| Game progress/ticks/record/residue/owner | Defined updater/observer equations | `StepLaw`; `funded_closure_updates` for ledger/record/residue; full lift remains below |
| Auxiliary invariant / responses | Evidence against defined semantics | `full_soundness`, `operational_soundness`, no stored game proof |

Guard prefixes in the first rows are `POS04OperationalViability`; game prefixes
are `POS04GameBinding`. These method guards are not new scientific declarations.

## Explicit outstanding gates

1. **Fully polymorphic raw game binding and C6 extraction:** the POS-04 binding
   does not generalize carrier/cell/stage/cover/audit domains. Unrestricted
   context-dependent recipes remain permitted by the hybrid contract.
2. **Actual factor-support lift:** assigned C6 futures use quotient outcomes and
   `representative6`. The response/phase-2 tables use actual factor outcomes.
   A finished game/finite adapter must prove that all actual branches lift and
   preserve the required context, not merely reset each class to its chosen
   representative. No `GameFiniteConstructor.LiftWitness` for POS-04 is claimed
   in this seam; no equivalence of these new game readouts with G6 `AF`/`AO` is
   claimed yet.
3. **Positive game nonemptiness and control vectors:** canonical F/O finite
   checks remain proved in G6c; they have not yet been transported to the new
   run-space game readouts. The conditional soundness lemmas alone do not
   establish that new certificates are inhabited.
4. **Generic temporal C6 family equivalence:** reusing the assigned C6 sufficiency
   theorem is not the completion of its polymorphic extraction. Full-future
   bisimulation and per-field closure guards remain required there.

These are completion gates, not applied narrowings. No status promotion. Existing
Lean declarations and registry statements are unchanged. New raw-rule, adapter
and game-binding definitions/theorems are (b) additions for TTH-06. No (a) rename.

## Verification and self-review

- `cd lean && lake build`: exit 0, 378 jobs. The new operational module built
  in 1.8s, its POS-04 adapter in 2.5s, and the game binding in 1.5s. No new
  module warnings.
- `scripts/validate_lean.sh`: exit 0; inventory matches; 210 registered
  declarations resolve; no untrusted axioms, placeholders or gating vacuity
  findings. The 29 reported heuristic leads are pre-existing.
- Read-only `/tmp` probes for all 54 new theorems: 52 use a subset of
  `propext`, `Classical.choice`, `Quot.sound`; two use no axioms.
- Forbidden-construct scan on the three new modules and `git diff --check`:
  clean. No frozen science files, registry or inventory changed.

Self-review traced the Option decoder into the arbitrary-partial-assignment
equivalence, and the activated entry into the game readout and arrival-package
implication. Invariant soundness is a conditional construction; it does not
prove positive certificate inhabitation. The actual-support lift and generic
C6 binding above are therefore unresolved completion gates, not evidence for
promotion. Unrelated `paper/` and concurrent playbook edits were left untouched.
