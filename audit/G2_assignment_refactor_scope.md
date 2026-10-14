# G2 — assignment-indexed package refactor: scope stop

## Disposition

**G2 is not implemented. TTH-02 remains `conditional`.** This note invokes the packet's explicit stop condition: “If that is too large for one packet, stop and report the scope.” The required POS-04 assignment-indexed C1–C8 refactor exceeds one small review round. This is an implementation-scope finding, **not** a proof that TTH-02 is false or infeasible. No Lean or registry statement has been changed and no promotion is proposed.

The gluing/locality argument itself is feasible. The obstruction to completing the packet is its required substantive POS-04 instance, including every primitive-field guard and the existing controls. Merely combining the current positive package theorem with TTH-01 would leave the acceptance gap intact.

## Exact evidence

The row's unchanged exact statement is:

> Separately typed, total, value-preserving source-to-target clause maps plus an independently valid target gluing certificate assemble one integrated target package without using lineage or autonomy premises.

The accepted contract is `audit/G0_generic_contracts.md:17-31`. It requires target acceptance evaluated on the **defined mapped assignments**, and locality transferring those checks to the **defined glued assignment**.

The current coordinate type has no value:

```lean
-- lean/CSTTT/POS04/Data.lean:302-311
structure Coordinate where
  tag : Tag
  state : KState
  clause : Clause
  deriving DecidableEq, Repr

def coordinates : List Coordinate :=
  tags.flatMap fun tag => kernel.flatMap fun state =>
    clauses.map fun clause => ⟨tag,state,clause⟩
```

`primitiveRefs` (`Data.lean:320-328`) supplies lists of table references. It does not provide a coordinate-to-primitive-value assignment or decode clause data from such an assignment.

The existing package checks also have no assignment argument:

```lean
-- lean/CSTTT/POS04/Assembly.lean:224-231
def PackagePass (v : C8Variant) (tag : Tag)
    (variants : ClauseVariants := {}) : Prop :=
  CoordinatesComplete ∧
  C1FactorPass tag variants.c1 variants.profile ∧
  C2Pass variants.lower tag ∧
  C3Pass variants.profile variants.lower tag ∧
  C4Surrogate variants.c4 tag ∧ C5Surrogate variants.c5 tag ∧
  C6Pass variants.c6 tag ∧ C7Pass variants.c7 tag ∧ C8Pass v tag
```

Their inputs select a finite family of interventions against fixed POS-04 definitions; they do not supply arbitrary primitive tables through an assignment. The package theorem (`Assembly.lean:233`) proves the fixed positive instance. It does not establish assignment-sensitive locality.

The prior TTN-08 disclosure already says precisely this:

> The 160 L5 coordinates enumerate `(tag,state,clause)` slots but have no assignment value or assignment-sensitive acceptance function. `PackagePass` checks model data, not a supplied local `GlobalAssignment`.

Source: `lean/CSTTT/POS04/CyclicObstruction.lean:7-10`; its follow-up at lines 18-20 requests the missing assignment-indexed checks and equivalence proofs. Its `cycleSpec` (`:104` onward) adds an equality rule to fixed package side conditions. G2 expressly excludes that shortcut.

## Required primitive refactor

The following is an inventory of work still required, **not a table of implemented predicates**. All grades remain unchanged: C1–C3 substantive on the exact T1 factor; C8 substantive operational viability; C4–C7 POS-04 surrogates. No full P05 or T17-I instance is claimed.

| Clause | Raw values the assignment must provide or resolve to actual values | Existing dependency that must be parameterized / linked | Required equivalence and control |
|---|---|---|---|
| C1 | Actual action rows, hazards/public readout, ordered M prototypes, P/C/U and the audit parameters/certificates | `Assembly.lean:34-112,194-203`: raw M/C/U/P reconstruction plus transported probability, uniqueness, retention, TV and both defects | Canonical assignment recovers `C1FactorPass`; actual row drift rejects via reconstruction. Keep L4 audit and transport theorems; do not re-prove their numbers or store audit verdicts. |
| C2 | Public channel/readout and the action/hazard data used to compute M | `C2C3.lean:11-39`: `rawM` reads fixed `actionRow`; `lowerReadout` reads a fixed public-position function | Recover `C2Pass`; the expanded public view rejects the split. A coordinate label standing in for M is insufficient. |
| C3 | Raw action rows, public profile seed, exit labels and finite state/action domains | `C2C3.lean:99-134`: refinement reads `profileRow`, fixed domains and `rawMFor` | Recover the actual 6→7→7/stability/terminal-M checks. `NEG-C3-PROFILE` must still pass C3 as computed; its C1 effect remains separate. |
| C4 | Current channels, raw predictive readout, connector history and actual support rows | `C4C5.lean:26-54`: current/connector/exposure checks read fixed tables | Recover `C4Surrogate`, including its full-HIDD-failure disclosure; preserve the expanded-channel control. |
| C5 | Generator edge/channel/owner/housing data and supported history anchors | `C4C5.lean:133-157`: product credit and owner consistency use fixed protocol/history data | Recover `C5Surrogate` and the external/internalized outcomes from assigned generator data. No stored credit. |
| C6 | Action/hazard/M data; raw tick and writer tables; events and realization; route register; owner/resources/ledger; fixed observation/update recipes | `C6.lean:273-292,378-391`: all-word F, bisimulation and coarseness use fixed `effectiveMass`, q, observation and successor. G1c supplies the generic closure/readout discipline | Recover `C6Pass`, its all-word proof, and future/record controls. Assignment changes must propagate to code, observation, mass and successor together. Do not pass an independent future model or assume future sufficiency. |
| C7 | Both branch histories, joint coupling, indexed reassembly, observable interface, receiver activation/display and realized events | `C7.lean:78-106`: operational use and transport still read fixed receiver/event/action data | Recover `C7Pass`; aggregate, uncoupled and transport controls keep their actual outcomes. A coupling-table change must feed both joint readout and receiver display. |
| C8 | Actual action supports, policy domain, owned recharge resources and ledger parameters | `C8.lean:13-62`: availability, pruning and gfp read fixed rows/resources/ledger. `:113-115` proves fixedness by cases on the existing variant family | Recover `C8Pass`; pruning, fixedness and greatestness must apply to decoded raw data, with underfunding empty. Operational package viability is not a post-withdrawal autonomy premise. |

These dependencies cross clause boundaries: action rows and M feed C1–C4, C6, C7 support and C8; histories feed C5/C7; resources and realization feed C6/C7/C8. The refactor must share those assigned raw values rather than copy them into independent clause payloads that can disagree. C1's universal fixed-distribution claim and C6's unbounded-word claim cannot be replaced by stored Booleans.

The existing relevant modules total 2,330 lines (`Data`, `Assembly`, `C2C3`, `C4C5`, `C6`, `C7`, `C8`). This is a dependency footprint, not a claim that all those lines need rewriting. The largest proof bridges are arbitrary assigned row data → T1 audit reconstruction, assigned temporal data → defined all-word dynamics, and assigned ledger/support → computed viable fixed point. Each needs its own equivalence and sensitivity review.

## What must not count as a repair

1. `accepts := fun assignment => PackagePass ... ∧ assignmentHasExpectedLabels assignment`: the substantive clause proposition still ignores assignment values. This repeats TTN-08's side-condition construction.
2. A table of stored acceptance/credit/viability flags or `accepted : Clause → Prop`: exactly the projection pattern G2 forbids.
3. Exchanging an assignment only for `ClauseVariants` names and reusing the old fixed-table calls: this would still leave the underlying primitive values outside the assignment. Mutation selectors can remain compatibility adapters; they are not the new raw-value semantics.
4. Supplying mapped assignments, target witnesses or a glued global as theorem arguments. All must be definitions over the same raw package/map data.
5. Omitting C1 uniqueness or C6 all-word sufficiency to make clause evaluation decidable. Finite raw certificates/one-step equations may be checked, but their substantive conclusions must be derived.

## Argument classification — implementation contract, pending

No new generic theorem exists in this packet. This table records the accepted theorem's intended arguments so a split implementation does not repeat the previous candidate loopholes.

| Intended argument/object | Classification | Required treatment |
|---|---|---|
| Carrier/coordinate/value types and finite domains | Raw data | Typed independently on source and target. |
| `m : RawPackage` | Raw data | Primitive-value assignments, scopes, raw clause-rule inputs, finite cover/parent/rank data and declared grades. No accepted verdict fields. |
| `f : RawStageMap m` | Raw data | Total typed coordinate/value maps; typed inverse/section data if needed for defined pullback. |
| `hsource : SourcePackagePass m` | Evidence on raw data | Each source evaluator/gate is run on the source assignment decoded from m. |
| `hmap : StageMapEquations m f` | Evidence on raw data | Scoped coverage and actual values; inverse/section consistency and any many-to-one fiber agreement. |
| `hlocal : ClauseLocality m` | Evidence on raw data | Equality on required coordinates implies evaluator/gate equality; preferably derived from scoped decoding. |
| `htarget : TargetLocalChecks m f` | Evidence on raw data | Evaluators/gates applied to the defined mapped assignments, never a supplied target verdict table. |
| `hcompat : EdgeCompatible (mappedLocal m f)` | Evidence on raw data | Computed parent adjacency, actual overlaps and mapped values. |
| Mapped assignments, rule verdicts, validated join tree, glued global, target witness | Defined objects | Not arguments. Construct using raw map/cover data and TTH-01, then derive global acceptance by locality. |
| Lineage, corridor, bridge, withdrawal/autonomy proof | Absent | No such theorem parameter. C8 resource/ledger data and operational viability remain package content. |

The no-lineage/no-autonomy theorem must be an actual construction with this parameter list (and optionally a corollary universally independent of unrelated lane data). A comment about not calling an autonomy theorem is insufficient.

## Field coverage — promotion blockers, not proved guards

Every row below is **PENDING/BLOCKER** until the implementation supplies its law and a proved guard. No guard names are fabricated as existing declarations.

| Raw field family | Required law/check | Required single-field sensitivity witness |
|---|---|---|
| Coordinate maps | Total typing, source-scope image, target coverage and pullback/section consistency | Constant map loses a required distinct target coordinate. |
| Value maps | Typed transformation and pointwise raw-value preservation at every mapped slot | Constant/broken map changes an actual discriminating row/readout/coupling value. |
| Source value assignment | Scoped decoding plus actual source clause/gate checks | Missing or corrupted required primitive fails the clause check. |
| Scopes | Cover required decoder accesses and respect staged coordinate maps | Delete a required primitive coordinate; acceptance must not silently read a global fallback. |
| Clause raw rules/inputs | Clause-specific actual algorithms; canonical-assignment equivalence to each POS-04 clause | Actual per-clause primitive perturbation changes the corresponding result, with C3's recorded exception respected. Constant-acceptance rule must not be accepted as the clause's authoritative rule. |
| Hard gates | Computed from assigned discrete/resource data; separate from any soft aggregation | Delete a required input or essential resource; a gate fails independently. |
| Cover/parent/rank | Coverage, root/no-parent, total nonroot parents, decreasing ranks, running intersection | Broken parent/cycle or missing coordinate coverage fails the tree check. |
| Adjacency | Defined from the checked parent map, not independently supplied | A broken parent variant cannot leave a stale valid adjacency; guard the parent/derived adjacency pair. |
| Cross-clause shared primitive data | All decoders access one assignment for shared rows, ownership, resources and realization | A changed shared primitive reaches every dependent evaluator; no stale model-global tables. |

A constant map or invariant value is not universally invalid: the guard must choose one that violates an actual law on this model. Likewise changing a valid acyclic cover to another valid cover is not a negative. These are concrete discriminating tests, not arbitrary syntactic bans.

## Suggested review sequence

This sequence separates implementation reviews; it proposes no new science data, thresholds or model version. Raw positive values must be derived from the already frozen POS-04 tables and existing controls, with provenance/equivalence. Any new scientific control beyond sensitivity probes needs the established declaration/evaluation discipline.

1. **G2a — raw assignment substrate and C1–C3 (L).** Define actual primitive-value cells/views for the 160 logical slots and shared table dependencies. Decoders only read their declared scopes and fail on missing inputs. Lift action/public/hazard/profile algorithms and C1 reconstruction to these values; prove exact positive equivalence and existing controls. Keep legacy APIs via canonical adapters. No promotion.
2. **G2b — C4–C8 assigned-data evaluation (L; split by clause if needed).** Finish current-channel/credit, temporal, joint-operation and ledger/gfp adapters. Reuse G1c's defined dynamics/update gates for C6. Prove all clause equivalences and actual negative outcomes. Prove decoding locality. No promotion until all eight are covered.
3. **G2c — generic staging/gluing and POS-04 arrival instance (M).** Define mapped locals from typed raw maps, define/validate the raw join-tree presentation and induced adjacency, apply TTH-01, and derive all global clause/gate checks by locality. Prove the generic construction, no-lane signature, nonempty POS-04 instance, field guards and package controls. Only then update TTH-02/inventory and run promotion validation.

This is the smallest review decomposition I recommend after tracing the dependencies. It does not demote or weaken TTH-02. Its eventual ceiling remains the declared structural package with C4–C7 surrogates, not full P05. TTH-01's gluing/restriction theorem is reused; acceptance/hard gates still need their real assignment-sensitive proofs.

## Checks and changes

Only this new scope note is changed. No Lean, registry, inventory, frozen model or cst-tt file is edited. There are **no statement changes**, no new declarations and no G2 promotion. Build/validator receipts are appended after their read-only rerun.

Read-only verification receipts:

- `cd lean && lake build`: exit 0; `Build completed successfully (300 jobs).` Existing unused-variable warnings remain; no Lean code was changed.
- `scripts/validate_lean.sh`: exit 0; all 39 rows and 174 row declaration entries checked (165 theorem-kind, 8 statement-only, 1 other definition). Inventory matches. No untrusted axioms; trusted set is `Classical.choice`, `Quot.sound`, `propext`.
- Source scan: 0 placeholders, 0 high-confidence vacuity findings, 9 non-gating ignored-input heuristic leads.
- Validator receipt: `lean/.validate-logs/run-20260930T121153-119909Z/report.json` (gitignored).
- `git diff --check`: exit 0. Final tracked diff is empty; the only untracked deliverable is this scope note. Frozen CST-TT-08 files, the 09 row and inventory remain unchanged.
