# G6d-4b: shared execution and finite snapshot boundary

## Proved

This is a **partial G6d-4b boundary**, not the completed lineage adapter.
TTH-06 remains conditional; neither its row nor the inventory changes.

- `StaticView` interprets a static raw instruction over any number of shared
  cells, with no run argument. Locality, missing-input rejection, and presence
  are proved. `ofCell_read` embeds the previous one-cell views exactly.
- Acquisition history words now use this instruction type. Their dependency
  list contains **all** consumed cells, including policy. Other acquisition
  semantics and existing rejection proofs are retained.
- `ExecutionFrontier` defines initial runs, history prefixes, snapshots,
  observations, code, futures, and closure. Its temporal interpreter uses the
  acquisition's **same** raw rows and updater. `snapshot_execution` proves actual
  supported history execution and membership in that computed closure.
- Its validity checks positive nonempty history prefixes, coverage of every
  declared history terminal, activated and realized strict paths, complete
  outcome/action domains, class-mass bisimulation, closure-wide independent
  readout recipes, and nonnegative future rows of mass zero or one.
- `soundness` derives full-interface sufficiency for **all finite words**, the
  closure laws and row laws, nonemptiness, and exact frozen-signature decoding.
  Finite snapshot images do not truncate run counters.
- `RuntimeComponents.frontier` constructs this interpreter from the committed
  shared runtime. `frontier_temporal`, `frontier_rows`, and `frontier_update`
  identify its temporal/resource/acquisition execution components.
- `ExecutionSnapshotTransport` constructs both frames from **one execution**,
  one assignment and raw typed maps. `frozen_transport` proves equality in the
  target frozen signature type, component by component, including the proved
  future proposition. Representative independence follows from the raw map
  equations; it is not a field.
- `FutureLumping.transport_one_step` preserves class-mass bisimulation through
  checked all-state encodings. `POS04RegisterFuture.one_step` binds the actual
  POS-04 register interpreter without requiring equal individual branch weights.

### POS-04 instance and limits

`POS04ExecutionFrontier.positive` proves the **source** frame on the committed
POS-04 data. Its audit is computed from the existing four snapshot selectors:
both routes at afterFirst and endpoint. Each history word uses the **assigned**
policy and actual Ambient outcomes. `canonical_rows` proves row laws on **every**
run context, and closure restriction transfers the existing independently
checked register recipes to these derived acquisition roots.

For **arbitrary partial assignments with the consumed cells present**:
`word_eq`, `initial_eq`, `actual_rows`, `actual_update`, and `prefix_check_iff`
are exact equations/biconditionals. The last compares the generic prefix gate
with a pure actual-support finite checker, not a canonical truth value.
Missing events or policy reject, as does source absence. The capped-progress
proposal agrees at the audited occurrences 1 and 2, but fails the independent
recipe at a supported future step from the executed endpoint (counter 3).
No POS-04 data or mutation declaration is edited.

This source-frame adapter does **not** certify receiver transfer: its receive
instruction is identity in the source namespace. The target acquisition/receiver
adapter, the two-sided instance of `ExecutionSnapshotTransport`, and the full
arbitrary-partial lineage biconditional remain to be constructed. The source
instance proves this interpreter boundary is inhabited, not that G6d-4b is done.

## Argument classification

| Input | Classification | Check or construction |
|---|---|---|
| Cell/register/value, action/disturbance/outcome, history/route/stage/event types | Raw interface | Typed references and declared finite-domain coverage; no fixed family in generic definitions |
| Immutable partial assignment | Raw data | Complete transitive instruction dependencies; missing reads reject |
| Initializer, static history instruction, receiver/update programs | Raw instruction data | No candidate run input to initializer/static views; supported prefix fold defines snapshots |
| Raw row instruction and alphabets | Raw data | One shared execution; outcome completeness, nonnegative closure rows of mass zero/one |
| Event/route/realization/receiver views and schema clocks | Raw data | PathsAvailable checks activation, realization, strict steps and independent positive clock increments |
| Audit selectors, occurrences, and typed component maps | Raw data | Positive bounded occurrences, terminal coverage, eight computed snapshot map equations |
| Readout and independent update-recipe instructions | Raw data | Whole-closure FieldLaw and supported PositiveRecipes checks |
| Ready/Valid evidence | Evidence on raw checks | No observer, future, code, weights, successors, snapshots, or verdict is supplied |
| Snapshot alphabets, signatures, futures and closures | Defined objects | Instruction fold, actual readouts and exact finite images |
| Old/new roots in restriction lemma; old/new models in lumping transport | Internal engine arguments | Instantiated only with the defined raw interpreters and proved all-state equations |

## Field/readout coverage and guards

| Field/dependency | Check or law | Guard/evidence |
|---|---|---|
| Histories and policy | Static instruction locality; exact word conversion | `StaticView.missing`, `missing_policy_rejected` |
| Initial coordinates | Input-only initializer, all read dependencies present | Existing acquisition initializer rejection; `initial_eq` |
| Actual row/support and successor | `rows_shared`, `updater_shared`, positive raw/aggregated support, complete outcomes | Missing source-row/update guards in AcquisitionExecution; `actual_rows`, `actual_update`, `prefix_check_iff` |
| Event/route references and realization | Own PathsAvailable gate, strict clock equations, nonempty prefixes | `missing_atomic_view`, `unrealized_path_rejected` |
| Receiver source/target/funding availability | Every ActivationField checked on each audited path | `inactive_receiver_rejected` (all fields), concrete `source_absent_rejected` |
| Predictive now | Actual readout and next-code fiber checks | Per-field `constant_readout_rejected` at `.predictive`; typed `map_field_guard` |
| Order, elapsed ticks and progress | Independent recipes; strict positive numerical checks throughout closure | Field guards `.order`, `.ticks`, `.progress`; `capped_progress_rejected` beyond the audit |
| Writer and record | Independent writer/record recipes and positive supported record growth | Field guards `.writer`, `.record` |
| Residue, maintenance and owner | Independent raw step equations throughout closure | Field guards `.residue`, `.maintenance`, `.owner` |
| All eight finite codecs | Decode/encode identity and typed map commutation on actual snapshot values | `codec_roundtrip`, `frozen_transport`, `map_field_guard` |

`constant_readout_rejected` is parameterized over **each of the nine** register
readout fields. It requires an actual mismatch with the independent recipe at
an actual closure state. A lawful constant owner is not required to vary.
`readout_mismatch_rejected` also handles nonconstant capped proposals. These are
component guards; no failure of a sufficient check is claimed as failure of the
as-yet-unconstructed named StrictTemporalLineage readout.

## Statement changes

| Classification | Row | Change/reason |
|---|---|---|
| (b) | TTH-06 | Acquisition Bindings.histories changes from one-cell CellView to StaticView; dependencies change from one cell to all instruction reads. Needed to compute history words from history, route and assigned policy/receiver inputs. One-cell behavior embeds exactly. No existing row text is narrowed. |
| (b) | TTH-06 | New executed-frontier, shared-runtime, actual-support reindexing, finite codec transport, source instance and guard theorems. No existing theorem is weakened. |

There are no (a) declaration renames. No finite-context premise is introduced;
closure laws remain semantic obligations over unbounded registers. This is not
an unrestricted-grammar decision-completeness claim.

## Remaining completion gates

1. Construct the G4 atomic legs/chain from the checked runtime acquisition.
   Link the actual atomic witness and all adjacent interfaces to those cells.
2. Complete the G1c factor, successor, record, route, owner and typed endpoint
   construction. In particular, bind primitive clause schemas to runtime
   readouts/rows, rather than relying on the standalone codec theorem.
3. Construct the target/receiver frame and prove **full arbitrary-partial**
   equivalence of L and the named StrictTemporalLineage readout with G6c,
   including its direct missing-atomic-witness negative. The negative currently
   proved here concerns the executed-frame component only.
4. TTH-05 transport from the generic game readout, followed by RawHandoff F/O
   soundness, named separation/dependence, controls, transcription and promotion.

No completed named lineage or generic TTH-06 result is claimed at this boundary.

## Verification and file list

- `cd lean && lake build`: exit 0, 441 jobs; final incremental build 14.75 s.
  The source-frontier module built in 7.7 s in that run. No new-module warnings;
  pre-existing warnings replay.
- `scripts/validate_lean.sh`: exit 0; 39 rows / 210 declarations resolve, no
  untrusted axioms, placeholders, or high-confidence vacuity. Thirty existing
  ignored-input heuristic leads remain non-gating.
- All 59 new public theorem names were checked and printed for axioms through
  `/tmp/g6d-execution-axioms.lean`: standard three or fewer.
- Forbidden-construct grep on new modules and `git diff --check` are clean.
  CST-TT files, the inventory, committed models and `paper/` are untouched.

Added under `lean/CSTTT/Targets/GenericHandoff/`:
`StaticView.lean`, `ExecutionFrontier.lean`, `RuntimeExecutionFrontier.lean`,
`ExecutionSnapshotTransport.lean`, `FutureLumpingTransport.lean`,
`POS04RegisterLumping.lean`, `ReadoutFrontierRestriction.lean`, and
`POS04ExecutionFrontier.lean`. Changed `AcquisitionExecution.lean` for the static
history instruction and dependency scope, and `lean/CSTTT.lean` for imports.
This note is the only audit addition. Changes are uncommitted.
