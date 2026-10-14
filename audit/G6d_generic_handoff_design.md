# G6d-0 — generic raw Temporal-FIACH design

**Design only; no statements, Lean sources, registry or frozen models change.**
Baseline: G6c-2, `f17a4d8`. TTH-06 remains `conditional`. This note implements
G0's `RawHandoff` contract, not a renamed POS-04 wrapper. The fixed POS-04
construction is a specialization and a source of proofs/controls. The owner's
F/O decision in G6a governs the autonomy meanings and separation claim.

Authorities: `audit/G0_generic_contracts.md:72–97`;
`audit/G6_lane_spec.md:147–313`; the current
`lean/CSTTT/Targets/ComputedFIACH/Assembly.lean:38–56,177–215`.
G0's earlier suggested split and candidate controls are superseded by the owner:
**no row split or voluntary narrowing**; use the registered G6 controls and
prove the stronger generic contract.

## 1. Generic raw interface

### 1.1 Finite factors, typed primitives, and unbounded runs

The public interface must have no mention of POS-04 `Tag`, `KState`, `Cell`,
`Action`, `EventId`, `HistoryId`, `RouteId`, canonical stage, star cover, four
snapshots, unit ledger, or singleton disturbance. The eight clause names and
six withdrawal roles are theory vocabulary, not a fixed model carrier.
`CarrierId` remains the existing identifier type. Factor types may differ
between source and target; corridor intermediates may have other carrier IDs.

Lean **structure sketches**, not claims that these declarations already exist:

```lean
structure FinitePresentation where
  Ty : Type
  eq : DecidableEq Ty
  enumeration : FiniteEnum Ty

structure RawInterface where
  SourceFactor TargetFactor : FinitePresentation
  SourceAction TargetAction Disturbance Outcome : FinitePresentation
  Cell Coord Event History Route Resource Protocol Assemblage : FinitePresentation
  PredictiveSource PredictiveTarget ResidueKey MaintenanceKey : FinitePresentation
  sourceId targetId : CarrierId
  cellSort : Cell.Ty → PrimitiveSort
  coordinateCell : Coord.Ty → Cell.Ty
  coordinateProjection : (k : Coord.Ty) → RawProjection (cellSort (coordinateCell k))

abbrev Assignment (I : RawInterface) :=
  (k : I.Cell.Ty) → Option (PrimitiveValue I (I.cellSort k))

structure RawStage (I : RawInterface) where
  arrows : Clause → I.Cell.Ty → Option (TypedCellArrow I)
  referenceTranslation : Clause → I.Cell.Ty → Option (TypedCellArrow I)

structure RawCover (I : RawInterface) where
  scopes : Clause → List I.Cell.Ty
  adjacency : Clause → Clause → Bool
  requiredCells : List I.Cell.Ty

structure RawHandoff where
  interface : RawInterface
  assignment : Assignment interface
  clauseInputs : RawClauseBindings interface
  clauseGrades : ClauseGrades
  stage : RawStage interface
  cover : RawCover interface
  acquisition : RawAcquisitionBindings interface
  dynamics : RawDynamicsBindings interface
  withdrawal : RawWithdrawal interface
  audit : RawAuditSelectors interface
```

### Forward interface for TTH-07 composition

```lean
structure RawHandoffMap (a b : RawHandoff) where
  interfaceMaps : TypedInterfaceMaps a.interface b.interface
  namespaceReindex : TypedNamespaceReindex a.interface b.interface
  instructionSequence : RawInstructionSequencing a.interface b.interface
```

These fields are raw typed maps and instruction syntax, not a composed success
verdict. A checked map transports intermediate carrier/package cell references,
types and values exactly; reindexing preserves shared cell identity. Instruction
sequencing is closed under interpretation: sequencing executes the first then
second instruction, including absence propagation. G0 TTH-07's preservation
targets additionally require delivered histories in the second reachable bridge
domain, intermediate package agreement, bridge/route readout composition,
receiver injectivity on delivered classes, and composite source-absence activation.
These are raw-equation laws to prove, not supplied HandoffPass fields. Generic
staged maps do not require globally bijective namespace reindexing. This sketch
adds no TTH-07 theorem in G6d-1.

`PrimitiveSort` describes **raw** tables/values: probability rows, public
channels, profiles, closure maps, generator edges, joint distributions,
receiver instructions, histories, events, route registers, ledger/resource
rules and structural audit parameters. It is not a `verdict` sort. Bindings
are references to these same cells, not second copies of their values.
`PrimitiveValue` is dependent on the sort; a mis-typed reference is rejected.
Finite tables are represented extensionally by finite indexed arrays/lists,
with explicit reference/order checks. A `FiniteEnum` completeness proof is
structural presentation evidence, not a proof of a lane. Remove duplicate enum
entries for sums and subset enumeration; retain a separate declared ordering
where class numbering depends on order.

A logical slot is a coordinate/projection view onto a primitive cell. Two shared
references must resolve to **the identical cell**, not equal-looking independent
stores. Cell sorts do not imply a finite value space: exact `Rat`, `Nat`, finite
lists and tables are permitted. Required equalities of finite functions are
pointwise checks, not invented `DecidableEq` instances on function spaces.

A run is **defined**, not stored:

```lean
RunState m := SideFactor m × Nat × Nat × Nat × RouteRegister m × RunLedger m
```

The exact representation can use named fields rather than the product. Finite
factors are separate from unbounded order/tick/progress/record values and route
tapes. There is no strict-growth rank on a recurrent finite factor. Raw receiver
instructions select/read wheel coordinates or general typed source coordinates;
raw action/ledger/writer recipes define the updater. No supplied run,
future, observer, code, entry set or signature is accepted. **(b), hybrid
resolution:** an auxiliary invariant witness is allowed only with obligations
proved against these defined raw semantics. It is not a stored autonomy verdict.

### 1.2 Explicit clause rules, locality and absent inputs

Do **not** introduce `accepted : Clause → Prop`, `eval : Assignment → Bool`,
`packageValid`, or an arbitrary function returning the desired verdict into
`RawHandoff`. Clause bindings select inputs to fixed, substantive rule schemas.
Rules are interpreted from those assigned inputs; they are not replaced by
an unconstrained callback. Clause grades identify which approved primitive or
surrogate schema is being checked. A grade is a declared ceiling, never a pass.

| Clause | General raw rule to extract/implement | POS-04 specialization |
|---|---|---|
| C1 | Finite closure/kernel, quotient reconstruction and staging; normalized fixed-point equations, uniqueness, nonuniformity, exact defect/retention checks under declared perturbation | T1 audit and C1 reconstruction |
| C2 | Lower and promoted readouts from raw tables; computed nonfactorizing split pair | public f / raw M |
| C3 | Iterated finite public-profile refinement to a fixed partition; terminal predictive/continuation coordinate equations | 6→7→7 and M-link |
| C4 | At the selected grade, channel collisions and supported connectors; full HIDD requires its additional premises, not a grade label | collision/connector surrogate; full-HIDD failure retained |
| C5 | Generator products, ownership/provenance and self/other/none partition | protocol-credit surrogate |
| C6 | Realized strict traces, finite predictive quotient/code, defined full observer/updater, one-step bisimulation, positive funded record advancement, coarser-code witness | assigned C6, including its current surrogate ceiling |
| C7 | Same assemblage domain, exact coupling distributions, K_bw/R_rec strictness, operational receiver use and staged transport | recombination surrogate |
| C8 | Raw priced owner/resource rows and computed greatest viable subset | funded T1 target kernel |

Raw numerical parameters and structural equations may vary; **77/80**, four-unit
probability encoding, unit cost/recharge and exactly ten states are not generic
assumptions. Those are specialized data and theorem consequences in POS-04.
The generic theorem remains at the supplied, explicitly checked clause grades;
it does not upgrade C4–C7 to full P05 by abstraction.

C1's uniqueness cannot become a finite `decide` over rational distributions or
a supplied “unique” flag. Extract the finite normalized-system verification:
a raw row-operation trace on the matrix **constructed from assigned rows** is
checked step by step; applying it to the normalization RHS **defines** the
candidate distribution. Verified reduction/rank derives uniqueness, rather
than accepting a candidate stationary vector. Alternatively derive a checked
contraction certificate from those rows. POS-04 uses `T1Audit.pi_unique` by
transport; that theorem is not already a uniqueness theorem for arbitrary
matrices. This generic verifier is a significant extraction/proof obligation.
Reference P/C/U tables are raw audit inputs; their reconstruction is recomputed
from action supports, hazards, class ordering and quotient tables.

`decodeClause m side c` returns `Option (ClauseInputs m side c)`. Its dependency
list is defined from the schema and typed references, including transitive
reference dependencies; it is not a caller-supplied readiness verdict. Every
consumed cell must be present. Missing/out-of-scope reads remain absent.
Acceptance and hard gates reject `none` before any total helper defaults apply.
Prove decoder locality, then acceptance/gate locality, over these dependencies.

Do not require all package cells to be present in the **model type** or in O's
readiness gate: the registered package-deletion model must remain a well-typed
raw model with P false and O true. Each lane checks its own dependencies. F's
packageInside adds package dependencies intentionally; O does not.

### 1.3 Stage and independently valid cover

`TypedCellArrow` carries a source-cell reference and a typed translation
**instruction**, interpreted on actual assigned values. The stage's working
arrow and separately declared reference translation are compared by raw
pointwise equations. Type/totality, value preservation and inverse/reference
laws required by a particular stage are checked; `swapCell` is only the POS-04
instance. There is no global requirement that source and target have identical
cell sets or an involutive map. Source-scope coverage is an explicit raw check.

Mapped locals are defined by decoding each arrow and applying it to the source
cell. Target local checks evaluate each clause on that defined local view.
Gluing requires independently computed cover coverage and coordinate-wise
connectivity under declared adjacency, plus edge compatibility. Reuse TTH-01's
`ScopedReach` propagation (`Package/FiniteGluing.lean:8–66`); define a finite BFS
certificate for each covered cell and choose the first covering clause in the
fixed eight-clause enumeration. A rooted join tree is one accepted cover
presentation, **not the only allowed raw topology**. Cyclic covers are not
silently forbidden: a cover with a valid coordinate-connectivity certificate
can glue; an obstructed cover fails the required gluing checks.

The global is defined from mapped locals and the checked covering selector.
The restriction proof then transports local clause acceptance/gates to global
acceptance using locality. No global assignment or target-package witness is
an argument. Stage/cover metadata and adjacency vary with `m`.

### 1.4 Acquisition, histories, routes and bridge

`RawAcquisitionBindings` references realized stages/events, owned support,
actual dependencies, intervention projections, receiver activation/content
instructions, latent target data and receiver protocol. History/route types
are arbitrary finite **IDs** for raw lists; the source→target history map
executes the receiver on actual source history and fixed latent receiver data.
It does not take a target class or target history conclusion as an argument.

`RawAuditSelectors` is a finite list of declared history/route/event/occurrence
selectors, not a list of supplied run snapshots. Decode and execute each raw
prefix to obtain source and target snapshots, including counter/ledger updates.
The checked frontier is nonempty with an actual strict supported edge and
coverage of the declared history domain. POS-04 chooses its existing four
selectors; the generic type does not fix their number or occurrences.

Construct G4 legs from stages/events/support/intervention tables. Construct
G1c `RawBridge` from the **same** decoded histories, transitions and update
recipes. Its existing function-valued readouts are an internal projection,
not independent raw arguments to `RawHandoff`. Every run readout is defined
from execution; coherence checks bind all G1c weights, successors, readouts
and roots to the common input cells. Compute M/predictive classes from raw
transition observables, never from stored class labels alone.

Routes execute supported raw paths. The comparison domain is declared before
checking, nonempty, and uses raw tuples/path identity rather than route names.
Route status is derived from execution, shared endpoint, retained provenance
and declared future readouts, or a separately substantive route license.
No empty comparison certifies flatness. No hardcoded 0/1 readouts: require
computed definedness/inequality for the memory branch. The first-phase rule is
POS-04 data, not the generic rule. The typed endpoint check compares the actual
corridor exit, receiver result and mapped history, class, ownership, and the
phase convention specified by the raw ledger/clock data.

### 1.5 Controlled system, disturbances, withdrawal and entries

```lean
structure RawWithdrawal (I : RawInterface) where
  removedRoles : List WithdrawalRole
  removedResources retainedResources : List I.Resource.Ty
  sourcePresentAfterWithdrawal : Bool
  retentionEdits : List (TypedResourceEdit I)

-- Schematic decoded raw data, obtained from assignment cells, never supplied
-- beside an independently supplied assignment:
structure DecodedControlledData (I : RawInterface) where
  rows : I.TargetFactor.Ty → I.Disturbance.Ty → I.TargetAction.Ty →
    List (Option I.TargetFactor.Ty × Rat)
  owner : I.TargetAction.Ty → CarrierId
  requiredResources : I.TargetFactor.Ty → List I.Resource.Ty
  resourceOwner : I.Resource.Ty → CarrierId
  ledgerRecipes : FiniteLedgerRecipes I
```

`none` destinations represent declared exits/failures. Reject negative weights,
zero-total rows and bad normalization; retain all positive support, including
exits. Exact rational probabilities are not restricted to quarters.
Disturbance IDs and their effects on rows/resource recipes are explicitly
separate from control actions, and universally quantified over the declared
nonempty disturbance domain. POS-04 instantiates a singleton nominal domain.
The theorem does not claim robustness to undeclared shocks.

Compute the withdrawn assignment by applying only declared retention/resource
edits. Verify six-role removal, disjoint removed/retained resources, actual
post-withdrawal source absence and target resource/action ownership. Historical
acquisition evidence remains historical; it is not reacquired after withdrawal.
Required resources and effective budget/recharge are state/context dependent,
not a generic singleton target-recharge resource.

Entries are defined from **activated, realized** receiver exits followed by the
raw acquisition-phase funded target response. Execute all positive support with
its actual register, ledger and counters. Empty/inactive/absent execution yields
no entries and rejects both autonomy versions. Never reset the entry to the
prior receiver or silently drop an exit. The entry projection includes every
finite context that affects control responses/resources; an entry with an
unrepresentable/invalid context fails, rather than receiving a default.

For a finite controlled factor X and S⊆X, define from decoded tables:

- `safeResponse m S x d a`: available target-owned action, normalized nonempty
  row; every positive destination is an in-factor member of S; resource closure,
  funded ledger and run advancement laws hold. No lucky-branch witness.
- `baseO m x`: C8 local readiness/ledger/resource viability checks only.
- `packageAt m x`: recomputed **arrival coherent P**, withdrawn graded clause
  checks at x, resolved state views and run-law checks, exactly the same-package
  meaning of G6 §4F. Including P is disclosed; no stored P verdict.
- `c8Response m S x a`: C8's own funded, owned, resource-closed response
  whose entire positive support stays in S; this does not incorporate acquisition
  activation or the six-role withdrawal check.
- `retainO m S x`: `baseO m x` and a C8 response into S, with precisely the
  disturbance quantification of the decoded C8 rule. Additional autonomy
  disturbance/withdrawal/advancement obligations belong to AO's later gate.
- `retainF m S x`: `packageAt m x` and **for every declared disturbance,
  some safe target action**. Package validity at every supported F successor
  follows from S's own viable membership, not a favored successor.

Use a canonical finite-set representation. Define `greatestO/F` as the union of
all viable subsets of X, ordered by the declared finite presentation. Prove
monotonicity, fixed-point equality and containment generically, then optionally
prove equivalence to a faster pruning iteration. There is no invariant argument.

Do **not** change POS-04 O's definition inadvertently: its C8 greatest set and
its extra withdrawal/acquisition/nominal-response checks are separate in G6c.
The generic operational operator specializes to C8's operator; extra conditions
are checked by AO afterward. They may be folded into an alternative invariant
only after proving the resulting AO predicate equivalent for all assignments,
not merely on baseline. F's existing operator includes the withdrawal/advance
response checks; preserve that distinction in its adapter.

`AF`/`AO` require their own decoded readiness, nonempty entry set, every entry
inside the appropriate computed invariant, nonempty invariant, withdrawal,
resource/ledger laws and every-state/every-disturbance safe responses. F adds
packageInside. Nonempty AF gives a real package-valid entry and hence P.
The derived `ControlledSystem`/`ExactAutonomyData` uses positive row support,
computed packageAt/inside/owner/resource and run-update predicates; every old
`Prop` field is **filled by a definition**, never by an unconstrained parameter.
Construct `ExactAutonomyCertificate` for each entry from these checks.

### 1.6 Semantic law gate versus executable finite verification

A generic statement about arbitrary unbounded runs cannot honestly receive
`Decidable` merely because the factor is finite. Use semantic `*Pass : Prop`
definitions consisting of raw equations, finite membership/inequalities,
supported execution laws and closure-wide update/bisimulation laws. They are
computed predicates, not stored propositions. `RawHandoff` has no field with a
lane verdict or supplied derived future function.

Finite verification certificates can check raw equation tables and symbolic
update recipes, then prove these semantic laws by induction. This is the G1c
pattern. An executable verifier is a **sound certifier**, not an assumed decision
procedure for arbitrary Lean functions. Do not restrict the primary theorem to
one syntactic updater class to make `decide` available. If only a restricted
verifier is implemented initially, label that intermediate boundary and retain
the broader semantic theorem as the promotion target. POS-04 specialization
must recover the actual G6c gates, not merely a sound sufficient subset.

## 2. Reuse and extraction map

These are the actual current theorem names and boundaries, not imagined
polymorphic versions of POS-04 code.

| Lane/task | Already-proved reuse | Required extraction / new bridge |
|---|---|---|
| P, restrictions/gluing | `PackageTheory.gluedAssignmentAgrees`, `localEqualityAlongScopedReach` (`Package/FiniteGluing.lean:49–89`) | Dependent assignment/decoder, heterogeneous typed arrows, arbitrary scopes/adjacency and constructive finite selector; locality of each raw rule |
| P, mapped clause acceptance | `POS04.Assigned.stagedHeterogeneousPackageAssembly_generic` (`Assigned/PackageAssembly.lean:184–201`) | Its proof pattern is generic; its **type is fixed POS-04**. Extract to arbitrary cell/value interfaces, explicit clauses, stage and cover. Prove specialization, do not claim current theorem already covers them |
| L, atomic chains | `CorridorTheory.AtomicChain.strictTemporalCorridorComposition_generic`, `append_corridor` (`Corridor/AtomicChain.lean:376–399`) | Construct legs from shared decoded raw cells; encode finite carrier/event IDs injectively into existing Nat/String fields with proved preservation, rather than renaming POS-04 event IDs |
| L, signatures and futures | `TransportTheory.bundledHeterogeneousTemporalTransport_frozen` (`Transport/FrozenSnapshotBridge.lean:358–379`); `bridge_defined_future_sufficient`; `FrozenBridgeSnapshotResult` | Generalize `ComputedFIACH.assignmentRawBridge`, history execution and snapshot selectors; bind every projection to common raw rows/update rules, all closure states, exact snapshot images |
| AF, entry-to-word transport | `AutonomyTheory.postWithdrawalFiniteHorizonInvariance`, `finiteHorizonRunExists` (`Autonomy/FiniteAutonomy.lean:67–96`) | Decode arbitrary target controls/resources/roles, define ExactAutonomyData and construct its certificate for **each** actual phase-2 support entry |
| AF, greatest invariant | `ComputedFIACH.pruneF_mono`, `greatestF_fixed`, `greatestF_viable`, `greatestF_contains_viable`, `greatestF_all_support_responses` (`ComputedFIACH/Autonomy.lean:83–125`) | Already arbitrary-assignment theorems, **not arbitrary-factor theorems**. Extract finite subset union and universal-disturbance response proofs from KState/actions/nominal/unit ledger |
| AO, greatest invariant | `POS04.Assigned.prune8_mono`, `greatest8_fixed`, `greatest8_viable`, `greatest8_contains_viable` (`Assigned/C8.lean:65–103`) | Same finite-set proof extraction; retain operator/additional-AO-check distinction |
| Acquisition into A | `ComputedFIACH.phase2Entries`, `entries` (`ComputedFIACH/Entries.lean:23–86`), execution/missing guards | Extract source rows, receiver activation, realized path, exit/funded step, exact positive support and counter/ledger/register update to varying types; include intermediate audit prefixes |
| F/O assembly | `ComputedFIACH.temporalFIACH_sound_F/O`, named-readout vectors and `operational_readouts_logically_independent` (`ComputedFIACH/Assembly.lean:79–99,177–215`) | Transfer via full predicate/readout equivalences; family soundness alone cannot discharge G0 |

The central extraction is three layers: **typed assignment and raw clauses**,
**activated acquisition/entries/bridge**, **finite controlled viability and
package-preserving autonomy**. C1 uniqueness and full-future/run-law checking
are separate sizable obligations inside these layers. TTH-02's current
promotion does not remove its fixed-type restriction for reuse here.

## 3. Theorem targets and proof architecture

Names below are proposed in a new generic namespace; old declarations remain.
`P`, `L`, `AF`, `AO` are calculated from the raw model. Named readouts express
the constructed package, actual corridor/bridge, and controlled invariant.
Do not define the negative readouts merely as negations of a sufficient check.

```lean
theorem temporalFIACHCertificateSoundness_generic
    (m : RawHandoff) (h : HandoffPassF m) :
    IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
    PostWithdrawalAutonomyF m

theorem temporalFIACHCertificateSoundness_generic_O
    (m : RawHandoff) (h : HandoffPassO m) :
    IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
    PostWithdrawalAutonomyO m

theorem fullAutonomy_implies_package (m : RawHandoff) : AF m → P m

theorem fullAutonomy_readout_implies_realization (m : RawHandoff) :
    PostWithdrawalAutonomyF m → IntegratedTargetRealization m

theorem fullAutonomy_package_failure_consequence (m : RawHandoff) :
    ¬ P m → ¬ AF m
```

`HandoffPassF/O` includes distinct carrier IDs, source package, stage equations,
independently valid gluing/target-local checks, the separate lane checks,
content-sensitive receiver and source-absence control laws, typed endpoint and
route-status agreement. These are equations/checks over m's data. SourceAbsent
is computed by re-running the **same** receiver with source unavailable, not
by a supplied counterfactual success flag. Content sensitivity holds fixed
latent target and receiver protocol, varies genuine source classes and derives
both endpoint classes from the actual operation.

P is derived by package assembly/locality; L by corridor composition and the
constructed G1c bridge; AF by generic greatest-ness and the TTH-05 construction.
O reuses operational viability. Each proof consumes only its lane's own
subchecks; P is not supplied from AF. `AF → P` follows from a nonempty computed
entry/invariant, packageInside and the coherent-package part of packageAt.
This implication is **not** claimed for arbitrary viability or a repaired,
unrelated later package. It is the G6 same-package F definition, not a new
hypothesis smuggled into the theorem. The readout implication follows by the
same package construction. F cannot have a package-only isolation witness.

G0's separation theorem is **O**, by the owner's F/O decision:

```lean
theorem temporalFIACH_three_lane_separation :
    (∃ m : RawHandoff,
      ¬ IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
      PostWithdrawalAutonomyO m) ∧
    (∃ m : RawHandoff,
      IntegratedTargetRealization m ∧ ¬ StrictTemporalLineage m ∧
      PostWithdrawalAutonomyO m) ∧
    (∃ m : RawHandoff,
      IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
      ¬ PostWithdrawalAutonomyO m)
```

Export F's registered readout vectors as well: package deletion `(F,T,F)`,
lineage deletion `(T,F,T)`, withdrawal deletion `(T,T,F)`. The generic
`fullAutonomy_package_failure_consequence` proves dependence for **all** m;
the registered package model witnesses that dependence nonvacuously. F's
“none inferred” is proof-structural, O's is logical independence. This note
neither changes the row text nor resurrects G0's earlier split suggestion.

## 4. POS-04 instantiation and equivalence obligations

Define `ofPOS04 : ComputedFIACH.RawLaneModel → RawHandoff`. It reads that model's
actual assignment/withdrawal fields. Its finite presentations and bindings use
L5's transcribed data; the stage/cover come from that specialization. It does
not replace changed rows, events or resources with a positive adapter.
The three registered controls remain the frozen raw transformations. No new
model declaration or evaluation is needed merely to transport them.

Mandatory targets, **for every family assignment including partial ones**:

```lean
P (ofPOS04 m) ↔ ComputedFIACH.PackageLane m.assignment
L (ofPOS04 m) ↔ ComputedFIACH.LineageLane m
AF (ofPOS04 m) ↔ ComputedFIACH.AF m
AO (ofPOS04 m) ↔ ComputedFIACH.AO m
```

Also prove equivalence of the named readouts with
`ComputedFIACH.IntegratedTargetRealization`, `StrictTemporalLineage`,
`PostWithdrawalFullAutonomy`, `PostWithdrawalOperationalAutonomy`, respectively.
These are **additional** obligations: acceptance equivalence alone does not
transport a negative conclusion. Reuse the direct negative proofs from G6c-2
and prove preservation of their failed cell/atomic witness/withdrawal argument.

Prove separately: decoded-input equalities under readiness; mapped-local and
global equations; all supported entry rows/probabilities/registers; membership
of both greatest sets; all four snapshot/root/execution equations; future/code/
observation equality with the appropriate outcome reindexing; resource/role and
ExactAutonomyData equivalence. Under absent dependencies, both gates reject
before decoding; do not assert an equality of default-filled dynamics for those
rejected inputs. Set equality is extensional membership; identical list order
is a stronger implementation/transcription result, not an invented assumption.

`HandoffPassF/O (ofPOS04 baseline)` must hold and yield both generic soundness
readouts. The existing F/O readout vectors then give the generic controls.
The reversed-histories family instance must still pass with computed outputs
1/0. Positive and control equivalences, not an unchecked embedding of the model
name, provide the non-vacuity/promotion gate.

## 5. Argument classification and readout coverage

### 5.1 Arguments and ownership

| Argument/object | Classification | Constraint |
|---|---|---|
| finite type/presentation, IDs and primitive sorts | raw structural data | Decidable equality, complete enumeration, reference/order coherence; nonemptiness where used |
| assignment, primitive tables and bindings | raw data | One immutable namespace; typed cell references; dependency-local decoding |
| stage/translation and cover/adjacency | raw data | Scope totality, value equations, independent coordinate connectivity/compatibility |
| receiver protocol/latent state, histories, events, audit selectors, routes | raw data | Supported realized execution; checked frontier coverage/strict edge; no stored class or entry |
| action/disturbance/resource/ledger/withdrawal tables | raw data | Exact rows, ownership, availability, full declared disturbance domain and withdrawal roles |
| raw algebra/update verification traces | evidence data on raw equations | Interpreted and verified against constructed inputs; never trusted verdict/derived inverse/distribution |
| `h : HandoffPassF/O m`, bridge/locality/raw-law hypotheses | evidence on raw data | Defined checks/equations, no free acceptance or conclusion predicate |
| subset S in greatest-set theorems | comparison data plus viability evidence | Not the supplied invariant; containment depends on real viability |
| mapped locals, global, clause acceptance/gates | defined objects | Source assignment, raw maps, cover and fixed rule interpretation |
| legs, bridge, snapshots, endpoints, entries, route status | defined objects | Shared decoded acquisition/execution data |
| run updater, weights, code, observer and closure | defined objects | Raw rows and update recipes; every readout law checked throughout closure |
| greatest sets, ControlledSystem/ExactAutonomyData/certificates | defined/constructed objects | Generic finite-set derivations and actual entry/response/withdrawal data |
| recognition | defined `.notAddressed` | Outside structural criterion; never supplied as an affirmative label |
| POS-04 embedding/equivalence evidence | defined instance and proof | No additional hypothesis restricting the generic theorem to POS-04 |

### 5.2 Readouts, checks and mandatory guards

Each extraction packet must export a named law and guard for every row below.
These are obligations, not claims that generic versions already exist.

| Field/readout | Derived rule / closure-wide law | Required guard |
|---|---|---|
| factor / source and target projections | Actual positive-support successor and typed factor projection | Alter one supported destination; wrong projection or dropped row rejects |
| predictive now / M | Raw action observables and ordered quotient; successor class agrees with mapped raw step | Corrupt raw support/hazard/class reconstruction; no stored-label acceptance |
| order counter | Actual executed event/run counter; supported strict increment | Cap after audit endpoint, or un-realize a certified event |
| tick and phase | Assigned clock increment; phase from declared positive modulus | Zero/change delta or modulus; closure law fails |
| progress | Raw increment recipe, positive on advancing supported steps | Constant/capped progress fails beyond roots |
| writer | Resource/owner and raw route writer rule, available on certified steps | Remove writer cell/availability; reject before defaults |
| endogenous record | Funded writer's record update from actual successor | Zero/cap record or zero funding; record-advance law fails |
| route residue/register | Actual raw path/history provenance updated/retained by execution | Delete a register write or collapse distinct paths; inspect resulting state |
| route readout/status | Execute funded step, declared rule/owner, shared endpoint and nonempty comparison | Change rule/owner, remove comparison, equalize outputs; reverse 0/1 remains valid |
| maintenance, budget and enabled | Effective retained resources, actual cost/recharge/next-ledger equation | Underfund/zero ledger or withdraw recharge; no survival via historical source |
| owner | Typed owner translation and preservation by target-owned updates | Relabel only owner without transporting resources/action ownership |
| package state views | Shared primitive cells and scoped per-state checks on constructed global | Delete an actual required cell; failed clause cannot be averaged away |
| cover/map/adjacency | Total mapped values and independent gluing law on the declared topology | Drop map cell, alter translation, break overlap or connectivity |
| withdrawal/entry interface | Activated realized exit followed by full supported phase-2 row; all six roles removed | Source unavailable at acquisition yields no entries; present after withdrawal or one unremoved role rejects A |
| disturbance/response coverage | Every disturbance from every invariant state, all positive support safe | Delete only one state's response for a declared disturbance; universal check fails |

Counters and tapes remain unbounded. Frozen `TemporalSignature` alphabets are
exact finite images of the **computed finite audited snapshots**, with codec
and typed-transport equations, not truncations. Their full future sufficiency
is about the defined bridge dynamics on its computed closure. A candidate cap,
uniform-weight substitute, identity updater or changed raw readout must fail
its coherence gate even when all roots look unchanged.

## 6. Dependency-ordered implementation packets

Sizes concern one reviewed boundary, not a promise that the entire generalization
fits one turn. No promotion until the final bridge/instance gate.

| Packet | Size | Proved, reviewable done boundary |
|---|---|---|
| G6d-1: polymorphic cells, decoder, maps and cover | M | Typed partial assignments; generic decoder locality/missing guards; constructive dependent gluing and stage laws; POS-04 substrate/stage/cover specialization |
| G6d-1b: monotone finite viable-set engine | M | Arbitrary finite carrier and monotone retention operator; viable union fixed point and greatest containment; no run/factor lift assumed |
| G6d-2a: generic C1–C3 raw-rule layer | L | Explicit rules/required inputs and locality; uniqueness verifier or checked generic fixed-point argument; POS-04 equivalences through T1Audit; clause controls transfer |
| G6d-2b: generic C4/C5/C7 schemas | M/L | Raw graded rules, operational C7 use/transport and locality; exact canonical/family equivalences; missing/constant controls |
| G6d-2c: generic temporal/C8 rules | L | Defined run dynamics/code/observer and full-word induction; closure-law guards; generic operational finite-factor viability and POS-04 equivalences |
| G6d-3: generic package construction | M | Arbitrary typed stage/checked cover yields accepted constructed global by locality/TTH-01; P and named package-readout equivalence, including direct deletion failure |
| G6d-4a: acquisition and entry execution | M | Receiver, supported realized paths, exact full-support phase-2 entries, dependency rejection and typed endpoint equations; family equalities |
| G6d-4b: corridor and G1c adapters | L | G4 legs/chain and bridge constructed from the same cells; all audit snapshots/run-law/future links; L and named lineage equivalence, including missing atomic witness |
| G6d-5a: generic F/O invariant algorithms | M | Instantiate the earlier G6d-1b engine with F/O retention operators; prove monotonicity and exact specialization of both current operators |
| G6d-5b: autonomy/TTH-05 transport | M/L | Every entry yields full ExactAutonomyCertificate, all-support safety and nominal/general declared words; AF→P and F dependence; AF/AO/readout equivalences and withdrawal controls |
| G6d-6: generic soundness, separation, registry gate | M | G0 F/O signatures, separate derivations, named-readout O separation/F controls; baseline and all family equivalences; exact transcription/adversarial guards; build/validator clean before promotion |

G6d-1b precedes G6d-2c, the first engine use. G6d-2c and G6d-5a
instantiate that engine; do not duplicate it.
If C1's general verifier exceeds G6d-2a, split its algebraic verifier from its
rule/adapter packet at a fully proved boundary; do not hide uniqueness under
an assumed flag. Likewise split run-law construction from future sufficiency
if needed. New model choices/controls, if any become necessary, receive their
own declaration→evaluation→Lean sequence; do not evaluate invented generic
examples during implementation and call them pre-registered.

## 7. Risks, decision points and anti-vacuity

1. **A fixed family in disguise.** Moving POS-04 names into a record is insufficient.
   Check the public `RawHandoff`/theorem types for all the fixed types/constants
   listed in §1.1, including implicit decoder canonical defaults and four audit
   selectors. Instance data may contain them; generic definitions may not.
2. **Extra conditions as narrowing.** Same-size carriers, bijective stages,
   involutions, a star-only cover, a singleton disturbance, unit prices,
   canonical-P-only dynamics, or a fixed audit frontier cannot become generic
   premises to simplify proofs. A necessary compatibility/closure law must be
   stated as raw equations and traced to G0/G6, with its role recorded. A newly
   needed hypothesis beyond those contracts is an owner decision: stop and
   report it rather than silently promoting at a narrower ceiling.
3. **AF→P meaning.** The theorem is true for the disclosed same-coherent-package
   F semantics. With an unrelated post-withdrawal repaired package, AF need
   not imply arrival P. Preserve G6's packageAt definition and derive P at a
   genuine entry; do not claim a theorem about arbitrary later viability.
4. **Unbounded context versus finite fixed points.** Every resource/response-
   relevant run context must be covered by a **proved finite-factor lift**.
   Naming a projection does not prove this lift. Prove that its
   projection and run-law invariant cover the full closure. If availability
   genuinely depends on uncaptured unbounded counters/tapes, the factor-only
   greatest set is not sound. Do not omit that dependency or assume uniform
   responses by fiat. If this lift requires a new finite-context premise beyond G0/G6, **stop
   and report it before proceeding**: it is an owner decision. An infinite-state
   invariant would be a larger follow-up. This records Eddy’s §7.4 requirement.
5. **`decide` limits.** Finite type enumeration does not decide rational
   uniqueness, universal finite words, unbounded arithmetic or equality of
   arbitrary functions. Use verified finite linear certificates, extensional
   finite checks, generic subset proofs and bisimulation/induction. Keep a
   semantic law theorem separate from a conservative executable certifier.
6. **Readiness and evidence coherence.** P deletion must not suppress L/AO
   through a global all-cells gate. An independent supplied observer, bridge,
   entry set, invariant or source/target class can re-open the G1c loopholes.
   All projections must read the same cells; invalid/missing inputs reject
   before defaults. General equivalence is a proof obligation for every family
   assignment, not four hand-picked successful cases.
7. **Vacuous universals and degenerate witnesses.** Require nonempty supported
   histories/strict edge, realized carrier-changing leg chain, route comparison,
   disturbance domain, actual entry support and invariant. Require all eight
   clause instances/dependencies and the declared nontrivial quotient/coupling
   witnesses at their grades. Empty types, zero weights, duplicate IDs and
   constant rule programs cannot manufacture a lane. Independence is existential
   over RawHandoff, **not** asserted for every finite interface (a one-state
   interface need not contain the separating controls).
8. **Readout attribution.** Failure of a sufficient certifier is not failure of
   the readout. Transfer negative cases through named-readout equivalence or a
   direct impossible witness, as G6c-2 does. F's `(F,T,F)` is dependence, not a
   confounded independence result. No logical three-way F separation is promised.
9. **Scientific ceiling.** Generalizing alphabets does not upgrade surrogate
   C4–C7, add resource-shock robustness to nominal POS-04, prove T17-I or establish
   physical continuation. Preserve those explicit grades/domain limitations;
   the unresolved blocker is generality of the raw interface.

## Completion/status decision

This packet changes **no statements**, (a) or (b), and applies no narrowing.
Future extraction/new theorem additions are mathematical work requiring their
own (b) reports. TTH-06 stays `conditional` until the generic contract above,
its POS-04 specialization/equivalences and **named-readout** F/O controls are
proved and reviewed. The result is feasible in core Lean at the semantic level;
C1 algebraic verification, full-context lifting and exact family equivalence
are the largest implementation risks, not already completed proofs.

## Initial G6d-0 design-turn checks (historical)

- `cd lean && lake build`: exit 0, all 350 jobs complete; existing replayed
  warnings remain. No Lean source changed.
- `git diff --check`: clean. At that boundary the sole new file was this note; registry, inventory,
  CST-TT-08, committed models and results are unchanged.
- No new model, property evaluation or Lean theorem is claimed by this design.

G6d-1/G6d-1b implementation and its current receipts are recorded separately
in `audit/G6d1_generic_substrate.md`; the historical design check above is not
a claim that this later implementation edits only the design note.


## Hybrid architectural addendum — G6d-2c resolution (b)

The manager adopts unrestricted raw run-context recipes (option 2). No finite
recipe grammar is imposed. Derived dynamics, observations, code, entries and
verdicts remain defined, never supplied as independent candidates. An auxiliary
run-space invariant and a response strategy may be supplied as mathematical
witnesses; all obligations must be proved against the defined raw semantics.
This is a (b) architectural change for TTH-06, not a row-text narrowing or a
promotion.

Autonomy has independent game semantics: a causal target-owned strategy answers
every declared disturbance, and the environment chooses every positive-support
successor of its selected response. Safety quantifies over plays generated by
that strategy, not over actions it never selects. The invariant certificate
proves activated/realized nonempty entry coverage, same-package preservation,
resource closure, target ownership, nonempty normalized response support,
solvency and advancement against the actual updater. Induction derives the game
readout; no autonomy proof is a certificate field. F computes PackageAt from the
same assignment and run context, and AF→P is derived at a genuine entry.
Historical acquisition is not a post-withdrawal response dependency.

The square-counter illustration in the scope report fails full autonomy: at
counter 2 the resource-request disturbance has no legal response. An infinite
invariant cannot repair that system. It can certify other unrestricted recipes.

The ViableSet constructor is a sound, potentially incomplete certifier. A finite
specialization requires proved context projection, closure invariant and
response/resource/ledger lifting on every relevant reachable run. Decision
completeness is claimed only for an explicitly specified fragment with exact
lifting and decidable checks. No claim of decision completeness for unrestricted
recipes is made. C6 full-future sufficiency stays a separate obligation.

Implementation order: independent strategy/play semantics and invariant
soundness; raw component interpretation and F same-package implication; sound
finite specialization with proved lift; POS-04 partial-assignment/control
and C6/C8 equivalences. Each layer ends at a proved boundary. A general game
induction lemma may abstract its semantic relations, but those parameters are
not independent candidates at the RawHandoff boundary: that boundary must
instantiate them with defined raw interpretations and prove the adapter equations.
