# L3b countermodel, boundary, and open-row fidelity audit

Scope: TTN-01–14 and TTF-01–08 in `cst-tt/registries/FINAL_THEOREM_STATUS.csv`. The Lean quotations below give the operative proposition after unfolding, not just the declaration name. **STIPULATED** means that the finite Lean witness assigns a verdict through unrelated predicates rather than instantiating the theory predicate. A `Prospects.* : Prop` definition is a statement only. For certificates, I opened every listed JSON file and the countermodel's referenced `models/countermodels/CM-*.model.json`; `recheck` in `cst-tt/src/cst_tt/countermodels.py:915–916` was run on each referenced model. All 15 CM model files reproduce their stored premise and failure checks. Reproduction alone does not establish that a checker recomputes those checks from primitive finite data.

**Registry pointer drift:** all TTN/TTF `declaration_refs` match their declarations except TTN-01 (the Prospects and corridor pointers are swapped), TTN-09 (likewise), TTN-10 (the two `DefectVector` pointers are each two lines early), and TTN-12 (the Prospects and autonomy pointers are swapped). The exact corrected pointers are in `audit/l3_fidelity.csv`; none is edited in the frozen registry.

## TTN-01 — Detached reconstruction

**Verdict: STIPULATED.** **Row text:** “There exists an exact finite detached reconstruction with endpoint equality, target package realization, and target autonomy but no strict overlap temporal corridor.” Ceiling: exact finite boundary. **Lean:** `lean/CSTTT/Prospects/Statements.lean:89–92` defines `∃ m, endpointEqual m ∧ package m ∧ autonomous m ∧ ¬ corridor m`. `lean/CSTTT/Countermodels/Kernel.lean:37–52` sets the first three predicates to `fun _ => True` and corridor to `fun _ => False`; no `IntegratedPackageWitness`, `ExactAutonomyCertificate`, or corridor data is instantiated. `lean/CSTTT/Corridor/FiniteTemporalCorridor.lean:94–100` proves only that an actual `AtomicTemporalCorridorCertificate` is impossible **if** no mixed-support stage is supplied.

**Wiring:** `cm02_detachedExactTemporalCopy` proves the `Prospects` instance; the registry omits it and lists only the statement definition plus the conditional no-mixed theorem. **Certificates:** CM-01 records two carriers, equal endpoints/signatures, and absent operational dependency; `_check_cm01` (`countermodels.py:184–195`) reads the stored `strict_temporal_lineage`. CM-02 records a two-stage source/target copy, zero mixed stages, package pass and autonomy as booleans; `_check_cm02` (`:225–243`) reads stored `strict_overlap_corridor`, `target_package_pass`, and autonomy. The four COR-POS certificates are positive corridor comparators, not proofs about CM-02. **Repair:** encode CM-02 as typed stages, package and withdrawal systems, prove positive package/autonomy and `¬ HasMixedSupport`, then apply `noMixedStageExcludesAtomicCorridor`; if the certificate lacks enough data for the positive lanes, demote those clauses. Size **L**.

## TTN-02 — Public shadow

**Verdict: STIPULATED.** **Row text:** “There exist exact finite systems with identical public observations and different hidden consciousness-relevant structural predicates.” Ceiling: finite-interface nonidentifiability. **Lean:** `Prospects/Statements.lean:95–99` says `∃ a b, observe a = observe b ∧ hidden a ∧ ¬ hidden b`. `Countermodels/Kernel.lean:215–225` chooses constant `Unit` observation and assigns `hidden .genuine := True`, `hidden .counterfeit := False`; no package, predictive, or other frozen hidden structural predicate is used.

**Wiring:** `cm09_publicShadowCollision` proves the generic `Prospects` instance, omitted by the registry. **Certificate:** CM-09 has observation `[0,0]` and hidden bits `[0,1]`; `_check_cm09` (`countermodels.py:481–490`) reads the generated collision flag for both premise and failure, rather than recomputing from the arrays. **Repair:** instantiate a specified hidden package/predictive predicate in two finite systems with the same observation; otherwise revise to the elementary information-theoretic statement about arbitrary hidden labels. Size **L**.

## TTN-03 — Holonomy without arrow

**Verdict: STIPULATED.** **Row text:** “There exists an exact finite route system with nontrivial holonomy and no endogenous temporal arrow.” Ceiling: exact finite boundary. **Lean:** `Prospects/Statements.lean:102–104` is `∃ m, holonomy m ∧ ¬ arrow m`. `Countermodels/Kernel.lean:61–80` computes noncommutation of two three-state permutations, but `cm03EndogenousArrow (_ : Unit) := False` (`:74`) stipulates the absent arrow; it does not instantiate a strict record-arrow predicate.

**Wiring:** `cm03_holonomyWithoutArrow` proves the `Prospects` instance and is omitted by the registry. **Certificate:** CM-03 contains permutations `[0,2,1]` and `[1,0,2]`, with `record_update = "constant"`; the generator computes their noncommutation, but `_check_cm03` (`countermodels.py:273–285`) reads stored `nonzero_holonomy` and `endogenous_arrow` booleans. **Repair:** reuse the permutation witness and define the actual record update and strict arrow on it; calculate noncommutation and arrow failure in Lean. Size **M**.

## TTN-04 — Current collision and route memory

**Verdict: FAITHFUL at the route-discipline ceiling.** **Row text:** “When two histories are current-equal but predictively unequal, a current-only predictor cannot represent both; the licensed repairs are retained route memory or a proof of flatness.” **Lean:** `lean/CSTTT/Transport/RouteDiscipline.lean:16–32` derives `¬ ∃ predictor, predictor (current r₁) = future r₁ ∧ predictor (current r₂) = future r₂` from current equality and future inequality. `:35–48` defines `FlatAt` and `MemoryRepairs`; `:53–68` proves `FlatAt current future ∨ MemoryRepairs current future residue` **under** future sufficiency of the pair `(current, residue)`. The latter premise is the license, not an unconditional repair claim. `Countermodels/Kernel.lean:122–148` computes a two-route collision and separating memory; its separate `cm06MemoryRetained := False` and `cm06Flat := False` (`:138–140`) merely describe the *unaugmented* encoding.

**Wiring:** no `Prospects.*` declaration is registered for this row. `cm06_currentEqualPredictivelyDifferent`, `cm06_routeMemoryRepairsCurrentCollision`, and `cm06_unaugmentedMemoryOrFlatnessFails` are concrete Lean support but omitted from the registry. **Certificates:** CM-06 has current `[0,0]`, futures `[0,1]`, memory `[0,1]`; the generator computes the collision, while `_check_cm06` (`countermodels.py:376–390`) reads its stored mismatch/repair flags. TR-POS-01 and ROUTE-COMP-FLAT/INDEXED are distinct transport and route-completion examples, not this CM-06 instance. **Repair:** no row statement repair; add a typed Lean instance of `FutureSufficientEncoding` for `(current, routeMemory)` and a kernel computation of the concrete collision. Size **S** for evidence wiring.

## TTN-05 — Translation holonomy and global now

**Verdict: WEAKER.** **Row text:** “There exists an exact finite clock-translation loop with nonzero holonomy, so no route-independent global present factors through the shared boundary alone.” Ceiling: route-indexed time only. **Lean:** `lean/CSTTT/Transport/RouteDiscipline.lean:71–93` defines `CanonicalGlobalNow boundary localNow := ∃ globalNow, ∀ r, globalNow (boundary r) = localNow r` and refutes it from **assumed** same-boundary routes with different local-now values. The theorem does not construct a clock-translation loop or prove nonzero holonomy. `Prospects/Statements.lean:113–118` only defines the existential, while `Countermodels/Kernel.lean:167–182` takes same boundary as `True` and defines two distinct `Bool` local-now values.

**Wiring:** `cm07_noCanonicalGlobalNow` proves the `Prospects` proposition but is absent from the registry; the registered theorem is the generic factorization obstruction. **Certificates:** CM-07 gives a one-node clock mod 2 with loop translation 1; its generator computes a nonzero residue and distinct local-now values. `_check_cm07` (`countermodels.py:411–424`) reads stored nonzero-holonomy/global-potential flags, though it compares the two stored local-now numbers. ROUTE-COMP-FLAT/INDEXED are separate positive completion cases. **Repair:** encode the mod-2 loop and boundary map in Lean, prove the translation composition has residue 1, then instantiate the factorization theorem. Size **M**.

## TTN-06 — Withdrawn essential resource

**Verdict: WEAKER.** **Row text:** “There exists an exact finite target whose runtime behavior is maintained by an essential withdrawn resource and therefore fails post-withdrawal autonomy.” Ceiling: model-relative autonomy boundary. **Lean:** `lean/CSTTT/Autonomy/FiniteAutonomy.lean:99–109` proves `¬ Nonempty (ExactAutonomyCertificate d)` if a resource is both required at the endpoint and removed. That is a real consequence of the certificate's retained-resource rule, but no such finite `d` is constructed. `Countermodels/Kernel.lean:87–99` instead uses `supportedBehavior := True`, `essentialSupport := True`, and `postWithdrawalAutonomy := False`, proving the generic existential `Prospects/Statements.lean:121–123`.

**Wiring:** `cm04_externalSchedulerShadow` proves the generic `Prospects` instance but is omitted from the registry. **Certificates:** CM-04 has two states, supported swap `[1,0]`, and withdrawn identity step `[0,1]`. Its generator derives stall and support essentiality; `_check_cm04` (`countermodels.py:309–319`) reads the stored runtime, essentiality, progress, and autonomy flags. AUT-POS-01 is a separate positive autonomy case. The CM-04 JSON has no typed required/removed resource sets for `ExactAutonomyData`. **Repair:** add those sets by a justified model rule, instantiate `ExactAutonomyData`, and prove the theorem's premises; otherwise narrow to scheduler withdrawal and stall. Size **L**.

## TTN-07 — Stable phase without progress

**Verdict: STIPULATED.** **Row text:** “There exists an exact finite clock whose phase is stable while genuine temporal progress is absent.” Ceiling: temporal closure boundary. **Lean:** `Prospects/Statements.lean:126–128` says `∃ m, stable m ∧ ¬ progress m`; `Countermodels/Kernel.lean:106–114` assigns `stable := True` and `progress := False`, without a clock transition or `Tick`/progress definition.

**Wiring:** `cm05_stableTickWithoutProgress` proves the generic instance and is omitted from the registry. **Certificates:** CM-05 has one state, phase `[0]`, transition `[0]`; the generator computes stable phase and no change, but sets `tick_viable = True`. `_check_cm05` (`countermodels.py:338–347`) reads all three stored verdict flags. AUT-POS-01 is a different positive autonomy model. **Repair:** encode the one-state clock with actual phase-stability and progress predicates, or remove `tick_viable` if genuine tick requires advance. Size **M**.

## TTN-08 — Local/global obstruction

**Verdict: STIPULATED.** **Row text:** “There exists an exact finite family of locally accepted clause witnesses that admits no coherent global package witness.” Ceiling: global package boundary. **Lean:** `Prospects/Statements.lean:131–133` says `∃ m, allLocal m ∧ ¬ global m`. `Countermodels/Kernel.lean:194–207` makes `cm08AllLocal := True` and `cm08GlobalWitness := ∃ v, v = .zero ∧ v = .one`. The contradiction is genuine, but the chosen predicates are not `ClauseWitness` or `IntegratedPackageWitness` instances (`lean/CSTTT/Package/FiniteGluing.lean:91–99`).

**Wiring:** `cm08_localGlobalObstruction` proves the generic instance and is omitted from the registry. **Certificate:** CM-08 has two clauses assigning `0` and `1` to one shared coordinate. The generator derives lack of overlap compatibility, but sets every local acceptance to `True`; `_check_cm08` (`countermodels.py:447–459`) reads the stored local/global flags rather than checking assignment equality. **Repair:** encode two actual local clauses with conflicting overlap values, prove each is locally accepted, and refute a `restricts`-satisfying global witness. Size **M**.

## TTN-09 — Gap and resumed stream

**Verdict: STIPULATED for the concrete countermodel.** **Row text:** “There exists an exact finite episode with equivalent endpoints and a realized-time gap; it is a resumed stream rather than a strict no-gap corridor.” Ceiling: strict no-gap criterion only. **Lean:** `Prospects/Statements.lean:136–138` is the generic existential. `Countermodels/Kernel.lean:267–279` sets endpoint equivalence and gap to `True`, strict corridor to `False`. The registered `lean/CSTTT/Corridor/FiniteTemporalCorridor.lean:103–113` does soundly refute an actual atomic certificate from an unrealized listed stage, but no instance connects it to CM-12.

**Wiring:** `cm12_gapResume` proves the `Prospects` instance and is omitted from the registry. **Certificates:** CM-12's realization trace is `[1,0,1]`; the generator derives the internal gap, but defines endpoint signature equality solely by both endpoint realization bits equalling 1. `_check_cm12` (`countermodels.py:570–580`) reads stored endpoint, gap, and corridor flags. Four COR-POS certificates are separate positive corridors, not the CM-12 episode. **Repair:** encode the three stages and actual endpoint signatures in Lean, derive `¬ NoRealizedGap`, and apply `realizedGapExcludesAtomicCorridor`; justify or demote the endpoint-equivalence clause. Size **M**.

## TTN-10 — Scalar residual and hard gate

**Verdict: STIPULATED.** **Row text:** “There exists an exact finite defect profile with a small scalar mean and a failed nonnegotiable hard gate; scalar aggregation does not determine acceptance.” Ceiling: hard gates cannot be averaged. **Lean:** `Prospects/Statements.lean:141–143` is `∃ m, smallResidual m ∧ ¬ hardGate m`; `Countermodels/Kernel.lean:232–241` calculates `10 * 1 ≤ 10` but sets `cm10EveryHardGate := False`. `lean/CSTTT/Robustness/DefectVector.lean:17–21` defines actual component/vector acceptance; `:24–33` shows accepted hard gates have zero defect, while `:90–99` repackages an abstract supplied scalar contrast. No `DefectVector` instance is given for CM-10.

**Wiring:** `cm10_scalarResidualHardGateFailure` proves the generic instance and is omitted from the registry. **Certificates:** CM-10's vector has nine zeros and one one, so mean `1/10`; its generator computes the mean and failed-gate flag, but `_check_cm10` (`countermodels.py:512–520`) reads those stored flags. DEF-EQUAL-SCALAR-01 contains a stronger equal-scalar accepted/rejected pair, DEF-POS/DEF-C01–06 are defect controls, and ROB-POS is a robustness control; none is translated to Lean `DefectVector` here. **Repair:** encode the ten components with hard flags, decide vector rejection, and encode the equal-scalar pair to support the final nonidentifiability clause. Size **M**.

## TTN-11 — Symmetric fork and nonselection

**Verdict: STIPULATED for the claimed continuation fork.** **Row text:** “There exists an exact symmetric two-target fork for which swap symmetry preserves validity and no invariant unique continuer can be selected.” Ceiling: no unique identity conclusion. **Lean:** `Prospects/Statements.lean:146–149` says a valid swapped pair implies no fixed valid choice. `Countermodels/Kernel.lean:249–260` computes a fixed-point-free two-target swap but defines `cm11Valid := True`; it does not instantiate the actual `TemporalFissionCertificate` relation/validity fields (`lean/CSTTT/Corridor/Fission.lean:6–24`). The registered theorem `Fission.lean:44–53` only shows neither of two selected targets is fixed.

**Wiring:** `cm11_symmetryNoUniqueSelector` proves the generic `Prospects` proposition and is omitted from the registry. **Certificates:** CM-11 records swap `[1,0]`, both targets valid, and no fixed point; the generator computes involution/fixed points but declares all targets valid. `_check_cm11` (`countermodels.py:539–548`) reads stored symmetric-fork/nonselection flags. FISSION-POS-01 is a separate positive fork certificate, not a Lean instantiation of CM-11. **Repair:** construct a two-target `TemporalFissionCertificate` from the finite fork and prove nonselection over its actual continuation relation. Size **L**.

## TTN-12 — Finite prefix and unbounded liveness

**Verdict: WEAKER.** **Row text:** “For every tested finite horizon there is an exact countdown system that succeeds through that horizon and fails immediately afterward; finite success alone does not imply unbounded liveness.” Ceiling: finite-horizon claim ceiling. **Lean:** `lean/CSTTT/Autonomy/UnboundedInvariant.lean:87–98` defines `CountdownLive horizon time := time ≤ horizon` and proves `∀ time ≤ horizon, CountdownLive horizon time` but `¬ CountdownLive horizon (horizon+1)`, for every `horizon : Nat`. This captures the logical boundary for all horizons, but supplies no countdown transition system or autonomy policy. `Prospects/Statements.lean:152–154` is a generic existential; `Countermodels/Kernel.lean:288–310` hardcodes the two-step budget `2,1,0`.

**Wiring:** `cm13_finiteTraceNotUnbounded` proves the `Prospects` instance and is omitted from the registry; the registered arbitrary-horizon theorem is stronger on the horizon quantifier. **Certificates:** CM-13 has budget trace `[2,1,0,0]` and claimed horizon 1; its generator computes finite success, but sets unbounded liveness to `False` after finding failure. `_check_cm13` (`countermodels.py:602–612`) reads both stored verdicts. AUT-POS-01 and UNB-POS-01 are separate positive policy/invariant comparators. **Repair:** encode a transition `b ↦ max(b−1,0)` and `Live b := b>0`, construct a family indexed by each finite horizon, and derive failure at the next step. Size **M**.

## TTN-13 — Same-carrier re-encoding

**Verdict: STIPULATED.** **Row text:** “A nonidentity re-encoding on one fixed carrier does not satisfy the distinct-carrier condition required for cross-carrier transport.” Ceiling: typing boundary. **Lean:** `Prospects/Statements.lean:157–160` states `∀ m, sameCarrier m → reencoding m → ¬ crossCarrierTransport m` for arbitrary predicates. `Countermodels/Kernel.lean:317–327` makes the first two `True` and cross-carrier transport `False`. It never uses the distinct-carrier condition on `CarrierId` or a `TemporalBridge`.

**Wiring:** `cm14_sameCarrierReencoding` proves the generic `Prospects` universal and is omitted from the registry. **Certificate:** CM-14 has one carrier and a two-code swap `[1,0]`; its generator computes nonidentity, but `_check_cm14` (`countermodels.py:632–640`) reads `same_carrier`, `nontrivial_reencoding`, and `distinct_carrier_transport` flags. **Repair:** model source and target as the same actual `CarrierId`, define a nonidentity code map, and derive failure of the real distinct-carrier transport premise. Size **S**.

## TTN-14 — Marginals and recombination

**Verdict: WEAKER.** **Row text:** “There exist exact finite joint structures with identical branchwise marginals and different recombination structure; branchwise preservation does not imply integrated binding.” Ceiling: joint-structure boundary. **Lean:** `Countermodels/Kernel.lean:335–382` genuinely proves equal marginals of diagonal versus off-diagonal relations on two bits and different joint relations. This establishes the finite relation separation nontrivially. The further inference to integrated package binding is missing: `cm15BranchwisePreserved`/`cm15RecombinationPreserved` are not an actual `EightClauseIntegratedPackage`, and the registered `lean/CSTTT/Package/FusionBoundary.lean:28–39` only projects arbitrarily supplied fusion certificate fields.

**Wiring:** `cm15_branchwiseMarginals`, `cm15_recombinationDiffers`, and `cm15_branchwiseRecombinationFailure` (`Countermodels/Kernel.lean:354–382`) prove the finite separation and the generic `Prospects` proposition (`Prospects/Statements.lean:163–166`); the registry omits all three and lists only the projection theorems. **Certificates:** CM-15 has diagonal `[(0,0),(1,1)]` versus off-diagonal `[(0,1),(1,0)]`, both with full marginals. The generator computes marginals and relation inequality; `_check_cm15` (`countermodels.py:665–677`) reads stored preservation booleans. FUSION-BOUNDARY-01 is a separate merger certificate, not the CM-15 relation interpreted as a target package. **Repair:** retain and register the sound finite relation lemma, then connect joint-recombination preservation to a specified package clause or demote only the “integrated binding” inference. Size **M**.

## TTF-01 — Predictive bridge descent

**Verdict: DIVERGENT as a formal target.** **Row text:** “Open fallback target: prove that a predictive bridge descends through the declared source and target predictive equivalences.” Ceiling: fallback transport only. **Lean:** `lean/CSTTT/Prospects/Statements.lean:186–191` defines only respectfulness, `∀ a b, sourceEquivalent a b → targetEquivalent (bridge a) (bridge b)`. It does not construct a map on equivalence classes or require a respectful bridge. **Well-formedness:** the parameterized proposition has both satisfying and refuting instances: `/tmp` Lean probes prove it for `bridge = id`, both equivalences equality, and refute it when all source pairs are equivalent but target equivalence is equality on `Bool`. **Tractability:** **the universal closure without added premises is refutable** by the latter instance. With an admissible/respectful bridge premise and quotient types, descent is likely provable (**M**). **Repair:** add the premise and quotient construction, recording that as (b) mathematical change. Size **M**.

## TTF-02 — Least operational ancestry

**Verdict: DIVERGENT.** **Row text:** “Open fallback target: construct the least no-ex-nihilo operational ancestry relation generated by admissible provenance seeds.” **Lean:** `Prospects/Statements.lean:194–200` takes `seed`, `ancestry`, `closed`, and `noExNihilo` as independent parameters, then asserts inclusion, closure, and minimality among relations satisfying both predicates. There is no existential construction of `ancestry`, no definition of admissible seeds, and no closure operators. **Well-formedness:** choosing `closed := fun _ => False` refutes the proposition for every ancestry; choosing all predicates `True` and an empty ancestry can make it true. **Tractability:** **needs definitions first**: give concrete provenance seeds, closure rules, and a no-ex-nihilo rule that is preserved by intersection/induction; otherwise leastness may fail. **Repair:** define an inductive least relation and prove closure/minimality. Size **L**.

## TTF-03 — Independent twin exclusion

**Verdict: DIVERGENT.** **Row text:** “Open fallback target: prove that an independently constructed but structurally equivalent twin is excluded by no-ex-nihilo ancestry.” **Lean:** `Prospects/Statements.lean:203–205` is only `∀ source twin, ¬ operationallyConnected source twin → ¬ ancestry source twin`; structural equivalence and independence of construction are absent. **Well-formedness:** `/tmp` probes prove the proposition with empty ancestry and refute it with universal ancestry and empty connectivity on `Unit`; it is not a consequence of the parameter types. **Tractability:** **needs definitions first** for operational ancestry and independent construction; once ancestry is generated only by provenance paths, path induction should give exclusion (**M**). **Repair:** use TTF-02's actual relation and prove the no-path boundary. Size **M**.

## TTF-04 — Fission, fusion, and empty target

**Verdict: DIVERGENT.** **Row text:** “Open fallback target: characterize relation-valued fission, guarded fusion, and empty targets under least operational ancestry.” **Lean:** `Prospects/Statements.lean:208–214` asserts two ancestry edges and `(two fusion edges ∨ emptyTarget fused)` for arbitrarily supplied four nodes. There is no guard, least ancestry, classification, or quantification over cases. **Well-formedness:** it is true with universal ancestry, false with empty ancestry and `emptyTarget := False`; the supplied nodes determine its truth. **Tractability:** **needs definitions first** for branching and fusion guards; a universal characterization would require separate soundness/completeness proofs. **Repair:** split into typed fission, guarded fusion, and empty-target theorems after TTF-02. Size **L**.

## TTF-05 — Integrated Temporal-IAPS

**Verdict: PROJECTION target.** **Row text:** “Open fallback target: combine predictive ancestry, integrated target package realization, and autonomy into a Temporal-IAPS certificate.” **Lean:** `Prospects/Statements.lean:217–220` is `∀ c, valid c → ancestry c ∧ packageRealized c ∧ autonomous c` for four unrelated `Cert → Prop` predicates. No `Temporal-IAPS` data or construction exists. **Well-formedness:** setting all predicates to `True` makes it immediate; setting `valid := True`, `ancestry := False` on `Unit` refutes it. Statement-only status is expected, but this target does not constrain the intended certificate. **Tractability:** **needs definitions first**, specifically TTF-02 ancestry, TTH-02 target package, and TTH-05 autonomy as typed lanes. **Repair:** define the three-lane certificate and a non-projection assembly theorem. Size **L**.

## TTF-06 — Destructive reconstruction versus twin

**Verdict: DIVERGENT.** **Row text:** “Open fallback target: separate source-derived destructive reconstruction from an independently constructed structural twin.” **Lean:** `Prospects/Statements.lean:223–230` asks for `∃ reconstruction twin, sameStructure reconstruction twin ∧ sourceDerived reconstruction twin ∧ ancestral reconstruction twin ∧ ¬ ancestral twin reconstruction`. `sourceDerived` is a binary relation between the *two targets*, with no source node or destruction event; asymmetric ancestry is imposed rather than derived. **Well-formedness:** empty `sameStructure` refutes it; all positive relations `True` also refute the last conjunct, so existence depends on arbitrary relation assignments. **Tractability:** **needs definitions first** for source provenance, destructive operation, twin independence, and ancestry from TTF-02. **Repair:** build two finite histories with a common source structure and decide their provenance distinction. Size **L**.

## TTF-07 — Ancestry and numerical identity

**Verdict: DIVERGENT.** **Row text:** “Open fallback target: show that ancestry alone supplies no unique numerical-identity verdict under symmetric branching.” **Lean:** `Prospects/Statements.lean:233–237` requires only one ancestral swapped pair and `¬ identity s t`; there is no symmetry preservation requirement on `identity` and no universal no-unique-selector claim. **Well-formedness:** the parameterized proposition has both satisfying and refuting instances: an empty `identity` makes the existential easy on a two-target swap, while universal `identity` refutes it; `/tmp` Lean probes establish both. **Tractability:** **the universal closure without added premises is refutable** by `identity := True`; a chosen singleton identity may exist without an invariance axiom. With equivariance and a fixed-point-free fork, nonselection is likely provable (**M**). **Repair:** state the invariant-selector impossibility using an actual ancestry fork. Size **M**.

## TTF-08 — Ancestry does not supply package

**Verdict: DIVERGENT.** **Row text:** “Open fallback target: show that predictive ancestry is insufficient for integrated target package realization.” **Lean:** `Prospects/Statements.lean:240–242` is `∃ m, ancestry m ∧ ¬ packageRealized m` for arbitrary unary predicates. No predictive ancestry or package definition occurs. **Well-formedness:** `/tmp` Lean probes prove it on `Unit` with ancestry `True` and package `False`, and refute it when package is `True`; this is underdetermined by the formal target. **Tractability:** **needs definitions first** for the ancestry relation and independent package audit; then seek a source-derived target with an explicit failed package clause. **Repair:** encode such a finite countermodel and decide both predicates. Size **M**.

## Summary and combined recommendation

| Scope | Verdict | Rows | Count |
|---|---|---|---:|
| TTN | FAITHFUL | TTN-04 | 1 |
| TTN | WEAKER | TTN-05, TTN-06, TTN-12, TTN-14 | 4 |
| TTN | STIPULATED | TTN-01, TTN-02, TTN-03, TTN-07, TTN-08, TTN-09, TTN-10, TTN-11, TTN-13 | 9 |
| TTF | PROJECTION | TTF-05 | 1 |
| TTF | DIVERGENT | TTF-01, TTF-02, TTF-03, TTF-04, TTF-06, TTF-07, TTF-08 | 7 |

Across L3a and L3b: FAITHFUL 3, WEAKER 14, PROJECTION 6, STIPULATED 9, DIVERGENT 7 (39 rows). The L3a audit gives the row-specific constructive gaps. These verdicts are about **statement fidelity**, not a change to the frozen status column.

### Three distinct sets

1. **Minimal positive handoff path:** start at **TTH-06**, the single Temporal-FIACH three-lane assembly claim. Its direct lane inputs are **TTH-02** (integrated target package), **TTH-04** (strict temporal corridor), and **TTH-05** (post-withdrawal autonomy). This four-row path is the logical assembly target, not yet sufficient evidence. It needs typed, endpoint-linked concrete witnesses for all three lanes: a target-owned integrated package assembled through typed maps and compatible local assignments; an actual chain of atomic overlap legs with no realized gap, strict temporal steps, and route/owner transfer; and an `ExactAutonomyCertificate` with target-owned responses after specified resources are withdrawn. In addition, `TemporalFIACHCertificate` (`lean/CSTTT/Targets/TemporalFIACH.lean:17–44`) requires distinct source and target carriers (`:26–28`), a source-package premise and its evidence (`:29–30`), staged clause-preservation evidence (`:31–32`), a route status (`:43`) that reflects the witnessed corridor, and an honest `recognitionStatus` (`:44`), such as `.notAddressed` because recognition is outside the structural claim. Each substantive obligation must be **derived from the same concrete model**, with package, corridor, and autonomy endpoints agreeing as required by `:35–42`; an arbitrary stored proof field or route-status label is insufficient. With these obligations and the three typed lane witnesses proved and linked, a kernel-checked TTH-06 supports its conditional `exact_statement`. The three lane witnesses alone do not.
2. **Registry dependency closure:** transitive closure of those four path rows in the CSV is exactly **{TTH-01, TTH-02, TTH-03, TTH-04, TTH-05, TTH-06, TTN-03, TTN-04}**. The closure adds gluing (TTH-01), temporal transport (TTH-03), the route-predictor obstruction (TTN-04), and its holonomy prerequisite (TTN-03). Its complete edges are **TTH-01 → TTH-02; TTH-02 → TTH-05, TTH-06; TTH-03 → TTH-04; TTN-03 → TTN-04; TTN-04 → TTH-04; TTH-04 → TTH-06; TTH-05 → TTH-06**. The closure follows registry bookkeeping; TTN-03's present stipulated arrow predicate must be repaired or its interpretive claim demoted before using it as substantive route evidence.
3. **Optional negative controls:** **TTN-01** (detached copy), **TTN-05** (clock-loop holonomy), and **TTN-09** (resumed stream with a gap) are useful challenges to the same handoff predicates but are **not** dependencies of the minimal positive path. Other optional controls include TTN-06/07/08/10/11/12/13/14, selected according to the lane under test. TTH-07 is an extension for composing two handoffs; TTH-08 and TTN-11 address branching. None substitutes for the three concrete positive lane witnesses.

**Honest demotions before promotion:** keep the nine STIPULATED TTN rows at “toy separation under declared predicates,” rather than “kernel-checked countermodel of the theory,” until their real predicates are encoded. TTN-14 already has a genuine finite marginal/recombination separation; retain that proved boundary and demote only the unproved integrated-package inference. For TTN-02, TTN-07, and TTN-13, the finite abstract separation is useful even if the wider theory interpretation is demoted. For TTF-01 and TTF-07, **the universal closure without added premises is refutable**, while each parameterized proposition has both satisfying and refuting instances; neither open target should be called simply false. TTF-02–06 and TTF-08 remain open targets after their missing definitions are supplied. The conditional L3a projections TTH-02, TTH-03, TTH-06, TTH-10, and TTD-02 likewise should not be promoted on compilation alone. If their substantive bridge laws cannot be justified, revise the row text/ceiling instead of adding proof fields that merely restate the conclusion.

### Registry edges used for the global fix order

Rows absent from this table have no `dependencies` entry. Each listed edge is copied from the registry CSV; the closure edges above are its restriction to the minimal path.

| Dependent | Prerequisites (edges point into dependent) |
|---|---|
| TTN-04 | TTN-03 |
| TTH-02 | TTH-01 |
| TTH-04 | TTH-03, TTN-04 |
| TTH-05 | TTH-02 |
| TTH-06 | TTH-02, TTH-04, TTH-05 |
| TTN-09 | TTN-01 |
| TTN-05 | TTN-04 |
| TTH-09 | TTN-04, TTN-05 |
| TTH-07 | TTH-04, TTH-05, TTH-06, TTH-09 |
| TTN-06 | TTH-05 |
| TTH-08 | TTH-04, TTN-11 |
| TTD-01 | TTH-03 |
| TTD-02 | TTH-04, TTD-01 |
| TTD-03 | TTD-01, TTN-01 |
| TTH-10 | TTH-03, TTN-03 |
| TTS-01 | TTH-04, TTD-01, TTD-02 |
| TTS-02 | TTN-10 |
| TTS-03 | TTH-06, TTS-02 |
| TTS-04 | TTH-05, TTN-12 |
| TTF-01 | TTH-03 |
| TTF-02 | TTF-01 |
| TTF-03 | TTF-02 |
| TTF-04 | TTF-02, TTN-14 |
| TTF-05 | TTH-02, TTH-05, TTF-02 |
| TTF-06 | TTF-02, TTF-03 |
| TTF-07 | TTF-04, TTN-11 |
| TTF-08 | TTF-02, TTN-08 |

### Dependency-valid fix sequence

The following ordered groups cover all 39 rows. Within each group, read left to right; complete earlier groups first. A row marked as a boundary control may be repaired or honestly demoted, but its registry successor follows its disposition. Sizes are estimates for substantive implementation; “review” means the L3a fidelity finding requires no statement repair.

1. **Single-handoff closure (8 rows):** TTN-03 (**M**), TTH-03 (**L**), TTN-04 (**S** evidence wiring), TTH-01 (**review**), TTH-02 (**L**), TTH-05 (**M** positive instance), TTH-04 (**L**), TTH-06 (**L**). This order puts TTN-03 before TTN-04 and all three witnessed lanes before TTH-06.
2. **Extensions and boundary controls (23 rows):** TTN-01 (**L**), TTN-09 (**M**), TTN-05 (**M**), TTH-09 (**M**), TTH-07 (**L**), TTN-06 (**L**), TTN-11 (**L**), TTH-08 (**L**), TTD-01 (**L**), TTD-02 (**M**), TTD-03 (**M**), TTH-10 (**M**), TTS-01 (**L**), TTN-10 (**M**), TTS-02 (**M**), TTS-03 (**L**), TTN-12 (**M**), TTS-04 (**L**), TTN-02 (**L**), TTN-07 (**M**), TTN-08 (**M**), TTN-13 (**S**), TTN-14 (**M**, retain relation theorem).
3. **Fallback ancestry (8 rows):** TTF-01 (**M**, respectful bridge premise), TTF-02 (**L**, least relation), TTF-03 (**M**), TTF-04 (**L**, after both TTF-02 and TTN-14), TTF-05 (**L**), TTF-06 (**L**), TTF-07 (**M**, after TTN-11), TTF-08 (**M**, after TTN-08). The first two steps precede every later ancestry use.
