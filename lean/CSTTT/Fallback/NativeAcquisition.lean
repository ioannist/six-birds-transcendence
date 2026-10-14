import CSTTT.Fallback.NativePredictiveBridge

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeAcquisitionSeedPrototype
open RegisterInterpreter CSTTT.TransportTheory CSTTT.FallbackTheory.OperationalTrace NativePredictiveBridgePrototype
set_option autoImplicit false
-- Class (b): emitted graph edges come ONLY from actual primitive events selected by the actual executed route.
def eventReceipts (p : Input × Input) : List Bool → Option (List (Nat × Nat))
  | [] => some []
  | id::rest => do
      let event ← p.2.temporal.events.find? (fun e => e.id=id)
      if event.atomic && event.strictStep && decide (event.fromStage.val<event.toStage.val) &&
          (if id then p.1.receiver.targetFunded else p.1.receiver.sourcePresent) then
        let edges ← eventReceipts p rest
        some ((event.fromStage.val,event.toStage.val)::edges)
      else none
structure Receipt where
  initial : ModeExecution.Registers
  terminal : ModeExecution.Registers
  entry : ModeExecution.Registers
  edges : List (Nat × Nat)
-- Execution witnesses are interpreted from the SAME optional owner pair; source/entry/edge lists are never caller inputs.
noncomputable def actualReceipt (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) : Option Receipt := do
  let pair ← a cell
  let routes ← (PublicationReplay.raw cell).routes.read (NativePackageBundle.nativeInputs a)
  let _ ← (pair.2.native.temporal.histories (routes history).history).head?
  let terminal ← EpisodeExecution.sourceTerminal (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready history
  let entry ← SupportedAcquisitionSequence.firstEntry (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready history history
  let edges ← eventReceipts (pair.1.native,pair.2.native) (routes history).path
  some ⟨AcquisitionExecution.initial (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready (routes history).history,terminal,entry,edges⟩
theorem missing_event_rejected (p : Input × Input) (id : Bool) (rest : List Bool)
    (missing : p.2.temporal.events.find? (fun e => e.id=id)=none) : eventReceipts p (id::rest)=none := by
  simp [eventReceipts,missing]
theorem cut_source_events_rejected (p : NativePackageBundle.Bundle × NativePackageBundle.Bundle) (rest : List Bool) :
    eventReceipts ((NativeJointCells.cutSource p.1).native,p.2.native) (false::rest)=none := by
  cases event : p.2.native.temporal.events.find? (fun e => e.id=false) <;>
    simp [eventReceipts,NativeJointCells.cutSource]
theorem canonical_event_receipts (cell : Owner) :
    eventReceipts ((canonicalPair cell).1.native,(canonicalPair cell).2.native) [false,true]=some [(0,1),(1,2)] := by
  cases cell <;> rfl
-- The native actual acquisition has its OWN source terminal and target entry, not the source-checked proxy's virtual clocks.
theorem canonical_actual_receipt (cell : Owner) (history : Factor) :
    actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=
      some ⟨AcquisitionExecution.initial (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs NativePackageBundle.canonical) (PublicationReplay.ready cell) history,PublicationPhysical.terminalRun cell history,PublicationPhysical.entryRun cell history,[(0,1),(1,2)]⟩ := by
  have assigned : NativePackageBundle.nativeInputs NativePackageBundle.canonical=PublicationResources.assignment :=
    rfl
  have head : ((canonicalPair cell).2.native.temporal.histories history).head?=some history := by cases cell <;> rfl
  simp only [actualReceipt,canonical_pair_present,assigned,PublicationPhysical.route_reader,
    PublicationPhysical.source_terminal,PublicationPhysical.actual_entry,bind,Option.bind_some,head]
  change (do
    let edges ← eventReceipts ((canonicalPair cell).1.native,(canonicalPair cell).2.native) [false,true]
    some (Receipt.mk (AcquisitionExecution.initial (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs NativePackageBundle.canonical) (PublicationReplay.ready cell) history) (PublicationPhysical.terminalRun cell history) (PublicationPhysical.entryRun cell history) edges))=_
  rw [canonical_event_receipts]
  rfl
-- Exact all-partial decomposition into actual cell, interpreted executions, and checked primitive event graph.
theorem actual_receipt_exact (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (receipt : Receipt) :
    actualReceipt cell a ready history=some receipt ↔ ∃ pair routes payload terminal entry edges,
      a cell=some pair ∧ (PublicationReplay.raw cell).routes.read (NativePackageBundle.nativeInputs a)=some routes ∧
      (pair.2.native.temporal.histories (routes history).history).head?=some payload ∧
      EpisodeExecution.sourceTerminal (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready history=some terminal ∧
      SupportedAcquisitionSequence.firstEntry (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready history history=some entry ∧
      eventReceipts (pair.1.native,pair.2.native) (routes history).path=some edges ∧
      receipt=⟨AcquisitionExecution.initial (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready (routes history).history,terminal,entry,edges⟩ := by
  simp only [actualReceipt,bind,Option.bind_eq_some_iff,Option.some.injEq]
  constructor
  · rintro ⟨pair,hp,routes,hr,payload,hh,terminal,ht,entry,he,edges,hg,eq⟩
    exact ⟨pair,routes,payload,terminal,entry,edges,hp,hr,hh,ht,he,hg,eq.symm⟩
  · rintro ⟨pair,routes,payload,terminal,entry,edges,hp,hr,hh,ht,he,hg,eq⟩
    exact ⟨pair,hp,routes,hr,payload,hh,terminal,ht,entry,he,edges,hg,eq.symm⟩
-- Queries consume represented phase endpoints only. An absent phase endpoint rejects rather than supplying a verdict.
def endpointRead (receipt : Receipt) (source target : Nat) : Option (Factor × Factor × List (Nat × Nat)) := do
  let first ← receipt.edges.head?
  let last ← receipt.edges.getLast?
  if source=first.1 ∧ target=last.2 then
    some ((receipt.initial ()).1.factor,(receipt.entry ()).1.factor,receipt.edges)
  else none
noncomputable def scientificRead (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (source target : Nat) : Option (Factor × Factor × List (Nat × Nat)) := do
  let receipt ← actualReceipt cell a ready history
  endpointRead receipt source target
noncomputable def seedDecision (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (source target : Nat) : Option Bool := do
  let pair ← a cell
  let (original,received,edges) ← scientificRead cell a ready history source target
  let b := raw cell names (pair.1.native,pair.2.native)
  some (CSTTT.FallbackTheory.ExecutableSeed.pathBit edges source target &&
    decide (CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature b
      (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries b) original=
      CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature b
        (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries b) received))
theorem seed_some_exact (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (source target : Nat) (bit : Bool) :
    seedDecision cell names a ready history source target=some bit ↔ ∃ pair original received edges,
      a cell=some pair ∧ scientificRead cell a ready history source target=some (original,received,edges) ∧
      (CSTTT.FallbackTheory.ExecutableSeed.pathBit edges source target &&
        decide (CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature (raw cell names (pair.1.native,pair.2.native))
          (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names (pair.1.native,pair.2.native))) original=
          CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature (raw cell names (pair.1.native,pair.2.native))
            (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names (pair.1.native,pair.2.native))) received))=bit := by
  simp only [seedDecision,bind,Option.bind_eq_some_iff,Option.some.injEq]
  constructor
  · rintro ⟨pair,hp,⟨original,received,edges⟩,hr,hb⟩
    exact ⟨pair,original,received,edges,hp,hr,hb⟩
  · rintro ⟨pair,original,received,edges,hp,hr,hb⟩
    exact ⟨pair,hp,(original,received,edges),hr,hb⟩

-- The actual interpreter initializes the raw source phase; no source factor is supplied as a derived input.
theorem canonical_initial_factor (cell : Owner) (history : Factor) :
    ((AcquisitionExecution.initial (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs NativePackageBundle.canonical)
      (PublicationReplay.ready cell) history) ()).1.factor=history := by
  cases cell
  · change ((AcquisitionExecution.initial PublicationExecution.secondAcquisition PublicationExecution.nativeAssignment (PublicationReplay.ready false) history) ()).1.factor=history
    rw [PublicationExecution.second_initializer]
    rfl
  · change ((AcquisitionExecution.initial PublicationExecution.firstAcquisition PublicationExecution.nativeAssignment (PublicationReplay.ready true) history) ()).1.factor=history
    rw [PublicationExecution.first_initializer]
    rfl
theorem canonical_scientific_read (cell : Owner) (history : Factor) :
    scientificRead cell NativePackageBundle.canonical (PublicationReplay.ready cell) history 0 2=
      some (history,history,[(0,1),(1,2)]) := by
  rw [scientificRead,canonical_actual_receipt]
  simp only [bind,Option.bind_some,endpointRead,List.head?_cons,List.getLast?_cons]
  change some (((AcquisitionExecution.initial (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs NativePackageBundle.canonical) (PublicationReplay.ready cell) history) ()).1.factor,history,[(0,1),(1,2)])=_
  rw [canonical_initial_factor]
theorem canonical_seed_positive (cell : Owner) (names : Owner → CarrierId) (history : Factor) :
    seedDecision cell names NativePackageBundle.canonical (PublicationReplay.ready cell) history 0 2=some true := by
  apply (seed_some_exact _ _ _ _ _ _ _ _).mpr
  refine ⟨canonicalPair cell,history,history,[(0,1),(1,2)],canonical_pair_present cell,canonical_scientific_read cell history,?_⟩
  have path : CSTTT.FallbackTheory.ExecutableSeed.pathBit [(0,1),(1,2)] 0 2=true :=
    (CSTTT.FallbackTheory.ExecutableSeed.path_bit_exact _ _ _).mpr
      ((Path.extend (y:=1) (Path.one (by simp)) (by simp)))
  have signature := CSTTT.FallbackTheory.RawPredictiveQuotient.actual_finite_signature
    (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native))
    (canonical_map_laws cell names) (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native))) history
  change CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature _ _ history=_ at signature
  simp only [path,Bool.true_and,decide_eq_true_eq]
  exact signature.symm
-- Generic all-partial finite predictive Seed predicate, interpreted from the same acquisition result.
noncomputable def Seed (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (source target : Nat) : Prop := ∃ pair original received edges,
      a cell=some pair ∧ scientificRead cell a ready history source target=some (original,received,edges) ∧
      Path edges source target ∧
      CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature (raw cell names (pair.1.native,pair.2.native))
        (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names (pair.1.native,pair.2.native))) original=
      CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature (raw cell names (pair.1.native,pair.2.native))
        (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names (pair.1.native,pair.2.native))) received
theorem seed_true_exact (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (source target : Nat) :
    seedDecision cell names a ready history source target=some true ↔ Seed cell names a ready history source target := by
  rw [seed_some_exact]
  simp only [Seed,Bool.and_eq_true,decide_eq_true_eq,CSTTT.FallbackTheory.ExecutableSeed.path_bit_exact]
theorem seed_none_exact (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (source target : Nat) :
    seedDecision cell names a ready history source target=none ↔
      a cell=none ∨ scientificRead cell a ready history source target=none := by
  cases hp : a cell with
  | none => simp [seedDecision,hp]
  | some pair =>
    cases hr : scientificRead cell a ready history source target with
    | none => simp [seedDecision,hp,hr]
    | some value => obtain ⟨original,received,edges⟩ := value; simp [seedDecision,hp,hr]
theorem seed_false_exact (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (source target : Nat) :
    seedDecision cell names a ready history source target=some false ↔
      (a cell).isSome=true ∧ (scientificRead cell a ready history source target).isSome=true ∧
      ¬ Seed cell names a ready history source target := by
  rw [← seed_true_exact]
  cases hp : a cell with
  | none => simp [seedDecision,hp]
  | some pair =>
    cases hr : scientificRead cell a ready history source target with
    | none => simp [seedDecision,hp,hr]
    | some value =>
      obtain ⟨original,received,edges⟩ := value
      simp only [seedDecision,hp,hr,bind,Option.bind_some,Option.isSome_some,Option.some.injEq,true_and]
      cases bit : (CSTTT.FallbackTheory.ExecutableSeed.pathBit edges source target &&
        decide (CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature (raw cell names (pair.1.native,pair.2.native))
          (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names (pair.1.native,pair.2.native))) original=
          CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature (raw cell names (pair.1.native,pair.2.native))
            (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names (pair.1.native,pair.2.native))) received)) <;> simp
-- The repaired native all-word law upgrades the finite predictor to the exact all-query relation, without false pointwise bisimulation.
theorem canonical_cross_full_iff (cell : Owner) (names : Owner → CarrierId) (original received : Factor) :
    CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native))
      (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native))) original=
    CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native))
      (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native))) received ↔
    ∀ query, CSTTT.TransportTheory.sourceFuture (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native)) original query=
      CSTTT.TransportTheory.targetFuture (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native)) received query := by
  have sig := CSTTT.FallbackTheory.RawPredictiveQuotient.actual_finite_signature
    (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native)) (canonical_map_laws cell names)
    (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native))) received
  change CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature _ _ received=_ at sig
  rw [sig]
  dsimp only [canonicalPair]
  rw [canonical_finite_full_iff]
  have transport := CSTTT.FallbackTheory.RawPredictiveQuotient.actual_future_transport
    (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native)) (canonical_map_laws cell names) received
  change ∀ query, targetFuture (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) received query=sourceFuture (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) received query at transport
  change (∀ query, _ = CSTTT.TransportTheory.sourceFuture _ received query) ↔ _
  constructor
  · intro eq query; rw [transport query]; exact eq query
  · intro eq query; rw [← transport query]; exact eq query

theorem scientific_read_some_exact (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (source target : Nat) (original received : Factor) (edges : List (Nat × Nat)) :
    scientificRead cell a ready history source target=some (original,received,edges) ↔ ∃ receipt,
      actualReceipt cell a ready history=some receipt ∧ endpointRead receipt source target=some (original,received,edges) := by
  simp only [scientificRead,bind,Option.bind_eq_some_iff]
theorem endpoint_read_some_exact (receipt : Receipt) (source target : Nat)
    (original received : Factor) (edges : List (Nat × Nat)) :
    endpointRead receipt source target=some (original,received,edges) ↔ ∃ first last,
      receipt.edges.head?=some first ∧ receipt.edges.getLast?=some last ∧
      source=first.1 ∧ target=last.2 ∧
      (original,received,edges)=((receipt.initial ()).1.factor,(receipt.entry ()).1.factor,receipt.edges) := by
  cases hf : receipt.edges.head? with
  | none => simp [endpointRead,hf]
  | some first =>
    cases hl : receipt.edges.getLast? with
    | none => simp [endpointRead,hf,hl]
    | some last =>
      by_cases guard : source=first.1 ∧ target=last.2
      · simp [endpointRead,hf,hl,guard,eq_comm]
      · have absent : source≠first.1 ∨ target≠last.2 := by
          by_cases hs : source=first.1
          · exact Or.inr (fun ht => guard ⟨hs,ht⟩)
          · exact Or.inl hs
        rcases absent with hs|ht
        · simp [endpointRead,hf,hl,hs]
        · simp [endpointRead,hf,hl,ht]
-- Every positive native decision returns the SAME actually executed receipt and exact all-query prediction.
theorem canonical_seed_actual_full (cell : Owner) (names : Owner → CarrierId) (history : Factor) (source target : Nat)
    (positive : seedDecision cell names NativePackageBundle.canonical (PublicationReplay.ready cell) history source target=some true) :
    ∃ receipt, actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=some receipt ∧
      Path receipt.edges source target ∧ ∀ query,
        sourceFuture (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native)) (receipt.initial ()).1.factor query=
        targetFuture (raw cell names ((canonicalPair cell).1.native,(canonicalPair cell).2.native)) (receipt.entry ()).1.factor query := by
  obtain ⟨pair,original,received,edges,hp,hr,path,pred⟩ := (seed_true_exact _ _ _ _ _ _ _).mp positive
  have equal : pair=canonicalPair cell := Option.some.inj (hp.symm.trans (canonical_pair_present cell))
  subst pair
  obtain ⟨receipt,actual,read⟩ := (scientific_read_some_exact _ _ _ _ _ _ _ _ _).mp hr
  obtain ⟨first,last,_,_,_,_,eq⟩ := (endpoint_read_some_exact _ _ _ _ _ _).mp read
  have ho := congrArg Prod.fst eq
  have ht := congrArg (fun value : Factor × Factor × List (Nat × Nat) => value.2.1) eq
  have he := congrArg (fun value : Factor × Factor × List (Nat × Nat) => value.2.2) eq
  change original=(receipt.initial ()).1.factor at ho
  change received=(receipt.entry ()).1.factor at ht
  change edges=receipt.edges at he
  rw [ho,ht] at pred
  rw [he] at path
  exact ⟨receipt,actual,path,(canonical_cross_full_iff cell names _ _).mp pred⟩
-- Missing executed source, target entry, or selected event graph directly rejects the full receipt.
theorem failed_source_receipt_rejected (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a)) (history : Factor)
    (failed : EpisodeExecution.sourceTerminal (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready history=none) :
    actualReceipt cell a ready history=none := by
  simp only [actualReceipt]
  cases hp : a cell <;> cases hr : (PublicationReplay.raw cell).routes.read (NativePackageBundle.nativeInputs a) <;>
    simp [bind,failed]
theorem failed_entry_receipt_rejected (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a)) (history : Factor)
    (failed : SupportedAcquisitionSequence.firstEntry (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready history history=none) :
    actualReceipt cell a ready history=none := by
  simp only [actualReceipt]
  cases hp : a cell <;> cases hr : (PublicationReplay.raw cell).routes.read (NativePackageBundle.nativeInputs a) <;>
    cases ht : EpisodeExecution.sourceTerminal (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready history <;>
    simp [bind,failed]
theorem missing_phase_rejected (receipt : Receipt) (source target : Nat) (empty : receipt.edges=[]) :
    endpointRead receipt source target=none := by simp [endpointRead,empty]
-- No identity or self-loop is manufactured: each emitted edge retains the actual strict primitive phase order.
theorem event_receipts_strict (p : Input × Input) (ids : List Bool) (edges : List (Nat × Nat))
    (computed : eventReceipts p ids=some edges) : ∀ edge∈edges,edge.1<edge.2 := by
  induction ids generalizing edges with
  | nil =>
    have eq : edges=[] := Option.some.inj computed.symm
    simp [eq]
  | cons id rest ih =>
    cases found : p.2.temporal.events.find? (fun e => e.id=id) with
    | none => simp [eventReceipts,found] at computed
    | some event =>
      by_cases guard : event.atomic=true ∧ event.strictStep=true ∧ event.fromStage.val<event.toStage.val ∧
        (if id then p.1.receiver.targetFunded else p.1.receiver.sourcePresent)=true
      · have accepted : (event.atomic && event.strictStep && decide (event.fromStage.val<event.toStage.val) &&
          (if id then p.1.receiver.targetFunded else p.1.receiver.sourcePresent))=true := by
          simp only [Bool.and_eq_true,decide_eq_true_eq]
          exact ⟨⟨⟨guard.1,guard.2.1⟩,guard.2.2.1⟩,guard.2.2.2⟩
        cases remainder : eventReceipts p rest with
        | none => simp only [eventReceipts,found,bind,Option.bind_some,accepted,ite_true,remainder,Option.bind_none,reduceCtorEq] at computed
        | some tail =>
          have eq : (event.fromStage.val,event.toStage.val)::tail=edges := by
            simpa [eventReceipts,found,guard,remainder] using computed
          rw [← eq]
          intro edge member
          rcases List.mem_cons.mp member with same|mem
          · subst edge
            exact guard.2.2.1
          · exact ih tail remainder edge mem
      · have impossible : (event.atomic && event.strictStep && decide (event.fromStage.val<event.toStage.val) &&
          (if id then p.1.receiver.targetFunded else p.1.receiver.sourcePresent))≠true := by
          intro positive
          have flat : ((event.atomic=true ∧ event.strictStep=true) ∧ event.fromStage.val<event.toStage.val) ∧
            (if id then p.1.receiver.targetFunded else p.1.receiver.sourcePresent)=true := by
            simpa only [Bool.and_eq_true,decide_eq_true_eq] using positive
          exact guard ⟨flat.1.1.1,flat.1.1.2,flat.1.2,flat.2⟩
        have rejected : (event.atomic && event.strictStep && decide (event.fromStage.val<event.toStage.val) &&
          (if id then p.1.receiver.targetFunded else p.1.receiver.sourcePresent))=false := by
          cases value : (event.atomic && event.strictStep && decide (event.fromStage.val<event.toStage.val) &&
            (if id then p.1.receiver.targetFunded else p.1.receiver.sourcePresent)) with
          | false => rfl
          | true => exact False.elim (impossible value)
        simp only [eventReceipts,found,bind,Option.bind_some,rejected,Bool.false_eq_true,ite_false,reduceCtorEq] at computed

-- These are actual semantic target entries of the acquisition, with the same interpreted recipe and package assignment.
theorem canonical_receipt_entry (cell : Owner) (history : Factor) (receipt : Receipt)
    (actual : actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=some receipt) :
    PublicationResources.entries cell receipt.entry := by
  rw [canonical_actual_receipt] at actual
  have eq := Option.some.inj actual
  rw [← eq]
  cases cell
  · exact PublicationExecution.second_semantic_entry (PublicationReplay.ready false) history
  · exact PublicationExecution.first_semantic_entry (PublicationReplay.ready true) history
-- Actual source terminal and entry retain their unbounded physical clocks and interpreted owners.
theorem canonical_receipt_physical (cell : Owner) (history : Factor) (receipt : Receipt)
    (actual : actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=some receipt) :
    (receipt.terminal ()).1.counter=PublicationReplay.start cell+(PublicationReplay.jump cell-1) ∧
    (receipt.entry ()).1.counter=PublicationReplay.start cell+PublicationReplay.jump cell ∧
    (PublicationPhysical.ownerExpr cell).eval PublicationResources.assignment receipt.terminal ()=some (PublicationReplay.names cell (swapOwner cell)) ∧
    (PublicationPhysical.ownerExpr cell).eval PublicationResources.assignment receipt.entry ()=some (PublicationReplay.names cell cell) := by
  rw [canonical_actual_receipt] at actual
  have eq := Option.some.inj actual
  rw [← eq]
  exact ⟨rfl,rfl,(PublicationPhysical.actual_owners cell history).1,(PublicationPhysical.actual_owners cell history).2.2⟩
-- The exact receipt target feeds the existing controller; ancestry and continuation share an executed state.
theorem canonical_receipt_controller (cell : Owner) (history : Factor) (receipt : Receipt)
    (actual : actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=some receipt)
    (x : ModeExecution.Registers) (past : List ModeExecution.Registers)
    (play : StrategyGame.Play (ResourceRuntime.rows (PublicationResources.runtime cell) PublicationResources.assignment)
      (ResourceRuntime.update (PublicationResources.runtime cell) PublicationResources.assignment (PublicationResources.ready cell))
      PublicationResources.safeController receipt.entry (x::past)) :
    PublicationResources.packageAt cell x := by
  apply PublicationResources.package_inside cell x
  exact PublicationResources.every_safe_play_inside cell receipt.entry (canonical_receipt_entry cell history receipt actual) _ play x past rfl

-- Reject the exact raw source head used by the initializer, after the actual route selects its history.
theorem empty_copied_source_receipt_rejected (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (pair : NativePackageBundle.Bundle × NativePackageBundle.Bundle)
    (routes : Factor → AcquisitionExecution.Route Factor Bool)
    (hp : a cell=some pair)
    (hr : (PublicationReplay.raw cell).routes.read (NativePackageBundle.nativeInputs a)=some routes)
    (empty : (pair.2.native.temporal.histories (routes history).history).head?=none) :
    actualReceipt cell a ready history=none := by
  simp [actualReceipt,hp,hr,empty]

-- With a real copied source head, the actual interpreter's initialized factor equals that payload; its inherited getD fallback is unreachable.
theorem initial_from_actual_head (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (selected : Factor) (pair : NativePackageBundle.Bundle × NativePackageBundle.Bundle) (payload : Factor)
    (hp : a cell=some pair) (head : (pair.2.native.temporal.histories selected).head?=some payload) :
    ((AcquisitionExecution.initial (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready selected) ()).1.factor=payload := by
  have nativePair : NativePackageBundle.nativeInputs a cell=some (pair.1.native,pair.2.native) := by
    simp [NativePackageBundle.nativeInputs,hp]
  have initialized := ModeExecution.acquisition_initial cell (swapOwner cell) (PublicationReplay.start cell) (PublicationReplay.stride cell)
    (NativePackageBundle.nativeInputs a) ready (pair.1.native,pair.2.native) nativePair selected
  have coordinate := congrArg (fun x : ModeExecution.Registers => (x ()).1.factor) initialized
  change ((AcquisitionExecution.initial (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a) ready selected) ()).1.factor=
    (pair.2.native.temporal.histories selected).getD 0 selected at coordinate
  rw [coordinate]
  obtain ⟨tail,cons⟩ := List.head?_eq_some_iff.mp head
  simp [cons]
theorem receipt_initial_from_actual_head (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) (receipt : Receipt) (actual : actualReceipt cell a ready history=some receipt) :
    ∃ pair routes payload, a cell=some pair ∧
      (PublicationReplay.raw cell).routes.read (NativePackageBundle.nativeInputs a)=some routes ∧
      (pair.2.native.temporal.histories (routes history).history).head?=some payload ∧
      (receipt.initial ()).1.factor=payload := by
  obtain ⟨pair,routes,payload,terminal,entry,edges,hp,hr,head,_,_,_,eq⟩ := (actual_receipt_exact _ _ _ _ _).mp actual
  refine ⟨pair,routes,payload,hp,hr,head,?_⟩
  rw [eq]
  exact initial_from_actual_head cell a ready (routes history).history pair payload hp head
end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeAcquisitionSeedPrototype
