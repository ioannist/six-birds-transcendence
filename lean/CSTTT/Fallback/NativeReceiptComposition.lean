import CSTTT.Fallback.NativeWithdrawal

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeTwoHopReceiptPrototype
open RegisterInterpreter CSTTT.TransportTheory NativePredictiveBridgePrototype NativeAcquisitionSeedPrototype
set_option autoImplicit false
-- Compare every actual register coordinate, including history, funding and mode, at the literal intermediate state.
def runKey (x : ModeExecution.Registers) : Factor × Nat × Nat × Frame.Residue × Bool × Owner :=
  ((x ()).1.factor,(x ()).1.counter,(x ()).1.ticks,(x ()).1.residue,(x ()).1.funded,(x ()).2)
structure ReceiptPair where
  left : Receipt
  right : Receipt
  edges : List (Nat × Nat)
-- Both receipt executions come from one raw assignment. The interface and phase splice are checked, never supplied as success bits.
noncomputable def execute (a : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a))
    (history : Factor) : Option ReceiptPair := by
  classical
  exact do
    let left ← actualReceipt true a (ready true) history
    let right ← actualReceipt false a (ready false) history
    if runKey left.entry=runKey right.initial then
      let last ← left.edges.getLast?
      let first ← right.edges.head?
      if first.1≤last.2 then
        let offset := last.2-first.1
        some ⟨left,right,left.edges++right.edges.map (fun edge => (edge.1+offset,edge.2+offset))⟩
      else none
    else none
-- Expected output is derived from existing native interpreter recipes; it is never an execute input.
noncomputable def canonicalReceipt (cell : Owner) (history : Factor) : Receipt :=
  ⟨AcquisitionExecution.initial (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs NativePackageBundle.canonical)
    (PublicationReplay.ready cell) history,PublicationPhysical.terminalRun cell history,PublicationPhysical.entryRun cell history,[(0,1),(1,2)]⟩
theorem actual_canonical_receipt (cell : Owner) (history : Factor) :
    actualReceipt cell NativePackageBundle.canonical (PublicationReplay.ready cell) history=some (canonicalReceipt cell history) :=
  canonical_actual_receipt cell history
theorem actual_middle (history : Factor) :
    (canonicalReceipt true history).entry=(canonicalReceipt false history).initial :=
  PublicationSequence.physical_middle history
theorem canonical_two_hop (history : Factor) :
    execute NativePackageBundle.canonical PublicationReplay.ready history=
      some ⟨canonicalReceipt true history,canonicalReceipt false history,[(0,1),(1,2),(2,3),(3,4)]⟩ := by
  have matched := congrArg runKey (actual_middle history)
  simp only [execute,actual_canonical_receipt,bind,Option.bind_some,matched,ite_true]
  rfl
-- The splice has full register equality, not merely a matching scalar or history identifier.
theorem run_key_exact (x y : ModeExecution.Registers) : runKey x=runKey y ↔ x=y := by
  constructor
  · intro eq
    funext r
    cases r
    cases hx : x () with
    | mk xs xo =>
      cases hy : y () with
      | mk ys yo =>
        cases xs with
        | mk xf xc xt xr xb =>
          cases ys with
          | mk yf yc yt yr yb =>
            simp only [runKey,hx,hy,Prod.mk.injEq] at eq
            rcases eq with ⟨hfactor,hcounter,hticks,hresidue,hfunded,howner⟩
            cases hfactor; cases hcounter; cases hticks; cases hresidue; cases hfunded; cases howner
            rfl
  · intro eq; cases eq; rfl
-- The merged phase graph is emitted from the two actual event lists; its four-edge path has no reflexive convention.
theorem canonical_two_hop_path (history : Factor) :
    ∃ pair, execute NativePackageBundle.canonical PublicationReplay.ready history=some pair ∧
      CSTTT.FallbackTheory.OperationalTrace.Path pair.edges 0 4 ∧ pair.left.entry=pair.right.initial ∧
      pair.right.entry=PublicationPhysical.entryRun false history := by
  refine ⟨_,canonical_two_hop history,?_,actual_middle history,rfl⟩
  exact .extend (y:=3) (.extend (y:=2) (.extend (y:=1) (.one (by simp)) (by simp)) (by simp)) (by simp)

-- The same literal published middle data drives the first target and second source future functions.
theorem actual_middle_future (leftNames rightNames : Owner → CarrierId) (factor : Factor) (query : List Nat) :
    targetFuture (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native)) factor query=
      sourceFuture (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native)) factor query := by
  have word : ∀ w s d, targetWord (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native)) s w d=
      sourceWord (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native)) s w d := by
    intro w
    induction w with
    | nil => intro s d; rfl
    | cons action rest ih =>
      intro s d
      simp only [targetWord,sourceWord]
      change (factors.map (fun u => indexedNumerator (canonicalPair true).1.native.temporal s action u *
        targetWord (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native)) u rest d)).sum=
        (factors.map (fun u => indexedNumerator (canonicalPair false).2.native.temporal s action u *
          sourceWord (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native)) u rest d)).sum
      apply congrArg List.sum
      apply List.map_congr_left
      intro u _
      rw [ih]
      rfl
  cases query with
  | nil => rfl
  | cons destination w =>
    simp only [sourceFuture,targetFuture]
    have statesT : (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native)).targetStates=factors := rfl
    have statesS : (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native)).sourceStates=factors := rfl
    rw [statesT,statesS]
    cases found : factors[destination]? with
    | none => rfl
    | some d => exact word w factor d

theorem two_hop_future_transport (leftNames rightNames : Owner → CarrierId) (factor : Factor) (query : List Nat) :
    sourceFuture (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native)) factor query=
      targetFuture (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native)) factor query := by
  calc
    _ = targetFuture (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native)) factor query :=
      (CSTTT.FallbackTheory.RawPredictiveQuotient.actual_future_transport _ (canonical_map_laws true leftNames) factor query).symm
    _ = sourceFuture (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native)) factor query :=
      actual_middle_future leftNames rightNames factor query
    _ = _ := (CSTTT.FallbackTheory.RawPredictiveQuotient.actual_future_transport _ (canonical_map_laws false rightNames) factor query).symm
-- Source-to-final prediction, actual receipt graph and qualified post-withdrawal resource return share the same literal execution chain.
theorem canonical_two_hop_return (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor) :
    ∃ pair, execute NativePackageBundle.canonical PublicationReplay.ready history=some pair ∧
      CSTTT.FallbackTheory.OperationalTrace.Path pair.edges 0 4 ∧ pair.left.entry=pair.right.initial ∧
      (∀ query, sourceFuture (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native)) (pair.left.initial ()).1.factor query=
        targetFuture (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native)) (pair.right.entry ()).1.factor query) ∧
      NativeAcquiredWithdrawalPrototype.retainedSeedDecision false rightNames
        (PublicationComposition.cutReceiver affected NativePackageBundle.canonical) NativePackageBundle.canonical (PublicationReplay.ready false) history 0 2=some true ∧
      NativeAcquiredWithdrawalPrototype.ContinuationLaw affected false pair.right.entry := by
  refine ⟨⟨canonicalReceipt true history,canonicalReceipt false history,[(0,1),(1,2),(2,3),(3,4)]⟩,canonical_two_hop history,?_,actual_middle history,?_,
    NativeAcquiredWithdrawalPrototype.canonical_retained_seed affected false rightNames history,?_⟩
  · exact .extend (y:=3) (.extend (y:=2) (.extend (y:=1) (.one (by simp)) (by simp)) (by simp)) (by simp)
  · intro query
    change sourceFuture _ ((AcquisitionExecution.initial (PublicationReplay.raw true) (NativePackageBundle.nativeInputs NativePackageBundle.canonical)
      (PublicationReplay.ready true) history) ()).1.factor query=targetFuture _ history query
    rw [canonical_initial_factor]
    exact two_hop_future_transport leftNames rightNames history query
  · intro x past play
    exact NativeAcquiredWithdrawalPrototype.canonical_qualified_receipt_play affected false history (canonicalReceipt false history)
      (actual_canonical_receipt false history) x past play
-- The same graph splice rejects an unavailable actually executed second acquisition, irrespective of the first run.
theorem failed_second_acquisition_rejected (a : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a)) (history : Factor)
    (missing : actualReceipt false a (ready false) history=none) : execute a ready history=none := by
  cases left : actualReceipt true a (ready true) history <;> simp [execute,left,missing]
-- Full literal register mismatch directly refutes the optional splice even if both separate acquisitions succeeded.
theorem mismatched_interface_rejected (a : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs a)) (history : Factor)
    (left right : Receipt) (hl : actualReceipt true a (ready true) history=some left)
    (hr : actualReceipt false a (ready false) history=some right) (mismatch : left.entry≠right.initial) :
    execute a ready history=none := by
  have keys : runKey left.entry≠runKey right.initial := fun eq => mismatch ((run_key_exact _ _).mp eq)
  simp [execute,hl,hr,keys]

-- The combined query consumes only the outer endpoints of the emitted splice and its actual initial/final factors.
def outerRead (pair : ReceiptPair) (source target : Nat) : Option (Factor × Factor × List (Nat × Nat)) := do
  let first ← pair.edges.head?
  let last ← pair.edges.getLast?
  if source=first.1 ∧ target=last.2 then
    some ((pair.left.initial ()).1.factor,(pair.right.entry ()).1.factor,pair.edges)
  else none
noncomputable def combinedRead (acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) : Option (Factor × Factor × List (Nat × Nat)) := do
  let pair ← execute acquired ready history
  outerRead pair source target
-- Current prediction recipes and retained acquisition memory are optional RAW inputs. The two owner maps remain phase-specific.
noncomputable def retainedDecision (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) : Option Bool := do
  let left ← current true
  let right ← current false
  let (original,received,edges) ← combinedRead acquired ready history source target
  let bLeft := raw true leftNames (left.1.native,left.2.native)
  let bRight := raw false rightNames (right.1.native,right.2.native)
  some (CSTTT.FallbackTheory.ExecutableSeed.pathBit edges source target &&
    decide (CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature bLeft
      (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries bLeft) original=
      CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature bRight
        (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries bLeft) received))
noncomputable def CombinedSeed (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) : Prop := ∃ left right original received edges,
      current true=some left ∧ current false=some right ∧
      combinedRead acquired ready history source target=some (original,received,edges) ∧
      CSTTT.FallbackTheory.OperationalTrace.Path edges source target ∧
      CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature (raw true leftNames (left.1.native,left.2.native))
        (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames (left.1.native,left.2.native))) original=
      CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature (raw false rightNames (right.1.native,right.2.native))
        (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames (left.1.native,left.2.native))) received
-- Exact optional verdict over every dependency-ready partial assignment, current raw assignment and endpoint query.
theorem retained_some_exact (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) (bit : Bool) :
    retainedDecision leftNames rightNames current acquired ready history source target=some bit ↔
      ∃ left right original received edges, current true=some left ∧ current false=some right ∧
        combinedRead acquired ready history source target=some (original,received,edges) ∧
        (CSTTT.FallbackTheory.ExecutableSeed.pathBit edges source target &&
          decide (CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature (raw true leftNames (left.1.native,left.2.native))
            (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames (left.1.native,left.2.native))) original=
            CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature (raw false rightNames (right.1.native,right.2.native))
              (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames (left.1.native,left.2.native))) received))=bit := by
  simp only [retainedDecision,bind,Option.bind_eq_some_iff,Option.some.injEq]
  constructor
  · rintro ⟨left,hl,right,hr,⟨original,received,edges⟩,read,eq⟩
    exact ⟨left,right,original,received,edges,hl,hr,read,eq⟩
  · rintro ⟨left,right,original,received,edges,hl,hr,read,eq⟩
    exact ⟨left,hl,right,hr,(original,received,edges),read,eq⟩
theorem retained_true_exact (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) :
    retainedDecision leftNames rightNames current acquired ready history source target=some true ↔
      CombinedSeed leftNames rightNames current acquired ready history source target := by
  rw [retained_some_exact]
  simp only [CombinedSeed,Bool.and_eq_true,decide_eq_true_eq,CSTTT.FallbackTheory.ExecutableSeed.path_bit_exact]
theorem retained_none_exact (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) :
    retainedDecision leftNames rightNames current acquired ready history source target=none ↔
      current true=none ∨ current false=none ∨ combinedRead acquired ready history source target=none := by
  cases hl : current true with
  | none => simp [retainedDecision,hl]
  | some left =>
    cases hr : current false with
    | none => simp [retainedDecision,hl,hr]
    | some right =>
      cases read : combinedRead acquired ready history source target with
      | none => simp [retainedDecision,hl,hr,read]
      | some value => obtain ⟨original,received,edges⟩ := value; simp [retainedDecision,hl,hr,read]
theorem retained_false_exact (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) :
    retainedDecision leftNames rightNames current acquired ready history source target=some false ↔
      (current true).isSome=true ∧ (current false).isSome=true ∧
      (combinedRead acquired ready history source target).isSome=true ∧
      ¬CombinedSeed leftNames rightNames current acquired ready history source target := by
  rw [←retained_true_exact]
  cases hl : current true with
  | none => simp [retainedDecision,hl]
  | some left =>
    cases hr : current false with
    | none => simp [retainedDecision,hl,hr]
    | some right =>
      cases read : combinedRead acquired ready history source target with
      | none => simp [retainedDecision,hl,hr,read]
      | some value =>
        obtain ⟨original,received,edges⟩ := value
        simp only [retainedDecision,hl,hr,read,bind,Option.bind_some,Option.isSome_some,Option.some.injEq,true_and]
        cases bit : (CSTTT.FallbackTheory.ExecutableSeed.pathBit edges source target &&
          decide (CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature (raw true leftNames (left.1.native,left.2.native))
            (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames (left.1.native,left.2.native))) original=
            CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature (raw false rightNames (right.1.native,right.2.native))
              (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames (left.1.native,left.2.native))) received)) <;> simp
-- Finite cross-phase signatures are equivalent to ALL future words on the released native chain, without pointwise bisimulation.
theorem combined_finite_full_iff (leftNames rightNames : Owner → CarrierId) (original received : Factor) :
    CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native))
      (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native))) original=
    CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native))
      (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native))) received ↔
    ∀ query, sourceFuture (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native)) original query=
      targetFuture (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native)) received query := by
  have signatures : CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature
      (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native))
      (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native))) received=
      CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature
        (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native))
        (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native))) received := by
    unfold CSTTT.FallbackTheory.RawPredictiveQuotient.targetSignature CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature
    exact List.map_congr_left (fun query _ => (two_hop_future_transport leftNames rightNames received query).symm)
  rw [signatures]
  change CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature
    (raw true leftNames (AvailabilityPublication.selected true false,AvailabilityPublication.selected true true))
    (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames (AvailabilityPublication.selected true false,AvailabilityPublication.selected true true))) original=
    CSTTT.FallbackTheory.RawPredictiveQuotient.sourceSignature
      (raw true leftNames (AvailabilityPublication.selected true false,AvailabilityPublication.selected true true))
      (CSTTT.FallbackTheory.RawPredictiveQuotient.classQueries (raw true leftNames (AvailabilityPublication.selected true false,AvailabilityPublication.selected true true))) received ↔ _
  rw [canonical_finite_full_iff]
  constructor
  · intro full query
    exact (full query).trans (two_hop_future_transport leftNames rightNames received query)
  · intro cross query
    exact (cross query).trans (two_hop_future_transport leftNames rightNames received query).symm
theorem canonical_combined_read (history : Factor) :
    combinedRead NativePackageBundle.canonical PublicationReplay.ready history 0 4=
      some (history,history,[(0,1),(1,2),(2,3),(3,4)]) := by
  rw [combinedRead,canonical_two_hop]
  simp only [bind,Option.bind_some,outerRead,List.head?_cons,List.getLast?_cons]
  change some (((AcquisitionExecution.initial (PublicationReplay.raw true) (NativePackageBundle.nativeInputs NativePackageBundle.canonical)
    (PublicationReplay.ready true) history) ()).1.factor,history,[(0,1),(1,2),(2,3),(3,4)])=_
  rw [canonical_initial_factor]
theorem canonical_combined_positive (leftNames rightNames : Owner → CarrierId) (history : Factor) :
    retainedDecision leftNames rightNames NativePackageBundle.canonical NativePackageBundle.canonical PublicationReplay.ready history 0 4=some true := by
  apply (retained_true_exact _ _ _ _ _ _ _ _).mpr
  refine ⟨canonicalPair true,canonicalPair false,history,history,[(0,1),(1,2),(2,3),(3,4)],
    canonical_pair_present true,canonical_pair_present false,canonical_combined_read history,?_,?_⟩
  · exact .extend (y:=3) (.extend (y:=2) (.extend (y:=1) (.one (by simp)) (by simp)) (by simp)) (by simp)
  · exact (combined_finite_full_iff leftNames rightNames history history).mpr (two_hop_future_transport leftNames rightNames history)
-- Current withdrawal cannot change acquired receipts or either raw predictive signature.
theorem combined_decision_cut (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) :
    retainedDecision leftNames rightNames (PublicationComposition.cutReceiver affected current) acquired ready history source target=
      retainedDecision leftNames rightNames current acquired ready history source target := by
  cases hl : current true with
  | none => simp [retainedDecision,PublicationComposition.cutReceiver,hl]
  | some left =>
    cases hr : current false with
    | none => simp [retainedDecision,PublicationComposition.cutReceiver,hl,hr]
    | some right =>
      cases affected <;> simp only [retainedDecision,PublicationComposition.cutReceiver,hl,hr,Option.map_some,bind,Option.bind_some] <;> rfl
-- One actual final entry carries global 0-to-4 Seed, all-query transport, actual semantic Entry and the full qualified resource continuation.
theorem combined_withdrawal_return (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor) :
    ∃ pair, execute NativePackageBundle.canonical PublicationReplay.ready history=some pair ∧
      retainedDecision leftNames rightNames (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)
        NativePackageBundle.canonical PublicationReplay.ready history 0 4=some true ∧
      CSTTT.FallbackTheory.OperationalTrace.Path pair.edges 0 4 ∧ pair.left.entry=pair.right.initial ∧
      (∀ query, sourceFuture (raw true leftNames ((canonicalPair true).1.native,(canonicalPair true).2.native)) (pair.left.initial ()).1.factor query=
        targetFuture (raw false rightNames ((canonicalPair false).1.native,(canonicalPair false).2.native)) (pair.right.entry ()).1.factor query) ∧
      PublicationResources.entries false pair.right.entry ∧
      NativeAcquiredWithdrawalPrototype.ContinuationLaw affected false pair.right.entry := by
  obtain ⟨pair,actual,path,middle,future,_,continuation⟩ := canonical_two_hop_return affected leftNames rightNames history
  refine ⟨pair,actual,?_,path,middle,future,?_,continuation⟩
  · rw [combined_decision_cut]; exact canonical_combined_positive leftNames rightNames history
  · have canonical := Option.some.inj ((canonical_two_hop history).symm.trans actual)
    subst pair
    exact canonical_receipt_entry false history _ (actual_canonical_receipt false history)
-- Actual absence and actual register mismatch refute the GLOBAL combined readout directly.
theorem absent_execute_readout_rejected (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) (missing : execute acquired ready history=none) :
    retainedDecision leftNames rightNames current acquired ready history source target=none := by
  apply (retained_none_exact _ _ _ _ _ _ _ _).mpr
  right; right
  simp [combinedRead,missing]
theorem mismatched_interface_readout_rejected (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) (left right : Receipt)
    (hl : actualReceipt true acquired (ready true) history=some left)
    (hr : actualReceipt false acquired (ready false) history=some right) (mismatch : left.entry≠right.initial) :
    retainedDecision leftNames rightNames current acquired ready history source target=none :=
  absent_execute_readout_rejected leftNames rightNames current acquired ready history source target
    (mismatched_interface_rejected acquired ready history left right hl hr mismatch)

-- Exact combined read connects its factors and edge list back to one actually emitted ReceiptPair.
theorem outer_read_some_exact (pair : ReceiptPair) (source target : Nat)
    (original received : Factor) (edges : List (Nat × Nat)) :
    outerRead pair source target=some (original,received,edges) ↔ ∃ first last,
      pair.edges.head?=some first ∧ pair.edges.getLast?=some last ∧
      source=first.1 ∧ target=last.2 ∧
      (original,received,edges)=((pair.left.initial ()).1.factor,(pair.right.entry ()).1.factor,pair.edges) := by
  cases hf : pair.edges.head? with
  | none => simp [outerRead,hf]
  | some first =>
    cases hl : pair.edges.getLast? with
    | none => simp [outerRead,hf,hl]
    | some last =>
      by_cases guard : source=first.1 ∧ target=last.2
      · simp [outerRead,hf,hl,guard,eq_comm]
      · have absent : source≠first.1 ∨ target≠last.2 := by
          by_cases hs : source=first.1
          · exact Or.inr (fun ht => guard ⟨hs,ht⟩)
          · exact Or.inl hs
        rcases absent with hs|ht
        · simp [outerRead,hf,hl,hs]
        · simp [outerRead,hf,hl,ht]
theorem combined_read_some_exact (acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (source target : Nat) (original received : Factor) (edges : List (Nat × Nat)) :
    combinedRead acquired ready history source target=some (original,received,edges) ↔
      ∃ pair, execute acquired ready history=some pair ∧ outerRead pair source target=some (original,received,edges) := by
  simp only [combinedRead,bind,Option.bind_eq_some_iff]
-- Success validates full interface equality and BOTH raw-derived edge lists; the phase offset is calculated, never supplied.
theorem execute_some_exact (acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (pair : ReceiptPair) :
    execute acquired ready history=some pair ↔ ∃ left right last first,
      actualReceipt true acquired (ready true) history=some left ∧
      actualReceipt false acquired (ready false) history=some right ∧ left.entry=right.initial ∧
      left.edges.getLast?=some last ∧ right.edges.head?=some first ∧ first.1≤last.2 ∧
      pair=ReceiptPair.mk left right (left.edges++right.edges.map (fun edge => (edge.1+(last.2-first.1),edge.2+(last.2-first.1)))) := by
  cases hl : actualReceipt true acquired (ready true) history with
  | none => simp [execute,hl]
  | some left =>
    cases hr : actualReceipt false acquired (ready false) history with
    | none => simp [execute,hl,hr]
    | some right =>
      by_cases matched : left.entry=right.initial
      · cases last : left.edges.getLast? with
        | none => simp [execute,hl,hr,last,matched]
        | some l =>
          cases first : right.edges.head? with
          | none => simp [execute,hl,hr,first]
          | some f =>
            rcases l with ⟨lFrom,lTo⟩
            rcases f with ⟨fFrom,fTo⟩
            by_cases order : fFrom≤lTo
            · simp [execute,hl,hr,last,first,matched,order,eq_comm]
              constructor
              · intro eq; exact ⟨lFrom,lTo,⟨rfl,rfl⟩,order,eq⟩
              · rintro ⟨a,b,⟨rfl,rfl⟩,_,eq⟩; exact eq
            · simp [execute,hl,hr,last,first,matched,order]
      · have key : runKey left.entry≠runKey right.initial := fun eq => matched ((run_key_exact _ _).mp eq)
        simp [execute,hl,hr,key,matched]
theorem failed_first_acquisition_rejected (acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (missing : actualReceipt true acquired (ready true) history=none) :
    execute acquired ready history=none := by simp [execute,missing]
-- The original current-source final package and nominal gate are rejected on the SAME receiver cut that preserves the global ancestry return.
theorem combined_current_gates_rejected (leftNames rightNames : Owner → CarrierId) (history : Factor) :
    ¬(NativeClosedPackage.package false false).accept (PublicationComposition.cutReceiver false NativePackageBundle.canonical) ∧
    ¬PublicationNominal.PassAt false (NativePackageBundle.nativeInputs (PublicationComposition.cutReceiver false NativePackageBundle.canonical))
      (PublicationPhysical.entryRun false history) ∧
    retainedDecision leftNames rightNames (PublicationComposition.cutReceiver false NativePackageBundle.canonical)
      NativePackageBundle.canonical PublicationReplay.ready history 0 4=some true := by
  refine ⟨PostWithdrawalPrototype.cut_current_package_rejected false _,PostWithdrawalQualifiedPrototype.original_nominal_cut_rejected false _ _,?_⟩
  rw [combined_decision_cut]
  exact canonical_combined_positive leftNames rightNames history
end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeTwoHopReceiptPrototype
