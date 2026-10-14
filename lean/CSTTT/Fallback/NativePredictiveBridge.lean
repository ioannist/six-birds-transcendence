import CSTTT.Fallback.HistoricalQualifiedPackage

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePredictiveBridgePrototype
open RegisterInterpreter CSTTT.TransportTheory CSTTT.FallbackTheory.RawPredictiveQuotient
set_option autoImplicit false
-- Class (b): native factor bridge from the SAME actual input pair, with actual unbounded run recipes.
abbrev Bridge := RawBridge Factor Factor Factor Bool Factor Frame.Predictive Frame.Predictive Frame.Residue (Bool × Owner)

def action (index : Nat) : Option Bool := [false,true][index]?
def numerator (d : FactorData) (s : Factor) (a : Bool) (outcome : Factor) : Nat :=
  (((d.rows s a).filter (fun e => decide (e.1=outcome))).map Prod.snd).sum
def indexedNumerator (d : FactorData) (s : Factor) (index : Nat) (outcome : Factor) : Nat :=
  (action index).map (fun a => numerator d s a outcome) |>.getD 0
def active (cell : Owner) (p : Input × Input) (x : ModeExecution.State) : FactorData :=
  if x.2=cell then p.1.temporal else p.2.temporal
def updated (cell : Owner) (p : Input × Input) (x : ModeExecution.State) (a : Bool) (o : Factor) : ModeExecution.State :=
  (TemporalFactorRules.update (factorSchema (swapOwner cell)) (active cell p x) x.1 a o,x.2)
def eventRecord (d : FactorData) (id : Bool) : Nat :=
  ((d.events.filter (fun e => e.id=id)).map (fun e => e.toStage.val)).sum
def eventEdges (d : FactorData) : List (Bool × Bool) :=
  (d.events.zip (d.events.drop 1)).map (fun p => (p.1.id,p.2.id))
def route (d : FactorData) (h : Factor) : List Bool :=
  (d.routes.find? (fun r => decide (r.id=h))).toList.flatMap TemporalFactorRules.Route.eventPath
def raw (cell : Owner) (names : Owner → CarrierId) (p : Input × Input) : Bridge where
  frontier := factors
  sourceHistory := p.2.temporal.histories
  targetHistory := p.1.temporal.histories
  mapState := id
  sourceCoord := p.2.temporal.positions
  targetCoord := p.1.temporal.positions
  mapCoord := id
  sourceClass := TemporalFactorRules.prediction (factorSchema (swapOwner cell)) p.2.temporal
  targetClass := TemporalFactorRules.prediction (factorSchema cell) p.1.temporal
  mapClass := id
  sourceStates := factors
  targetStates := factors
  sourceClassDecEq := inferInstance
  targetClassDecEq := inferInstance
  sourceActionStep := indexedNumerator p.2.temporal
  targetActionStep := indexedNumerator p.1.temporal
  sourceStep := p.2.temporal.publishedP
  targetStep := p.1.temporal.publishedP
  sourceOrder := fun h => List.range (p.2.temporal.histories h).length
  targetOrder := fun h => List.range (p.1.temporal.histories h).length
  sourceTick := fun s => p.2.temporal.ticks s (p.2.temporal.policy s)
  targetTick := fun s => p.1.temporal.ticks s (p.1.temporal.policy s)
  sourceProgress := fun h => ((p.2.temporal.histories h).zip ((p.2.temporal.histories h).drop 1)).length
  targetProgress := fun h => ((p.1.temporal.histories h).zip ((p.1.temporal.histories h).drop 1)).length
  sourceProgressAt := fun h i => ((p.2.temporal.histories h).take (i+1)).length-1
  targetProgressAt := fun h i => ((p.1.temporal.histories h).take (i+1)).length-1
  record := ⟨eventEdges p.2.temporal,eventEdges p.1.temporal,id,eventRecord p.2.temporal,eventRecord p.1.temporal,id,
    fun first last => eventRecord p.2.temporal last-eventRecord p.2.temporal first⟩
  routeIds := factors
  routeHistory := id
  sourceRoute := route p.2.temporal
  targetRoute := route p.1.temporal
  sourceResidue := fun h => (p.2.temporal.histories h,route p.2.temporal h)
  targetResidue := fun h => (p.1.temporal.histories h,route p.1.temporal h)
  sourceReadout := fun h => if TemporalFactorRules.writer (factorSchema (swapOwner cell)) p.2.temporal
    (p.2.temporal.histories h,route p.2.temporal h) then some (p.2.temporal.histories h).length else none
  targetReadout := fun h => if TemporalFactorRules.writer (factorSchema cell) p.1.temporal
    (p.1.temporal.histories h,route p.1.temporal h) then some (p.1.temporal.histories h).length else none
  targetRouteSteps := fun h => (p.1.temporal.routes.find? (fun r => decide (r.id=h))).toList.filterMap (fun r =>
    if TemporalFactorRules.writer (factorSchema cell) p.1.temporal (p.1.temporal.histories r.history,r.eventPath)
    then some ((p.1.temporal.histories r.history,r.eventPath),(p.1.temporal.histories r.history).length) else none)
  sourceMaintenance := fun _ => (p.2.temporal.resource.rechargeAvailable,swapOwner cell)
  targetMaintenance := fun _ => (p.1.temporal.resource.rechargeAvailable,cell)
  mapMaintenance := fun m => (m.1,swapOwner m.2)
  sourceOwner := fun _ => names p.2.temporal.resource.owner
  targetOwner := fun _ => names p.1.temporal.resource.owner
  targetId := names cell
  RunState := ModeExecution.State
  RunAction := Bool
  RunOutcome := Factor
  runOutcomeDecEq := inferInstance
  runOutcomes := factors
  runDenominator := clauseSchema.rowScale
  runNumerator := fun x a o => if TemporalFactorRules.enabled (active cell p x) x.1
    then numerator (active cell p x) x.1.factor a o else 0
  runUpdate := updated cell p
  runSourceFactor := fun x => if x.2=swapOwner cell then some x.1.factor else none
  runTargetFactor := fun x => if x.2=cell then some x.1.factor else none
  runSourceOutcome := id
  runTargetOutcome := id
  runActionIndex := fun a => if a then 1 else 0
  runEnabled := fun x => TemporalFactorRules.enabled (active cell p x) x.1
  runCounter := fun x => x.1.counter
  runTicks := fun x => x.1.ticks
  RunPredictive := Frame.Predictive
  runPredictiveDecEq := inferInstance
  residueDecEq := inferInstance
  maintenanceDecEq := inferInstance
  runPredictive := fun x => TemporalFactorRules.prediction (factorSchema (swapOwner cell)) (active cell p x) x.1.factor
  sourcePredictiveMap := id
  targetPredictiveMap := id
  runProgress := fun x => x.1.counter
  runRecordWriter := fun x => TemporalFactorRules.writer (factorSchema (swapOwner cell)) (active cell p x) x.1.residue
  runResidue := fun x => x.1.residue
  runMaintenance := fun x => (x.1.funded,x.2)
  runOwner := fun x => names (active cell p x).resource.owner
  runRecord := fun x => if x.1.funded && TemporalFactorRules.writer (factorSchema (swapOwner cell))
    (active cell p x) x.1.residue then x.1.counter else 0
  runSourceFactorUpdate := fun x _ o => if x.2=swapOwner cell then some o else none
  runTargetFactorUpdate := fun x _ o => if x.2=cell then some o else none
  runPredictiveUpdate := fun x _ o => TemporalFactorRules.prediction (factorSchema (swapOwner cell)) (active cell p x) o
  runTickAdvance := fun x a _ => TemporalFactorRules.delta (factorSchema (swapOwner cell)) (active cell p x) x.1.factor a
  runProgressAdvance := fun _ _ _ => 1
  runWriterRule := fun residue owner => TemporalFactorRules.writer (factorSchema (swapOwner cell))
    (if owner=names p.1.temporal.resource.owner then p.1.temporal else p.2.temporal) residue
  runResidueUpdate := fun residue _ _ => residue
  runMaintenanceUpdate := fun maintenance _ _ =>
    (maintenance.1 && decide (TemporalFactorRules.budgetAfter
      (if maintenance.2=cell then p.1.temporal else p.2.temporal)>0),maintenance.2)
  runOwnerUpdate := fun owner _ _ => owner
  runEnabledRule := fun maintenance _ => maintenance.1 &&
    (if maintenance.2=cell then p.1.temporal else p.2.temporal).resource.rechargeAvailable &&
    decide ((if maintenance.2=cell then p.1.temporal else p.2.temporal).ledger.initial ≥
      (if maintenance.2=cell then p.1.temporal else p.2.temporal).ledger.cost)
  runTickPeriod := 2
  AuditIndex := Factor × Bool
  auditFrontier := factors.flatMap (fun h => p.2.temporal.events.map (fun e => (h,e.id)))
  auditHistory := Prod.fst
  auditState := Prod.fst
  auditOccurrence := fun point => bit point.2
  auditEvent := Prod.snd
  auditRoute := Prod.fst
  makeSourceRun := fun s count ticks residue funded => (⟨s,count,ticks,residue,funded.1⟩,swapOwner cell)
  makeTargetRun := fun s count ticks residue funded => (⟨s,count,ticks,residue,funded.1⟩,cell)

-- Actual optional cell consumption, never a default whole input pair.
def decoded (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value) : Option Bridge :=
  (a cell).map (fun pair => raw cell names (pair.1.native,pair.2.native))
theorem missing_rejected (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (missing : a cell=none) : decoded cell names a=none := by simp [decoded,missing]
theorem factor_complete (cell : Owner) (names : Owner → CarrierId) (p : Input × Input) :
    ∀ s, s∈(raw cell names p).sourceStates := factor_mem
-- Publication preserves the actual row/position/hazard data; histories and ownership may change.
theorem published_map_laws (cell : Owner) (names : Owner → CarrierId) (input : Input) :
    MapLaws (raw cell names (publish input,input)) := by
  refine ⟨?_,?_,fun _ _ h => h⟩
  · intro s; rfl
  · exact ⟨by simp [raw],fun _ _ _ => rfl⟩
theorem published_all_query_return (cell : Owner) (names : Owner → CarrierId) (input : Input) :
    ∀ s query,targetFuture (raw cell names (publish input,input)) s query=
      sourceFuture (raw cell names (publish input,input)) s query :=
  actual_future_transport _ (published_map_laws cell names input)
theorem current_receiver_cut (cell : Owner) (names : Owner → CarrierId) (p : NativePackageBundle.Bundle × NativePackageBundle.Bundle) :
    raw cell names ((NativeJointCells.cutSource p.1).native,p.2.native)=raw cell names (p.1.native,p.2.native) := rfl
-- Actual run recipes equal the existing shared register interpreter on every partial assignment with a read pair.
theorem actual_mode_update (cell : Owner) (a : Assignment Owner MemoryValue) (p : Input × Input)
    (present : a cell=some p) (x : ModeExecution.Registers) (action : Bool) (outcome : Factor) :
    (ModeExecution.updateExpr cell (swapOwner cell)).eval a x ((),action,outcome)=
      some (updated cell p (x ()) action outcome) := by
  have same := ModeExecution.mode_update_evaluation cell (swapOwner cell) a p present x () action outcome
  simpa only [updated,active,swap_owner_involution] using same
theorem actual_mode_row (cell : Owner) (a : Assignment Owner MemoryValue) (p : Input × Input)
    (present : a cell=some p) (x : ModeExecution.Registers) (action : Bool) :
    (ModeExecution.rowExpr cell (swapOwner cell)).eval a x ((),action)=
      some (TemporalFactorRules.actualRows (factorSchema (swapOwner cell)) (active cell p (x ())) (x ()).1 action) := by
  have same := ModeExecution.mode_row_evaluation cell (swapOwner cell) a p present x () action
  simpa only [active,swap_owner_involution] using same
theorem actual_run_update (cell : Owner) (names : Owner → CarrierId) (p : Input × Input)
    (x : ModeExecution.State) (action : Bool) (outcome : Factor) :
    (raw cell names p).runUpdate x action outcome=updated cell p x action outcome := rfl
theorem actual_maintenance_update (cell : Owner) (names : Owner → CarrierId) (p : Input × Input)
    (x : ModeExecution.State) (action : Bool) (outcome : Factor) :
    (raw cell names p).runMaintenance ((raw cell names p).runUpdate x action outcome)=
      (raw cell names p).runMaintenanceUpdate ((raw cell names p).runMaintenance x) action outcome := rfl
theorem actual_enabled_rule (cell : Owner) (names : Owner → CarrierId) (p : Input × Input) (x : ModeExecution.State) :
    (raw cell names p).runEnabled x=
      (raw cell names p).runEnabledRule ((raw cell names p).runMaintenance x) ((raw cell names p).runOwner x) := rfl
-- No source payload is fabricated when the actually stored source history is empty or the owner cell is missing.
def sourcePayload (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) (history : Factor) : Option Factor := do
  let pair ← a cell
  (pair.2.native.temporal.histories history).head?
theorem missing_payload_rejected (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) (history : Factor)
    (missing : a cell=none) : sourcePayload cell a history=none := by simp [sourcePayload,missing]
theorem empty_history_rejected (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) (history : Factor)
    (pair : NativePackageBundle.Bundle × NativePackageBundle.Bundle) (present : a cell=some pair)
    (empty : pair.2.native.temporal.histories history=[]) : sourcePayload cell a history=none := by simp [sourcePayload,present,empty]
-- The older pointwise row-equality bisimulation hypothesis is too strong for these actual hidden-factor rows.
theorem canonical_bisim_refuted (cell : Owner) (names : Owner → CarrierId) :
    ¬SourceActionBisim (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) := by
  intro bisim
  have classEqual : (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)).sourceClass (false,false,false)=
      (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)).sourceClass (false,false,true) := by
    cases cell <;> rfl
  have weights := bisim (false,false,false) (false,false,true) classEqual 0 (false,false,false) (factor_mem _)
  have unequal : (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)).sourceActionStep (false,false,false) 0 (false,false,false) ≠
      (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)).sourceActionStep (false,false,true) 0 (false,false,false) := by
    change indexedNumerator (AvailabilityPublication.selected cell true).temporal (false,false,false) 0 (false,false,false) ≠
      indexedNumerator (AvailabilityPublication.selected cell true).temporal (false,false,true) 0 (false,false,false)
    cases cell <;> decide +kernel
  exact unequal weights
def inputsOf (payload : Factor) (decoder : Option (Factor → Factor)) (duration maxAge : Nat) (twin : Factor) :
    CSTTT.FallbackTheory.SharedOperationalSeed.RawInputs Factor Factor :=
  ⟨0,some payload,decoder,maxAge,CSTTT.FallbackTheory.OperationalTrace.destructiveWithTwin 0 1 2 6 duration twin⟩
-- The operational raw source is decoded from the actual copied source history. Missing/empty history does not initialize it.
def checkedInputs (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) (history : Factor)
    (decoder : Option (Factor → Factor)) (duration maxAge : Nat) (twin : Factor) :
    Option (CSTTT.FallbackTheory.SharedOperationalSeed.RawInputs Factor Factor) :=
  (sourcePayload cell a history).map (fun payload => inputsOf payload decoder duration maxAge twin)
def scientificAncestry (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (history : Factor) (decoder : Option (Factor → Factor)) (duration maxAge : Nat) (twin : Factor)
    (commands : List (CSTTT.FallbackTheory.NativeDescendant.Command Factor)) (source target : Nat) : Option Bool :=
  match decoded cell names a with
  | none => none
  | some bridge => match checkedInputs cell a history decoder duration maxAge twin with
    | none => none
    | some inputs => CSTTT.FallbackTheory.ReceiptAncestry.actualAncestry bridge inputs commands source target
theorem missing_scientific_rejected (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (history : Factor) (decoder : Option (Factor → Factor)) (duration maxAge : Nat) (twin : Factor)
    (commands : List (CSTTT.FallbackTheory.NativeDescendant.Command Factor)) (source target : Nat)
    (missing : a cell=none) : scientificAncestry cell names a history decoder duration maxAge twin commands source target=none := by
  simp [scientificAncestry,decoded,missing]
theorem empty_scientific_rejected (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (history : Factor) (decoder : Option (Factor → Factor)) (duration maxAge : Nat) (twin : Factor)
    (commands : List (CSTTT.FallbackTheory.NativeDescendant.Command Factor)) (source target : Nat)
    (pair : NativePackageBundle.Bundle × NativePackageBundle.Bundle) (present : a cell=some pair)
    (empty : pair.2.native.temporal.histories history=[]) :
    scientificAncestry cell names a history decoder duration maxAge twin commands source target=none := by
  simp [scientificAncestry,decoded,checkedInputs,sourcePayload,present,empty]
-- Raw endpoint rows retain the hidden bit, while their complete future class readout descends.
theorem native_row_sum (s : Factor) (act : Bool) (f : Factor → Nat) :
    (factors.map (fun u => numerator (AvailabilityFactor.temporal false) s act u * f u)).sum=
      if act && !s.2.1 then 0 else f (destination s act) := by
  rcases s with ⟨phase,visible,hidden⟩
  cases phase <;> cases visible <;> cases hidden <;> cases act <;>
    simp [factors,numerator,AvailabilityFactor.temporal,AvailabilityFactor.rows,destination,probe]
theorem canonical_class (cell : Owner) (names : Owner → CarrierId) (s : Factor) :
    (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)).sourceClass s=
      TemporalFactorRules.prediction (factorSchema false) (AvailabilityFactor.temporal false) s := by
  cases cell <;> rfl
theorem canonical_weight (cell : Owner) (names : Owner → CarrierId) (s : Factor) (index : Nat) (u : Factor) :
    (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)).sourceActionStep s index u=
      indexedNumerator (AvailabilityFactor.temporal false) s index u := by
  cases cell <;> rfl
theorem canonical_word_cons (cell : Owner) (names : Owner → CarrierId) (s : Factor) (index : Nat)
    (rest : List Nat) (d : Factor) :
    sourceWord (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) s (index::rest) d=
      match action index with
      | none => 0
      | some act => if act && !s.2.1 then 0 else
        sourceWord (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) (destination s act) rest d := by
  rw [sourceWord]
  simp only [canonical_weight]
  cases ha : action index with
  | none => simp [indexedNumerator,ha,raw,factors]
  | some act => simp only [indexedNumerator,ha,Option.map_some,Option.getD_some]; exact native_row_sum s act _
theorem canonical_word_class_sufficient (cell : Owner) (names : Owner → CarrierId) (word : List Nat)
    (s t d : Factor)
    (equal : (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)).sourceClass s=
      (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)).sourceClass t) :
    sourceWord (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) s word d=
      sourceWord (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) t word d := by
  induction word generalizing s t with
  | nil => simp only [sourceWord,equal]
  | cons index rest ih =>
    rw [canonical_word_cons,canonical_word_cons]
    cases ha : action index with
    | none => rfl
    | some act =>
      simp only
      have nativeEqual := equal
      simp only [canonical_class] at nativeEqual
      have visibleEqual := (AvailabilityFactor.prediction_iff false s t).mp nativeEqual |>.2
      rw [visibleEqual]
      by_cases enabled : (act && !t.2.1)=true
      · simp [enabled]
      · simp only [enabled]
        apply ih
        simp only [canonical_class]
        exact AvailabilityFactor.predictive_successor false s t act nativeEqual
theorem canonical_all_query_class_sufficient (cell : Owner) (names : Owner → CarrierId) :
    SourceFutureSufficient (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) := by
  intro s t equal query
  cases query with
  | nil => rfl
  | cons index word =>
    simp only [sourceFuture]
    cases (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)).sourceStates[index]? with
    | none => rfl
    | some d => exact canonical_word_class_sufficient cell names word s t d equal
-- Complete positive AND negative available-readout equivalence on all partial native assignments.
theorem scientific_some_iff (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (history : Factor) (decoder : Option (Factor → Factor)) (duration maxAge : Nat) (twin : Factor)
    (commands : List (CSTTT.FallbackTheory.NativeDescendant.Command Factor)) (source target : Nat) (bit : Bool) :
    scientificAncestry cell names a history decoder duration maxAge twin commands source target=some bit ↔
      ∃ pair payload,a cell=some pair ∧ (pair.2.native.temporal.histories history).head?=some payload ∧
        CSTTT.FallbackTheory.ReceiptAncestry.actualAncestry (raw cell names (pair.1.native,pair.2.native))
          (inputsOf payload decoder duration maxAge twin) commands source target=some bit := by
  constructor
  · intro actual
    cases hp : a cell with
    | none => simp [scientificAncestry,decoded,hp] at actual
    | some pair =>
      cases hh : (pair.2.native.temporal.histories history).head? with
      | none => simp [scientificAncestry,decoded,checkedInputs,sourcePayload,hp,hh] at actual
      | some payload =>
        refine ⟨pair,payload,rfl,hh,?_⟩
        simpa [scientificAncestry,decoded,checkedInputs,sourcePayload,hp,hh] using actual
  · rintro ⟨pair,payload,present,head,actual⟩
    simpa [scientificAncestry,decoded,checkedInputs,sourcePayload,present,head] using actual
theorem scientific_none_iff (cell : Owner) (names : Owner → CarrierId) (a : Assignment Owner NativePackageBundle.Value)
    (history : Factor) (decoder : Option (Factor → Factor)) (duration maxAge : Nat) (twin : Factor)
    (commands : List (CSTTT.FallbackTheory.NativeDescendant.Command Factor)) (source target : Nat) :
    scientificAncestry cell names a history decoder duration maxAge twin commands source target=none ↔
      a cell=none ∨ ∃ pair,a cell=some pair ∧
        ((pair.2.native.temporal.histories history).head?=none ∨ ∃ payload,
          (pair.2.native.temporal.histories history).head?=some payload ∧
          CSTTT.FallbackTheory.ReceiptAncestry.actualRecorded (raw cell names (pair.1.native,pair.2.native))
            (inputsOf payload decoder duration maxAge twin) commands=none) := by
  constructor
  · intro actual
    cases hp : a cell with
    | none => exact Or.inl rfl
    | some pair =>
      refine Or.inr ⟨pair,rfl,?_⟩
      cases hh : (pair.2.native.temporal.histories history).head? with
      | none => exact Or.inl rfl
      | some payload =>
        refine Or.inr ⟨payload,rfl,?_⟩
        apply (CSTTT.FallbackTheory.ReceiptAncestry.actual_ancestry_none_exact _ _ _ _ _).mp
        simpa [scientificAncestry,decoded,checkedInputs,sourcePayload,hp,hh] using actual
  · rintro (missing|⟨pair,present,headMissing|⟨payload,head,failed⟩⟩)
    · exact missing_scientific_rejected cell names a history decoder duration maxAge twin commands source target missing
    · simp [scientificAncestry,decoded,checkedInputs,sourcePayload,present,headMissing]
    · have actual := (CSTTT.FallbackTheory.ReceiptAncestry.actual_ancestry_none_exact _ _ _ source target).mpr failed
      simpa [scientificAncestry,decoded,checkedInputs,sourcePayload,present,head] using actual
theorem canonical_bridge_decoded (cell : Owner) (names : Owner → CarrierId) :
    decoded cell names NativePackageBundle.canonical=
      some (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) := by
  cases cell <;> rfl
theorem canonical_source_payload (cell : Owner) (history : Factor) :
    sourcePayload cell NativePackageBundle.canonical history=some history := by cases cell <;> rfl
theorem canonical_input_decoded (cell : Owner) (history : Factor) (decoder : Option (Factor → Factor))
    (duration maxAge : Nat) (twin : Factor) :
    checkedInputs cell NativePackageBundle.canonical history decoder duration maxAge twin=
      some (inputsOf history decoder duration maxAge twin) := by
  simp [checkedInputs,canonical_source_payload]
theorem canonical_map_laws (cell : Owner) (names : Owner → CarrierId) :
    MapLaws (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) := by
  cases cell
  · exact published_map_laws false names (publish (AvailabilityFactor.input false))
  · exact published_map_laws true names (AvailabilityFactor.input false)
-- A real source-checked native-factor program computes its predictive Seed, using the SAME decoded raw class/action rows.
theorem canonical_seed (cell : Owner) (names : Owner → CarrierId) (history twin : Factor) :
    CSTTT.FallbackTheory.SharedOperationalSeed.Seed
      (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true))
      (inputsOf history (some id) 2 3 twin) 0 2 := by
  apply (CSTTT.FallbackTheory.SharedOperationalSeed.root_seed_exact _ _ _).mpr
  exact CSTTT.FallbackTheory.OperationalSeed.actual_seed_constructed
    (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true))
    (canonical_map_laws cell names) 0 1 2 6 2 3 history twin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
def canonicalPair (cell : Owner) : NativePackageBundle.Bundle × NativePackageBundle.Bundle :=
  (⟨AvailabilityPublication.selected cell false,NativePackagePrimitives.supplement⟩,
    ⟨AvailabilityPublication.selected cell true,NativePackagePrimitives.supplement⟩)
theorem canonical_pair_present (cell : Owner) : NativePackageBundle.canonical cell=some (canonicalPair cell) := by
  cases cell <;> rfl
theorem canonical_origin (history twin : Factor) :
    CSTTT.FallbackTheory.SharedOperationalSeed.computedStore (inputsOf history (some id) 2 3 twin)=
      some (CSTTT.FallbackTheory.OperationalTrace.withRawTwin 0 1 2 6 2 id history twin) := by
  exact CSTTT.FallbackTheory.SourceCheckedTrace.actual_checked_program 0 1 2 6 2 3 id history twin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem canonical_scientific_positive (cell : Owner) (names : Owner → CarrierId) (history twin : Factor) :
    scientificAncestry cell names NativePackageBundle.canonical history (some id) 2 3 twin [] 0 2=some true := by
  apply (scientific_some_iff _ _ _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨canonicalPair cell,history,canonical_pair_present cell,?_,?_⟩
  · cases cell <;> rfl
  · apply (CSTTT.FallbackTheory.ReceiptAncestry.actual_ancestry_exact _ _ _ _ _).mpr
    refine ⟨_,_,[],canonical_origin history twin,rfl,2,canonical_seed cell names history twin,Or.inl rfl⟩
theorem canonical_scientific_twin_false (cell : Owner) (names : Owner → CarrierId) (history twin : Factor) (source : Nat) :
    scientificAncestry cell names NativePackageBundle.canonical history (some id) 2 3 twin [] source 6=some false := by
  apply (scientific_some_iff _ _ _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨canonicalPair cell,history,canonical_pair_present cell,?_,?_⟩
  · cases cell <;> rfl
  · apply CSTTT.FallbackTheory.ReceiptAncestry.actual_twin_ancestry_false _ _ [] _ _ [] source 6 twin
      (canonical_origin history twin) _ _ rfl
    · simp [CSTTT.FallbackTheory.OperationalTrace.withRawTwin,CSTTT.FallbackTheory.OperationalTrace.put]
    · intro predecessor
      simp [CSTTT.FallbackTheory.OperationalTrace.withRawTwin,CSTTT.FallbackTheory.OperationalTrace.activated]
theorem canonical_finite_full_iff (cell : Owner) (names : Owner → CarrierId) (s t : Factor) :
    sourceSignature (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true))
      (classQueries (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true))) s=
    sourceSignature (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true))
      (classQueries (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true))) t ↔
    sourceEquivalent (raw cell names (AvailabilityPublication.selected cell false,AvailabilityPublication.selected cell true)) s t := by
  constructor
  · intro finite
    exact canonical_all_query_class_sufficient cell names s t
      (class_queries_detect _ (factor_complete cell names _) s t finite)
  · exact full_implies_finite _ _ s t
-- Weighted rows, including duplicates, agree exactly with actual interpreter probabilities; no probability verdict is supplied.
theorem cast_row_weight (entries : List (Factor × Nat)) (outcome : Factor) :
    List.sum (List.map Prod.snd (List.filter (fun e : Factor × Rat => decide (e.1=outcome))
      (List.map (fun e : Factor × Nat => (e.1,(e.2 : Rat))) entries)))=
    ((List.sum (List.map (fun e : Factor × Nat => e.2)
      (List.filter (fun e : Factor × Nat => decide (e.1=outcome)) entries)) : Nat) : Rat) := by
  induction entries with
  | nil => rfl
  | cons e entries ih =>
    by_cases same : e.1=outcome <;> simp [same,ih,Rat.natCast_add]
theorem rat_div_one (r : Rat) : r/1=r := by
  rw [Rat.div_def]
  have inverse : (1 : Rat)⁻¹=1 := by decide +kernel
  rw [inverse,Rat.mul_one]
theorem actual_run_weight (cell : Owner) (names : Owner → CarrierId) (p : Input × Input)
    (x : ModeExecution.State) (action : Bool) (outcome : Factor) :
    ((raw cell names p).runNumerator x action outcome : Rat)/(raw cell names p).runDenominator=
      TemporalFactorRules.weight (factorSchema (swapOwner cell)) (active cell p x) x.1 action outcome := by
  change ((if TemporalFactorRules.enabled (active cell p x) x.1 then numerator (active cell p x) x.1.factor action outcome else 0 : Nat) : Rat)/1=_
  unfold TemporalFactorRules.weight TemporalFactorRules.actualRows
  change _ = (((if TemporalFactorRules.enabled (active cell p x) x.1 then
    ((active cell p x).rows x.1.factor action).map (fun e => (e.1,(e.2 : Rat)/1)) else []).filter
      (fun e => decide (e.1=outcome))).map Prod.snd).sum
  cases enabled : TemporalFactorRules.enabled (active cell p x) x.1 with
  | false => simp [rat_div_one]
  | true => simpa [numerator,rat_div_one] using (cast_row_weight ((active cell p x).rows x.1.factor action) outcome).symm
-- Withdrawing the current receiver preserves historical source data and the computed scientific readout, including None/false cases.
theorem scientific_receiver_cut (affected cell : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value) (history : Factor) (decoder : Option (Factor → Factor))
    (duration maxAge : Nat) (twin : Factor) (commands : List (CSTTT.FallbackTheory.NativeDescendant.Command Factor))
    (source target : Nat) :
    scientificAncestry cell names (PublicationComposition.cutReceiver affected a) history decoder duration maxAge twin commands source target=
      scientificAncestry cell names a history decoder duration maxAge twin commands source target := by
  by_cases same : cell=affected
  · subst cell
    cases hp : a affected with
    | none => simp [scientificAncestry,decoded,PublicationComposition.cutReceiver,hp]
    | some pair =>
      simp only [scientificAncestry,decoded,checkedInputs,sourcePayload,PublicationComposition.cutReceiver,
        hp,Option.map_some]
      rfl
  · simp [scientificAncestry,decoded,checkedInputs,sourcePayload,PublicationComposition.cutReceiver,same]
theorem canonical_withdrawn_scientific (affected cell : Owner) (names : Owner → CarrierId) (history twin : Factor) :
    scientificAncestry cell names (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)
      history (some id) 2 3 twin [] 0 2=some true ∧
    ∀ source,scientificAncestry cell names (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)
      history (some id) 2 3 twin [] source 6=some false := by
  constructor
  · rw [scientific_receiver_cut]; exact canonical_scientific_positive cell names history twin
  · intro source; rw [scientific_receiver_cut]; exact canonical_scientific_twin_false cell names history twin source
theorem missing_decoder_store_rejected (payload twin : Factor) (duration maxAge : Nat) :
    CSTTT.FallbackTheory.SharedOperationalSeed.computedStore (inputsOf payload none duration maxAge twin)=none := by
  simp [CSTTT.FallbackTheory.SharedOperationalSeed.computedStore,inputsOf,
    CSTTT.FallbackTheory.SourceCheckedTrace.checkedExecute,CSTTT.FallbackTheory.SourceCheckedTrace.checkedRun,
    CSTTT.FallbackTheory.SourceCheckedTrace.checkedStep,CSTTT.FallbackTheory.OperationalTrace.destructiveWithTwin,
    CSTTT.FallbackTheory.OperationalTrace.step,CSTTT.FallbackTheory.OperationalTrace.initial,
    CSTTT.FallbackTheory.OperationalTrace.put,CSTTT.FallbackTheory.OperationalTrace.switch]
theorem missing_decoder_scientific_rejected (cell : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value) (history : Factor) (duration maxAge : Nat) (twin : Factor)
    (commands : List (CSTTT.FallbackTheory.NativeDescendant.Command Factor)) (source target : Nat) :
    scientificAncestry cell names a history none duration maxAge twin commands source target=none := by
  apply (scientific_none_iff _ _ _ _ _ _ _ _ _ _ _).mpr
  cases hp : a cell with
  | none => exact Or.inl rfl
  | some pair =>
    refine Or.inr ⟨pair,rfl,?_⟩
    cases hh : (pair.2.native.temporal.histories history).head? with
    | none => exact Or.inl rfl
    | some payload =>
      refine Or.inr ⟨payload,rfl,?_⟩
      simp [CSTTT.FallbackTheory.ReceiptAncestry.actualRecorded,missing_decoder_store_rejected]
end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePredictiveBridgePrototype
