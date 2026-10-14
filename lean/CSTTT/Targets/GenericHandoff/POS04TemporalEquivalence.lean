import CSTTT.Targets.GenericHandoff.POS04TemporalFactor
import CSTTT.Targets.GenericHandoff.POS04FutureLumping
import CSTTT.Targets.GenericHandoff.TemporalFactorFuture
import CSTTT.Targets.GenericHandoff.ProfileNormalization
import CSTTT.Targets.GenericHandoff.POS04OperationalCompletion

/-! Exact arbitrary-partial-assignment specialization of the finite C6 rule.
Every dependency must be present before the Option decoder yields raw data.
No canonical fallback can discharge a missing-input check. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04TemporalFactor
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

 theorem decoded_complete (a : CSTTT.POS04.Assigned.Assignment) (t : Tag)
    (hc : CSTTT.POS04.Assigned.Complete (clauseScope t .c6) a) :
    TemporalFactorCells.decoded (bindings t) a = some (raw (runInputs6 a t) t) := by
  have complete (k : Cell) (hk : k ∈ clauseScope t .c6) := POS04RegisterDynamics.cell_value (hc k hk)
  have h1 := complete (.rows t) (by simp [clauseScope,commonScope])
  have h2 := complete .positions (by simp [clauseScope,commonScope])
  have h3 := complete .hazards (by simp [clauseScope,commonScope])
  have h4 := complete .policy (by simp [clauseScope,commonScope])
  have h5 := complete .publishedM (by simp [clauseScope,commonScope])
  have h6 := complete .publishedP (by simp [clauseScope,commonScope])
  have h7 := complete (.ticks t) (by simp [clauseScope,commonScope])
  have h8 := complete (.resources t) (by simp [clauseScope,commonScope])
  have h9 := complete .maintenance (by simp [clauseScope,commonScope])
  have h10 := complete .interface (by simp [clauseScope,commonScope])
  have h11 := complete .histories (by simp [clauseScope,commonScope])
  have h12 := complete .eventTable (by simp [clauseScope,commonScope])
  have h13 := complete .realized (by simp [clauseScope,commonScope])
  have h14 := complete .receiverInput (by simp [clauseScope,commonScope])
  have h15 := complete .routeTable (by simp [clauseScope,commonScope])
  have h16 := complete .writers (by simp [clauseScope,commonScope])
  simp only [TemporalFactorCells.decoded,bindings,CellView.read]
  rw [h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16]
  cases t <;> rfl

theorem decoded_complete_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    (∃ d, TemporalFactorCells.decoded (bindings t) a = some d) ↔
      CSTTT.POS04.Assigned.Complete (clauseScope t .c6) a := by
  constructor
  · rintro ⟨d,hd⟩ k hk
    cases he : a k with
    | some v => rfl
    | none =>
      have hm := TemporalFactorCells.missing_input (bindings t) a k ((scope_membership t k).mpr hk) he
      rw [hm] at hd
      contradiction
  · intro hc; exact ⟨_,decoded_complete a t hc⟩

def predictionImage : CSTTT.POS04.PredictiveNow → TemporalFactorRules.Predictive Ambient
  | .active v => .inl v
  | .exit2 => .inr .p2w0
  | .exit5 => .inr .p5w1

theorem predictionImage_injective : Function.Injective predictionImage := by
  intro x y he; cases x <;> cases y <;> simp_all [predictionImage]

theorem prediction_eq (d : RunInputs6) (t : Tag) (o : Ambient) :
    TemporalFactorRules.prediction (schema t) (raw d t) o = predictionImage (predictive6 d o) := by
  cases o <;> rfl

theorem row_eq (d : RunInputs6) (t : Tag) (o : Ambient) (a : Action) :
    TemporalFactorRules.row (schema t) (raw d t) o a = row6 d o a := by cases o <;> rfl

theorem delta_eq (d : RunInputs6) (t : Tag) (o : Ambient) (a : Action) :
    TemporalFactorRules.delta (schema t) (raw d t) o a = delta6 d o a := by cases o <;> rfl

theorem mass_eq (d : RunInputs6) (t : Tag) (o : Ambient) (a : Action) (c : CSTTT.POS04.PredictiveNow) :
    TemporalFactorRules.mass (schema t) (raw d t) o a (predictionImage c) = mass6 d o a c := by
  simp only [TemporalFactorRules.mass,row_eq,mass6]
  congr 1
  apply List.filter_congr
  intro e _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,prediction_eq]
  exact ⟨fun h => predictionImage_injective h,congrArg predictionImage⟩

local instance : LawfulBEq (TemporalFactorRules.Predictive Ambient) where
  rfl := by
    intro x
    cases x with
    | inl v => exact beq_self_eq_true v
    | inr v => exact beq_self_eq_true v
  eq_of_beq := by
    intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl w => exact congrArg Sum.inl (LawfulBEq.eq_of_beq (a := v) (b := w) h)
      | inr w => contradiction
    | inr v =>
      cases y with
      | inl w => contradiction
      | inr w => exact congrArg Sum.inr (LawfulBEq.eq_of_beq (a := v) (b := w) h)

theorem class_cover (d : RunInputs6) (t : Tag) (o : Ambient) :
    predictionImage (predictive6 d o) ∈ TemporalFactorRules.outcomeClasses (schema t) (raw d t) := by
  apply (ProfileRules.dedup_mem _ _).mpr
  apply List.mem_map.mpr
  refine ⟨o,?_,prediction_eq d t o⟩
  change o ∈ ambientStates
  cases o with
  | inK k => cases k <;> decide
  | p2w0 => decide
  | p5w1 => decide

theorem finite_bisim_iff (d : RunInputs6) (t : Tag) :
    TemporalFactorRules.FiniteBisim (schema t) (raw d t) ↔ FiniteBisim6 d := by
  simp only [TemporalFactorRules.FiniteBisim,FiniteBisim6,List.all_eq_true,decide_eq_true_eq]
  constructor
  · intro h s hs u hu a ha hp
    obtain ⟨hm,ht⟩ := h s hs u hu a ha (by rw [prediction_eq,prediction_eq,hp])
    refine ⟨?_,by simpa only [delta_eq] using ht⟩
    intro c hc
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hc
    have eq := hm _ (class_cover d t o)
    simpa only [mass_eq] using eq
  · intro h s hs u hu a ha hp
    obtain ⟨hm,ht⟩ := h s hs u hu a ha (predictionImage_injective (by simpa only [prediction_eq] using hp))
    refine ⟨?_,by simpa only [delta_eq] using ht⟩
    intro c hc
    obtain ⟨o,ho,rfl⟩ := List.mem_map.mp ((ProfileRules.dedup_mem _ _).mp hc)
    rw [prediction_eq,mass_eq,mass_eq]
    exact hm _ (outcomes6_cover d o)

theorem policy_weight_eq (d : RunInputs6) (t : Tag) (s u : KState) :
    TemporalFactorRules.policyWeight (schema t) (raw d t) s u =
      rowWeight (d.base.base.rows s (d.base.base.policy s)) u := by
  rw [POS04ObjecthoodQuotient.rowWeight_sum]
  unfold TemporalFactorRules.policyWeight
  congr 1
  apply List.map_congr_left
  intro e _
  cases e.1 <;> simp [schema,POS04ProfileRules.clauseSchema,POS04ProfileRules.schema]

theorem reference_iff (d : RunInputs6) (t : Tag) :
    TemporalFactorRules.Reference (schema t) (raw d t) ↔ Reference6 d := by
  simp only [TemporalFactorRules.Reference,Reference6,policy_weight_eq]
  rfl

theorem strict_event_eq (d : RunInputs6) (t : Tag) (e : CSTTT.POS04.Event) :
    TemporalFactorRules.strictEvent (schema t) (raw d t) (eventMap e) = strictEvent6 d e := rfl

theorem event_eq (d : RunInputs6) (t : Tag) (id : EventId) :
    TemporalFactorRules.event (raw d t) id = (event6 d id).map eventMap := by
  simp only [TemporalFactorRules.event,raw,List.find?_map,Function.comp_def,eventMap,event6]

theorem route_eq (d : RunInputs6) (t : Tag) (id : RouteId) :
    TemporalFactorRules.route (raw d t) id =
      (d.base.routes.find? (fun r => r.id == id)).map routeMap := by
  simp only [TemporalFactorRules.route,raw,List.find?_map,Function.comp_def,routeMap,Bool.beq_eq_decide_eq]

theorem supported_eq (d : RunInputs6) (t : Tag) (h : HistoryId) :
    TemporalFactorRules.supported (schema t) (raw d t) h = historySupported d.base h := by
  simp only [TemporalFactorRules.supported,historySupported,pathSupported,policy_weight_eq]
  rfl

theorem path_eq (d : RunInputs6) (t : Tag) (id : RouteId) :
    TemporalFactorRules.path (schema t) (raw d t) id = path6 d id := by
  simp only [TemporalFactorRules.path,route_eq,path6,routeTuple]
  cases hr : d.base.routes.find? (fun r => r.id == id) with
  | none => rfl
  | some r =>
    simp only [Option.map_some,routeMap,supported_eq,historySupported,event_eq,Option.any_map,strict_event_eq]
    have hempty := Bool.and_self (!((d.base.histories r.sourceHistory).isEmpty))
    simp only [pathSupported,Bool.and_assoc] at *
    simp only [← Bool.and_assoc,hempty]
    congr 1
    apply List.all_congr
    · rfl
    · intro p
      cases he : event6 d p.1 <;> cases hf : event6 d p.2 <;> rfl

theorem paths_eq (d : RunInputs6) (t : Tag) :
    TemporalFactorRules.paths (schema t) (raw d t) = paths6 d := by
  have hpath : TemporalFactorRules.path (schema t) (raw d t) = path6 d := funext (path_eq d t)
  simp only [TemporalFactorRules.paths,paths6,hpath,event_eq,Option.any_map,strict_event_eq]
  simp only [schema,raw,List.any_map,routeMap,Function.comp_def]

theorem trace_iff (d : RunInputs6) (t : Tag) :
    TemporalFactorRules.Trace (schema t) (raw d t) ↔ Trace6 d t := by
  simp only [TemporalFactorRules.Trace,Trace6,paths_eq]
  rfl

theorem observableMap_injective : Function.Injective observableMap := by
  intro x y h; cases x <;> cases y <;> simp_all [observableMap]

theorem interface_iff (d : RunInputs6) (t : Tag) :
    (raw d t).interface = TemporalFactorRules.interface ↔ d.interface = futureInterface := by
  change d.interface.map observableMap = futureInterface.map observableMap ↔ _
  exact List.map_inj_right (fun _ _ h => observableMap_injective h)

theorem funding_iff (d : RunInputs6) (t : Tag) :
    TemporalFactorRules.Funding (schema t) (raw d t) ↔
      (d.ledger.initialBudget = 1 ∧ d.ledger.actionCost = 1 ∧ d.ledger.rechargePerAction = 1) := by
  simp [TemporalFactorRules.Funding,schema,raw,ledger]
  intro hb hc hq; simp [hb,hc,hq]

theorem coarser_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    TemporalFactorRules.Coarser (schema t) (raw (runInputs6 a t) t) ↔ Coarser6 a t := by
  change ((Ambient.inK .p0w0 ≠ Ambient.inK .p0w1) ∧
    TemporalFactorRules.prediction (schema t) (raw (runInputs6 a t) t) (.inK .p0w0) =
    TemporalFactorRules.prediction (schema t) (raw (runInputs6 a t) t) (.inK .p0w1)) ↔ _
  rw [prediction_eq,prediction_eq]
  have hp : predictionImage (predictive6 (runInputs6 a t) (.inK .p0w0)) =
      predictionImage (predictive6 (runInputs6 a t) (.inK .p0w1)) ↔
      predictive6 (runInputs6 a t) (.inK .p0w0) = predictive6 (runInputs6 a t) (.inK .p0w1) :=
    ⟨fun h => predictionImage_injective h,congrArg predictionImage⟩
  simp only [hp,Coarser6,future6,code6,initial6,C6Code.mk.injEq]
  constructor
  · rintro ⟨_,he⟩; exact ⟨by simpa using he,by intro h; have hh := congrArg Run6.factor h; contradiction⟩
  · rintro ⟨he,_⟩; exact ⟨by decide,by simpa using he⟩

theorem rows_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    ProfileRules.RowsValid (schema t).base (TemporalFactorRules.profile (schema t) (raw (runInputs6 a t) t)) ↔
      RowsValid (clauseInputs a t .c6) := Iff.rfl

theorem raw_accept_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    TemporalFactorRules.Accept (schema t) (raw (runInputs6 a t) t) ↔
      RowsValid (clauseInputs a t .c6) ∧ Reference6 (runInputs6 a t) ∧
      Trace6 (runInputs6 a t) t ∧ LedgerConservation6 a t ∧
      (runInputs6 a t).interface = futureInterface ∧ UnitFunding6 (runInputs6 a t) ∧
      FiniteBisim6 (runInputs6 a t) ∧ Coarser6 a t := by
  have hd : ProfileRules.DomainCheck (schema t).base := POS04ProfileRules.domain_checked
  simp only [TemporalFactorRules.Accept,hd,true_and,
    rows_iff,reference_iff,trace_iff,interface_iff,funding_iff,finite_bisim_iff,coarser_iff]
  change (1 > 0 ∧ 1 > 0 ∧ _) ↔ _
  simp only [Nat.zero_lt_succ,true_and]
  unfold LedgerConservation6 UnitFunding6 budgetAfter6 budget6
  constructor
  · rintro ⟨hr,hm,ht,⟨hb,hc,hq⟩,hi,hf,hco⟩
    have hpos : (runInputs6 a t).ledger.initialBudget > 0 := by omega
    have hcons : (runInputs6 a t).ledger.initialBudget - (runInputs6 a t).ledger.actionCost +
        (runInputs6 a t).ledger.rechargePerAction = (runInputs6 a t).ledger.initialBudget := by omega
    exact ⟨hr,hm,ht,hcons,hi,⟨hb,hc,hq,hpos,by omega⟩,hf,hco⟩
  · rintro ⟨hr,hm,ht,_,hi,⟨hb,hc,hq,_,_⟩,hf,hco⟩
    exact ⟨hr,hm,ht,⟨hb,hc,hq⟩,hi,hf,hco⟩

theorem generic_c6_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    TemporalFactorCells.Accept (schema t) (bindings t) a ↔ C6Accept a t := by
  constructor
  · rintro ⟨d,hd,hpass⟩
    have hc := (decoded_complete_iff a t).mp ⟨d,hd⟩
    have he := Option.some.inj (hd.symm.trans (decoded_complete a t hc))
    subst d
    obtain ⟨hr,hm,ht,hl,hi,hfund,hb,hco⟩ := (raw_accept_iff a t).mp hpass
    exact ⟨⟨⟨hc,hr⟩,hm,ht,hl,hi,hfund⟩,hb,hco⟩
  · intro hp
    refine ⟨_,decoded_complete a t hp.1.1.1,?_⟩
    exact (raw_accept_iff a t).mpr
      ⟨hp.1.1.2,hp.1.2.1,hp.1.2.2.1,hp.1.2.2.2.1,hp.1.2.2.2.2.1,hp.1.2.2.2.2.2,hp.2.1,hp.2.2⟩

end CSTTT.TargetTheory.GenericHandoff.POS04TemporalFactor
