import CSTTT.Targets.GenericHandoff.StaticSlice
import CSTTT.Targets.GenericHandoff.POS04HistoricalAcquisition
import CSTTT.Targets.GenericHandoff.POS04HistoricalAutonomy
import CSTTT.Targets.GenericHandoff.POS04HistoricalDuplicateEvents

/-! Exact raw phase-2 protocol extraction for the historical F/O adapter.
G6_lane_spec §§3,4F,4O: activation, realized strict path, source/target
historical support, typed boundaries, target ownership/resources, writer, and
strictly positive normalized response entries. A static instruction reads ALL
twelve consumed cells before this raw rule can run. Neither an entry set nor
an AF/AO result is stored. This is the acquisition-protocol component, not the
whole package/resource/game equivalence or the final RawHandoff. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalProtocol
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter RegisterInitialization
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Raw phase-2 interpretation in the already-staged namespace. The other
RawLaneModel fields do not enter phase2Check. Staging back is an involution. -/
def model (a : CSTTT.POS04.Assigned.Assignment) : RawLaneModel :=
  {baseline with assignment := exchangeAssignment a}

theorem image_model (a : CSTTT.POS04.Assigned.Assignment) : image (model a).assignment = a :=
  exchange_assignment_involution a

theorem phase2_assignment_only (m n : RawLaneModel)
    (h : image m.assignment = image n.assignment) (rid : RouteId) :
    phase2Check m rid = phase2Check n rid := by
  simp only [phase2Check,phase2Complete,arrivalInputs,h]

theorem phase2_locality (m n : RawLaneModel)
    (he : Assigned.Agrees phase2Dependencies (image m.assignment) (image n.assignment))
    (rid : RouteId) : phase2Check m rid = phase2Check n rid := by
  have hc : phase2Complete m = phase2Complete n := by
    unfold phase2Complete
    have eqv := Assigned.complete_locality he
    by_cases h : Assigned.Complete phase2Dependencies (image m.assignment)
    · simp only [decide_eq_true h,decide_eq_true (eqv.mp h)]
    · have hn : ¬ Assigned.Complete phase2Dependencies (image n.assignment) := fun hn => h (eqv.mpr hn)
      simp only [decide_eq_false h,decide_eq_false hn]
  simp only [phase2Check,hc]
  simp only [arrivalInputs,runInputs6,clauseExtra,extraInputs,inputs,
    clause8,viabilityInputs,Assigned.decode,
    routeTuple,path6,event6,pathSupported,active7,mixed7,available8]
  try simp only [clauseScope,commonScope]
  simp only [he (.rows .source) (by decide),he (.rows .target) (by decide),
    he .policy (by decide),he (.ticks .target) (by decide),he (.resources .target) (by decide),
    he .maintenance (by decide),he .histories (by decide),he .eventTable (by decide),
    he .realized (by decide),he .receiverInput (by decide),he .routeTable (by decide),
    he .writers (by decide)]
  rfl

/-- Pure raw rule applied after the instruction has read the declared slice. -/
def check (rid : RouteId) : StaticView Cell Value Bool :=
  ⟨.map (fun a => phase2Check (model a) rid) (StaticSlice.instruction phase2Dependencies)⟩

theorem check_dependencies (rid : RouteId) : (check rid).dependencies = phase2Dependencies := by
  simp only [check,StaticView.dependencies,Expr.dependencies,StaticSlice.dependencies]

theorem check_computed (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Assigned.Complete phase2Dependencies a) (rid : RouteId) :
    (check rid).read a = some (phase2Check (model a) rid) := by
  change ((StaticSlice.instruction phase2Dependencies).eval a noRegisters ()).map _ = _
  rw [StaticSlice.evaluation phase2Dependencies a hc]
  simp only [Option.map_some]
  apply congrArg some
  apply phase2_locality
  intro k hk
  rw [image_model,image_model]
  simp [GenericHandoff.decode,hk]

/-- Exact arbitrary-partial acceptance, including rejection on EVERY missing
consumed cell. Canonical truth is not substituted for this biconditional. -/
theorem check_iff (m : RawLaneModel) (rid : RouteId) :
    (check rid).read (image m.assignment) = some true ↔ phase2Check m rid = true := by
  constructor
  · intro hp
    have hc : Assigned.Complete phase2Dependencies (image m.assignment) := by
      intro k hk
      cases hv : image m.assignment k with
      | some v => rfl
      | none =>
        have bad := (check rid).missing (image m.assignment) k (by rw [check_dependencies]; exact hk) hv
        rw [bad] at hp
        contradiction
    rw [check_computed _ hc] at hp
    exact (phase2_assignment_only (model (image m.assignment)) m (image_model _) rid).symm.trans (Option.some.inj hp)
  · intro hp
    have hc : phase2Complete m = true := by
      by_cases ht : phase2Complete m = true
      · exact ht
      · have hf : phase2Complete m = false := Bool.eq_false_iff.mpr ht
        simp [phase2Check,hf] at hp
    rw [check_computed _ (of_decide_eq_true hc)]
    rw [phase2_assignment_only (model (image m.assignment)) m (image_model _) rid,hp]

theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment)
    (rid : RouteId) (k : Cell) (hk : k ∈ phase2Dependencies) (hm : a k = none) :
    (check rid).read a = none :=
  (check rid).missing a k (by rw [check_dependencies]; exact hk) hm

theorem check_locality {a b : CSTTT.POS04.Assigned.Assignment}
    (h : Assigned.Agrees phase2Dependencies a b) (rid : RouteId) :
    (check rid).read a = (check rid).read b :=
  (check rid).locality (by simpa only [check_dependencies] using h)

/-- Every route check consumes exactly the declared phase-2 slice. -/
def AllRoutes (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  ∀ rid ∈ routeIds, (check rid).read a = some true

theorem all_routes_iff (m : RawLaneModel) : AllRoutes (image m.assignment) ↔
    routeIds.all (phase2Check m) = true := by
  simp only [AllRoutes,check_iff,List.all_eq_true]

theorem protocol_checks_all_routes (m : RawLaneModel) (h : POS04OperationalGame.Protocol m) :
    AllRoutes (image m.assignment) := (all_routes_iff m).mpr h.2.2.2.2

theorem scope_subset : POS04HistoricalAcquisition.scope ⊆ phase2Dependencies := by decide

/-- The static check's complete slice supplies genuine generic acquisition
readiness; no source tick, source funding, or hazard dependency is added. -/
theorem ready_of_check (m : RawLaneModel) (rid : RouteId) (h : phase2Check m rid = true) :
    HistoricalAcquisition.Ready POS04HistoricalAcquisition.raw (image m.assignment) := by
  have hc : phase2Complete m = true := by
    by_cases ht : phase2Complete m = true
    · exact ht
    · have hf : phase2Complete m = false := Bool.eq_false_iff.mpr ht
      simp [phase2Check,hf] at h
  exact POS04HistoricalAcquisition.ready _ (fun k hk => (of_decide_eq_true hc) k (scope_subset hk))

/-- Exact actual target response row, including every ambient branch.
The checked acquisition and frozen phase-2 rule read the same staged cells. -/
theorem response_rows (m : RawLaneModel) (rid : RouteId) (history : List KState)
    (path : List EventId) (hp : phase2Check m rid = true)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,path)) :
    let received : Run6 := ⟨.inK (history.getLastD .p0w0),0,0,(history,path),
      (arrivalInputs m).base.receiver.funded⟩
    HistoricalAcquisition.rows POS04HistoricalAcquisition.raw (image m.assignment)
      (POS04RegisterDynamics.encode received) .nominal
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) =
    ((arrivalInputs m).base.base.rows (history.getLastD .p0w0)
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0))).map
      (fun e => (e.1,(e.2 : Rat)/4)) := by
  dsimp only
  rw [POS04HistoricalAcquisition.actual_row _ (ready_of_check m rid hp)]
  exact POS04HistoricalAutonomy.target_response_row m rid history path hp ht

theorem response_normalized (m : RawLaneModel) (rid : RouteId) (history : List KState)
    (path : List EventId) (hp : phase2Check m rid = true)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,path)) :
    let received : Run6 := ⟨.inK (history.getLastD .p0w0),0,0,(history,path),
      (arrivalInputs m).base.receiver.funded⟩
    StrategyGame.Normalized (HistoricalAcquisition.rows POS04HistoricalAcquisition.raw (image m.assignment))
      (POS04RegisterDynamics.encode received) .nominal
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) := by
  obtain ⟨_,hn,hs,hpos⟩ := POS04HistoricalAutonomy.phase2_target_facts m rid history path hp ht
  have hnorm := ScaledRows.normalized 4
    ((arrivalInputs m).base.base.rows (history.getLastD .p0w0)
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0))) (by decide)
    (List.isEmpty_eq_false_iff.mp hn) hs (fun e he => (hpos e he).1)
  rcases hnorm with ⟨hnon,hmass,o,w,hmem,hweight⟩
  exact ⟨by simpa only [response_rows m rid history path hp ht] using hnon,
    by simpa only [response_rows m rid history path hp ht] using hmass,
    o,w,by simpa only [response_rows m rid history path hp ht] using hmem,hweight⟩

/-- Every raw branch of the checked response is supported by the generic
interpreter, with its exact probability and ACTUAL successor registers. -/
theorem response_all_branches (m : RawLaneModel) (rid : RouteId) (history : List KState)
    (path : List EventId) (hp : phase2Check m rid = true)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,path))
    (branch : Ambient × Nat)
    (hb : branch ∈ (arrivalInputs m).base.base.rows (history.getLastD .p0w0)
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0))) :
    let received : Run6 := ⟨.inK (history.getLastD .p0w0),0,0,(history,path),
      (arrivalInputs m).base.receiver.funded⟩
    StrategyGame.PositiveSupport (HistoricalAcquisition.rows POS04HistoricalAcquisition.raw (image m.assignment))
      (POS04RegisterDynamics.encode received) .nominal
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) branch.1 ∧
    HistoricalAcquisition.update POS04HistoricalAcquisition.raw (image m.assignment)
      (ready_of_check m rid hp) (POS04RegisterDynamics.encode received) .nominal
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) branch.1 =
    POS04RegisterDynamics.encode (actualUpdate6 (arrivalInputs m) received
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) branch.1) := by
  constructor
  · refine ⟨(branch.2 : Rat)/4,?_,ScaledRows.positive 4 branch.2 (by decide)
      ((POS04HistoricalAutonomy.phase2_target_facts m rid history path hp ht).2.2.2 branch hb).1⟩
    rw [response_rows m rid history path hp ht]
    exact List.mem_map.mpr ⟨branch,hb,rfl⟩
  · exact POS04HistoricalAcquisition.updater_computed _ _ _ .nominal _ _

/-- Nonempty baseline protocol instance: every raw route passes. -/
theorem baseline_all_routes : AllRoutes (image baseline.assignment) :=
  protocol_checks_all_routes baseline POS04ExactGames.positive_games.2.1

/-- A cell deletion rejects before the slice's assignment can be decoded.
This covers each of the twelve fields, including writers and source rows. -/
theorem missing_cell_all_routes_rejected (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) (hm : image m.assignment k = none) :
    ¬ AllRoutes (image m.assignment) := by
  intro h
  have bad := missing_rejected (image m.assignment) .a k hk hm
  have good := h .a (by decide)
  rw [bad] at good
  contradiction

/-- Exact support characterization: no target branch, including an exit,
is silently discarded by the historical interpreter. -/
theorem response_support_iff (m : RawLaneModel) (rid : RouteId) (history : List KState)
    (path : List EventId) (hp : phase2Check m rid = true)
    (ht : routeTuple (arrivalInputs m).base rid = some (history,path)) (o : Ambient) :
    let received : Run6 := ⟨.inK (history.getLastD .p0w0),0,0,(history,path),
      (arrivalInputs m).base.receiver.funded⟩
    StrategyGame.PositiveSupport (HistoricalAcquisition.rows POS04HistoricalAcquisition.raw (image m.assignment))
      (POS04RegisterDynamics.encode received) .nominal
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) o ↔
    ∃ numerator, (o,numerator) ∈ (arrivalInputs m).base.base.rows (history.getLastD .p0w0)
      ((arrivalInputs m).base.base.policy (history.getLastD .p0w0)) ∧ numerator > 0 := by
  dsimp only
  constructor
  · rintro ⟨w,hw,_⟩
    rw [response_rows m rid history path hp ht] at hw
    obtain ⟨branch,hb,he⟩ := List.mem_map.mp hw
    have ho : branch.1 = o := congrArg Prod.fst he
    exact ⟨branch.2,by simpa only [← ho] using hb,
      ((POS04HistoricalAutonomy.phase2_target_facts m rid history path hp ht).2.2.2 branch hb).1⟩
  · rintro ⟨n,hn,_⟩
    exact (response_all_branches m rid history path hp ht (o,n) hn).1

/-- Completeness is about the actual declared dependency set, not a larger
source-run domain. These three cells are unconsumed by this protocol. -/
theorem no_source_ticks : Cell.ticks .source ∉ (check .a).dependencies := by rw [check_dependencies]; decide
theorem no_source_resources : Cell.resources .source ∉ (check .a).dependencies := by rw [check_dependencies]; decide
theorem no_hazards : Cell.hazards ∉ (check .a).dependencies := by rw [check_dependencies]; decide

theorem replacement_unchanged (a : CSTTT.POS04.Assigned.Assignment) (rid : RouteId)
    (k : Cell) (v : Option (Value k)) (hk : k ∉ phase2Dependencies) :
    (check rid).read (Assigned.put a k v) = (check rid).read a := by
  apply check_locality
  intro j hj
  exact Assigned.put_other a k j v (fun h => hk (h ▸ hj))

/-- Duplicate-ID activation remains existential over all raw records. -/
theorem duplicate_event_regression :
    AllRoutes (image POS04HistoricalDuplicateEvents.diagnostic.assignment) :=
  protocol_checks_all_routes _ ((POS04OperationalGame.game_iff_ao _).mpr
    POS04HistoricalDuplicateEvents.legacy_ao_accepts).1

theorem missing_past_ticks_regression :
    AllRoutes (image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment) :=
  protocol_checks_all_routes _ POS04RuntimeEquivalenceBoundary.legacy_operational_game_accepts.1

theorem source_recharge_regression :
    AllRoutes (image POS04ReceiverResetProjection.sourceRechargeUnavailable.assignment) :=
  protocol_checks_all_routes _ POS04ReceiverResetProjection.diagnostic_legacy_operational_game_accepts.1

theorem package_control_regression : AllRoutes (image packageDeletion.assignment) :=
  protocol_checks_all_routes _ ((POS04OperationalGame.game_iff_ao _).mpr package_deletion_AO).1

theorem lineage_control_regression : AllRoutes (image lineageDeletion.assignment) :=
  protocol_checks_all_routes _ ((POS04OperationalGame.game_iff_ao _).mpr lineage_deletion_AO).1

/-- Independent activation rejection; it does not rely on a corridor theorem. -/
theorem source_absent_rejected (m : RawLaneModel)
    (hs : (arrivalInputs m).base.receiver.sourcePresent = false) :
    ¬ AllRoutes (image m.assignment) := by
  intro h
  have hp := (check_iff m .a).mp (h .a (by decide))
  rw [no_source_rejects_phase2 m hs .a] at hp
  contradiction

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalProtocol
