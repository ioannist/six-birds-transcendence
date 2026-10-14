import CSTTT.Targets.GenericHandoff.POS04HistoricalRuntime
import CSTTT.Targets.GenericHandoff.POS04MultiResourceGames

/-! Non-vacuous historical runtime instance and finite-factor TTH-05 lift.
The positive invariant and all response branches are derived from the raw
receiver and exact target updater. This is not whole arbitrary-partial game
equivalence or the final shared lineage/RawHandoff assembly. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalRuntimeInstance
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RouteExecution POS04ResourceRuntime POS04HistoricalRuntime
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

abbrev M := POS04HistoricalRuntime.model (protocol baseline)
abbrev CA := POS04HistoricalRuntime.canonical_acquisition_ready (protocol baseline)
abbrev HR := POS04HistoricalRuntime.canonical_resource_ready

theorem target_canonical : HistoricalPackageRuntime.target M canonical = canonical :=
  (POS04HistoricalRuntime.target_eq _ _).trans image_canonical

theorem canonical_arrival_unique (rid : RouteId) (received : Registers Unit FrameValue)
    (ha : HistoricalAcquisition.Arrival POS04ExecutionFrontier.schema
      (HistoricalPackageRuntime.acquisition M) canonical CA rid received) :
    received = frame .target (arrivalFor rid) := by
  rcases ha with ⟨hs,sr,sp,coord,tr,tp,rs,ev,real,rec,first,rest,
    hh,hr,hsp,hcoord,htr,htp,hrs,hev,hreal,hrec,hrid,hhid,hlist,hss,hts,hpath,hact,hreset⟩
  have hehs : hs = POS04ExecutionFrontier.historyPath sourceHistory routes :=
    Option.some.inj hh.symm
  have hers : rs = POS04ExecutionFrontier.routeView.project routes :=
    Option.some.inj hrs.symm
  have hep : sp = (fun (_ : RouteId) (_ : Nat) => canonicalAction) :=
    Option.some.inj hsp.symm
  subst hs; subst rs; subst sp
  have hhist : sourceHistory (routeOf rid).sourceHistory = first::rest := by
    cases rid <;> exact hlist
  have hfirst : first = match rid with | .a => .p1w0 | .b => .p1w1 := by
    cases rid <;> exact (List.cons.inj hhist).1.symm
  have hrest : rest = match rid with | .a => [.p2w1,.p1w0] | .b => [.p5w0,.p1w0] := by
    cases rid <;> exact (List.cons.inj hhist).2.symm
  subst received
  rw [POS04HistoricalRuntime.reset_link _ _ CA POS04HistoricalAcquisition.canonical_ready,
    POS04HistoricalAcquisition.reset_computed _ _ _ receiver rfl,
    POS04RegisterDynamics.decode_encode]
  cases rid <;> simp only [hfirst,hrest] <;> rfl

theorem raw_entries_inside (r : Registers Unit FrameValue)
    (he : HistoricalAcquisition.Entry POS04ExecutionFrontier.schema (HistoricalPackageRuntime.acquisition M) canonical CA r) :
    POS04MultiResourceGames.invariant r := by
  change HistoricalAcquisition.Entry POS04ExecutionFrontier.schema
    (HistoricalPackageRuntime.acquisition M) canonical CA r at he
  rcases he with ⟨_,rid,received,rs,da,o,ha,hr,hresp,hd,hact,hn,hp,hup⟩
  rw [canonical_arrival_unique rid received ha] at hresp hp hup
  have hrs : rs = POS04ExecutionFrontier.routeView.project routes := Option.some.inj hr.symm
  subst rs
  have hda : da = (LaneDisturbance.nominal,Action.cw) := by
    cases rid <;> exact (Option.some.inj hresp).symm
  subst da
  unfold StrategyGame.PositiveSupport at hp
  dsimp only at hp hup
  rw [POS04HistoricalRuntime.rows_eq _ _ CA] at hp
  have row : actualRows6 (runInputs6 canonical .target) (arrivalFor rid) .cw = [(.inK .p2w1,1)] := by
    cases rid <;> decide +kernel
  rw [row] at hp
  obtain ⟨weight,hm,_⟩ := hp
  have hout := congrArg Prod.fst (List.mem_singleton.mp hm)
  dsimp only at hout
  subst o
  rw [POS04HistoricalRuntime.update_eq _ _ CA] at hup
  exact ⟨.p2w1,rid,1,1,hup⟩

def HA : HistoricalPackageRuntime.AcquisitionReady M canonical := by
  change HistoricalAcquisition.Ready (HistoricalPackageRuntime.acquisition M)
    (HistoricalPackageRuntime.target M canonical)
  rw [target_canonical]
  exact CA

theorem entries_inside (r : Registers Unit FrameValue)
    (he : HistoricalPackageRuntime.Entries M canonical HA r) : POS04MultiResourceGames.invariant r := by
  apply raw_entries_inside r
  simpa only [HistoricalPackageRuntime.Entries,target_canonical] using he

theorem entries_nonempty : ∃ r, HistoricalPackageRuntime.Entries M canonical HA r := by
  refine ⟨frame .target (resultFor .a),?_⟩
  simpa only [HistoricalPackageRuntime.Entries,target_canonical] using
    POS04HistoricalRuntime.canonical_entry (protocol baseline) .a


/-- The resource game and historical acquisition share the SAME execution,
so these are updater/row equations, not assumptions of a safe quotient. -/
theorem actual_update (x : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    ResourceRuntime.update (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M canonical)
      HR (frame .target x) d act o =
      frame .target (actualUpdate6 (runInputs6 canonical .target) x act o) := by
  simpa only [ResourceRuntime.update,HistoricalAcquisition.update,target_canonical] using
    POS04HistoricalRuntime.update_eq (protocol baseline) canonical CA x d act o

theorem actual_rows (x : Run6) (d : LaneDisturbance) (act : Action) :
    ResourceRuntime.rows (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M canonical)
      (frame .target x) d act = actualRows6 (runInputs6 canonical .target) x act := by
  simpa only [ResourceRuntime.rows,HistoricalAcquisition.rows,target_canonical] using
    POS04HistoricalRuntime.rows_eq (protocol baseline) canonical CA x d act

theorem package_inside (r : Registers Unit FrameValue) (hi : POS04MultiResourceGames.invariant r) :
    HistoricalPackageRuntime.PackageAt M canonical r := by
  obtain ⟨s,rid,n,ticks,rfl⟩ := hi
  refine ⟨(POS04HistoricalRuntime.package_readout_iff baseline).mpr package_lane_positive,?_,?_⟩
  · refine ⟨s,?_,rfl⟩
    change s ∈ kernel
    cases s <;> decide
  · have he := POS04HistoricalRuntime.run_assignment_eq baseline (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩)
    rw [baseline_withdrawn] at he
    change (POS04Dispatcher.package .target).accept (HistoricalPackageRuntime.runAssignment (POS04HistoricalRuntime.model (protocol baseline)) baseline.assignment _)
    rw [he]
    exact POS04Dispatcher.canonical_accept .target

theorem resource_inside (r : Registers Unit FrameValue) (hi : POS04MultiResourceGames.invariant r) :
    ResourceRuntime.ResourceClosed M.resourceSchema
      (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M canonical) r := by
  obtain ⟨s,rid,n,ticks,rfl⟩ := hi
  rw [target_canonical]
  refine ⟨(fun res => match res with | .recharge => ⟨some (tagCarrierId .target),true,1⟩ | _ => ⟨none,false,0⟩),
    [.recharge],withdrawal (protocol baseline),(by apply congrArg some; funext res; cases res <;> rfl),rfl,rfl,rfl,?_,by simp,by decide,?_,?_⟩
  · cases rid <;> rfl
  · intro res hr
    have heq := List.mem_singleton.mp hr
    subst res
    exact ⟨rfl,rfl,by decide⟩
  · intro res hr
    cases res with
    | recharge => simp [withdrawal,protocol,baseline] at hr
    | removed role => rfl

theorem legal (r : Registers Unit FrameValue) (hi : POS04MultiResourceGames.invariant r) (d : LaneDisturbance) (act : Action) :
    ResourceRuntime.Legal M.resourceSchema
      (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M canonical) r d act := by
  obtain ⟨s,rid,n,ticks,rfl⟩ := hi
  rw [target_canonical]
  refine ⟨?_,?_,(fun res => match res with | .recharge => ⟨some (tagCarrierId .target),true,1⟩ | _ => ⟨none,false,0⟩),
    [.recharge],⟨tagCarrierId .target,[.recharge],(fun res => match res with | .recharge => 1 | _ => 0),
      (fun res => match res with | .recharge => 1 | _ => 0)⟩,
    withdrawal (protocol baseline),(by apply congrArg some; funext res; cases res <;> rfl),rfl,rfl,rfl,rfl,by simp,by simp,by decide,by decide,?_⟩
  · cases d; decide
  · cases act <;> decide
  · intro res hr
    have heq := List.mem_singleton.mp hr
    subst res
    exact ⟨rfl,rfl,by decide,by decide⟩

theorem row_exact (s : KState) (rid : RouteId) (n ticks : Nat) (act : Action) (d : LaneDisturbance) :
    ResourceRuntime.rows (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M canonical)
      (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩) d act =
      (actionRow .target s act).map (fun e => (e.1,(e.2 : Rat)/4)) := by
  rw [actual_rows]
  rfl

theorem policy_normalized (s : KState) (rid : RouteId) (n ticks : Nat) (d : LaneDisturbance) :
    StrategyGame.Normalized (ResourceRuntime.rows (HistoricalPackageRuntime.resources M)
      (HistoricalPackageRuntime.target M canonical)) (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩)
        d (canonicalAction s) := by
  unfold StrategyGame.Normalized StrategyGame.PositiveSupport
  rw [row_exact]
  let row := (actionRow .target s (canonicalAction s)).map (fun e => (e.1,(e.2 : Rat)/4))
  have pos : row.all (fun e => decide (0 < e.2)) = true := by cases s <;> decide +kernel
  have sum : (row.map Prod.snd).sum = 1 := by cases s <;> decide +kernel
  have nonempty : row ≠ [] := by cases s <;> decide +kernel
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ nonempty
  have hp := of_decide_eq_true (List.all_eq_true.mp pos e he)
  refine ⟨?_,sum,e.1,e.2,he,hp⟩
  intro e he
  exact Rat.le_of_lt (of_decide_eq_true (List.all_eq_true.mp pos e he))

theorem policy_supported (s : KState) (rid : RouteId) (n ticks : Nat) (d : LaneDisturbance) (o : Ambient)
    (hp : StrategyGame.PositiveSupport (ResourceRuntime.rows (HistoricalPackageRuntime.resources M)
      (HistoricalPackageRuntime.target M canonical)) (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩)
        d (canonicalAction s) o) : ∃ t, o = Ambient.inK t := by
  unfold StrategyGame.PositiveSupport at hp
  rw [row_exact] at hp
  obtain ⟨w,hw,_⟩ := hp
  obtain ⟨e,he,heq⟩ := List.mem_map.mp hw
  have hall : (actionRow .target s (canonicalAction s)).all (fun e => match e.1 with
    | .inK _ => true | _ => false) = true := by cases s <;> decide +kernel
  have hok := List.all_eq_true.mp hall e he
  have hout := congrArg Prod.fst heq
  cases hx : e.1 with
  | inK t => exact ⟨t,hout.symm.trans hx⟩
  | p2w0 => simp [hx] at hok
  | p5w1 => simp [hx] at hok

theorem policy_update (s t : KState) (rid : RouteId) (n ticks : Nat) (d : LaneDisturbance) :
    ResourceRuntime.update (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M canonical)
      HR (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩) d (canonicalAction s) (.inK t) =
      frame .target ⟨.inK t,n+1,ticks+1,routeRegister rid,true⟩ := by
  rw [actual_update]
  rfl

theorem policy_step (s t : KState) (rid : RouteId) (n ticks : Nat) (d : LaneDisturbance) :
    ResourceRuntime.StepLaw M.resourceSchema
      (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M canonical) HR
      (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩) d (canonicalAction s) (.inK t) := by
  unfold ResourceRuntime.StepLaw
  rw [policy_update]
  refine ⟨resource_inside _ ⟨t,rid,n+1,ticks+1,rfl⟩,
    (fun res => match res with | .recharge => ⟨some (tagCarrierId .target),true,1⟩ | _ => ⟨none,false,0⟩),
    (fun res => match res with | .recharge => ⟨some (tagCarrierId .target),true,1⟩ | _ => ⟨none,false,0⟩),
    ⟨tagCarrierId .target,[.recharge],(fun res => match res with | .recharge => 1 | _ => 0),
      (fun res => match res with | .recharge => 1 | _ => 0)⟩,
    ⟨1,1,1,1⟩,n,ticks,n,n,?_,?_,?_,?_,by decide,by decide,by decide,by decide,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [target_canonical]; apply congrArg some; funext res; cases res <;> rfl
  · rw [target_canonical]; apply congrArg some; funext res; cases res <;> rfl
  · rw [target_canonical]; rfl
  · rw [target_canonical]; rfl
  · intro res hr
    have hres := List.mem_singleton.mp hr
    subst res
    rfl
  all_goals try (rw [target_canonical]; rfl)
  all_goals rw [target_canonical]; cases rid <;> rfl

/-- The POS04MultiResourceGames.invariant and causal responses are constructed; the game readout is
derived by the generic strategy induction, not stored in this certificate. -/
theorem positive_certificate : Nonempty (HistoricalPackageRuntime.FullCertificate M canonical HA HR) := by
  refine ⟨{ inside := POS04MultiResourceGames.invariant
            withdrawn := canonical_withdrawal
            entriesNonempty := entries_nonempty
            entriesInside := entries_inside
            packageInside := package_inside
            resourcesInside := resource_inside
            response := ?_ }⟩
  intro r hr d
  obtain ⟨s,rid,n,ticks,rfl⟩ := hr
  refine ⟨canonicalAction s,legal _ ⟨s,rid,n,ticks,rfl⟩ d _,policy_normalized s rid n ticks d,?_⟩
  intro o hp
  obtain ⟨t,rfl⟩ := policy_supported s rid n ticks d o hp
  exact ⟨by rw [policy_update]; exact ⟨t,rid,n+1,ticks+1,rfl⟩,policy_step s t rid n ticks d⟩

theorem positive_full : HistoricalPackageRuntime.PostWithdrawalFullAutonomy M canonical :=
  HistoricalPackageRuntime.full_soundness M canonical ⟨HA,HR,positive_certificate⟩

theorem positive_operational : HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy M canonical :=
  HistoricalPackageRuntime.full_implies_operational M canonical positive_full



/-- A genuine historical entry and full game instantiate the generic transport.
The finite lift is already proved on every relevant run, not sampled at entry. -/
theorem positive_each_entry_exact :
    ∃ cert : HistoricalPackageRuntime.FullCertificate M canonical HA HR,
      ∀ entry, HistoricalPackageRuntime.Entries M canonical HA entry →
        Nonempty (CSTTT.AutonomyTheory.ExactAutonomyCertificate (GameAutonomyTransport.projectedData
          (HistoricalFiniteAutonomy.factor M (POS04HistoricalRuntime.factorFrame (protocol baseline))
            canonical POS04HistoricalRuntime.canonical_checked)
          cert (HistoricalFiniteAutonomy.project M (POS04HistoricalRuntime.factorFrame (protocol baseline))
            canonical POS04HistoricalRuntime.canonical_checked) entry)) :=
  HistoricalFiniteAutonomy.each_entry_exact _ _ _ POS04HistoricalRuntime.canonical_checked
    POS04HistoricalRuntime.positive_lift HA (by
      obtain ⟨cert⟩ := positive_certificate
      exact StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert)

theorem positive_each_entry_words :
    ∃ cert : HistoricalPackageRuntime.FullCertificate M canonical HA HR,
      ∀ entry, HistoricalPackageRuntime.Entries M canonical HA entry → ∀ word : List LaneDisturbance,
        ∃ final, CSTTT.AutonomyTheory.ControlledRun (GameAutonomyTransport.projectedData
          (HistoricalFiniteAutonomy.factor M (POS04HistoricalRuntime.factorFrame (protocol baseline))
            canonical POS04HistoricalRuntime.canonical_checked)
          cert (HistoricalFiniteAutonomy.project M (POS04HistoricalRuntime.factorFrame (protocol baseline))
            canonical POS04HistoricalRuntime.canonical_checked) entry)
          (HistoricalFiniteAutonomy.project M (POS04HistoricalRuntime.factorFrame (protocol baseline))
            canonical POS04HistoricalRuntime.canonical_checked entry) word final ∧
          HistoricalFiniteAutonomy.FactorPackage M (POS04HistoricalRuntime.factorFrame (protocol baseline)) canonical final :=
  HistoricalFiniteAutonomy.each_entry_words _ _ _ POS04HistoricalRuntime.canonical_checked
    POS04HistoricalRuntime.positive_lift HA (by
      obtain ⟨cert⟩ := positive_certificate
      exact StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert)


/-- Duplicate-ID all-record activation transfers to the whole historical
acquisition runtime; a first-record activation resolver would fail here. -/
theorem duplicate_event_entry (rid : RouteId) :
    ∃ ha : HistoricalPackageRuntime.AcquisitionReady
        (POS04HistoricalRuntime.model (protocol POS04HistoricalDuplicateEvents.diagnostic))
        POS04HistoricalDuplicateEvents.diagnostic.assignment,
      HistoricalPackageRuntime.Entries
        (POS04HistoricalRuntime.model (protocol POS04HistoricalDuplicateEvents.diagnostic))
        POS04HistoricalDuplicateEvents.diagnostic.assignment ha (frame .target (resultFor rid)) := by
  have hp := ((POS04OperationalGame.game_iff_ao _).mpr POS04HistoricalDuplicateEvents.legacy_ao_accepts).1
  let ha := POS04HistoricalRuntime.acquisition_ready_of_protocol _ hp
  refine ⟨ha,?_⟩
  have he := POS04HistoricalRuntime.entry_from_registers
    (protocol POS04HistoricalDuplicateEvents.diagnostic) POS04HistoricalDuplicateEvents.assignment
    (by simpa only [HistoricalPackageRuntime.AcquisitionReady,POS04HistoricalRuntime.target_eq,POS04HistoricalDuplicateEvents.staged_assignment] using ha)
    POS04HistoricalDuplicateEvents.ready _ (POS04HistoricalDuplicateEvents.duplicate_entry rid)
  simpa only [HistoricalPackageRuntime.Entries,POS04HistoricalRuntime.target_eq,
    POS04HistoricalDuplicateEvents.staged_assignment,POS04RegisterDynamics.decode_encode] using he

theorem missing_past_ticks_staged : image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment =
    Assigned.put canonical (.ticks .source) none := by
  funext k
  cases k <;> try rfl
  all_goals rename_i tag; cases tag <;> first | rfl | exact congrFun image_canonical _

theorem missing_past_ticks_entry (rid : RouteId) :
    ∃ ha : HistoricalPackageRuntime.AcquisitionReady
        (POS04HistoricalRuntime.model (protocol POS04RuntimeEquivalenceBoundary.missingPastTicks))
        POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment,
      HistoricalPackageRuntime.Entries
        (POS04HistoricalRuntime.model (protocol POS04RuntimeEquivalenceBoundary.missingPastTicks))
        POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment ha (frame .target (resultFor rid)) := by
  have hp := POS04RuntimeEquivalenceBoundary.legacy_operational_game_accepts.1
  let ha := POS04HistoricalRuntime.acquisition_ready_of_protocol _ hp
  refine ⟨ha,?_⟩
  have he := POS04HistoricalRuntime.entry_from_registers
    (protocol POS04RuntimeEquivalenceBoundary.missingPastTicks)
    (Assigned.put canonical (.ticks .source) none)
    (by simpa only [HistoricalPackageRuntime.AcquisitionReady,POS04HistoricalRuntime.target_eq,missing_past_ticks_staged] using ha)
    (POS04HistoricalAcquisition.replacement_ready canonical POS04HistoricalAcquisition.canonical_ready _
      POS04HistoricalAcquisition.no_source_ticks none) _ (POS04HistoricalAcquisition.missing_past_ticks_entry rid)
  simpa only [HistoricalPackageRuntime.Entries,POS04HistoricalRuntime.target_eq,
    missing_past_ticks_staged,POS04RegisterDynamics.decode_encode] using he

/-- Deleting the staged source rows rejects both games before any row default
can validate the recorded acquisition past. Only the assignment cell changes. -/
theorem missing_source_rows_no_games :
    let m : RawLaneModel := {baseline with assignment := Assigned.put canonical (.rows .target) none}
    ¬ HistoricalPackageRuntime.PostWithdrawalFullAutonomy (POS04HistoricalRuntime.model (protocol m)) m.assignment ∧
      ¬ HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy (POS04HistoricalRuntime.model (protocol m)) m.assignment := by
  dsimp only
  apply POS04HistoricalRuntime.missing_acquisition_no_games _ (.rows .source)
  · decide +kernel
  · exact image_delete_cell canonical (.rows .source)

/-- Retention deletion is a direct failure of the named GAME readouts, rather
than just failure of a sufficient finite constructor. -/
theorem withdrawal_no_games :
    ¬ HistoricalPackageRuntime.PostWithdrawalFullAutonomy
        (POS04HistoricalRuntime.model (protocol withdrawalDeletion)) withdrawalDeletion.assignment ∧
      ¬ HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy
        (POS04HistoricalRuntime.model (protocol withdrawalDeletion)) withdrawalDeletion.assignment :=
  POS04HistoricalRuntime.withdrawal_no_games withdrawalDeletion rfl

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalRuntimeInstance


