import CSTTT.Targets.GenericHandoff.POS04RawFiniteAutonomy

/-! Nonempty POS-04 F/O games on the shared multi-resource runtime. The
invariant retains actual factor states and route tuples; the canonical response
uses its declared policy. Every positive-support branch is retained, including
branches outside the predictive quotient. Six acquisition resources are absent
and target recharge is the only post-withdrawal maintenance resource.

This is the positive runtime constructor. It does not yet prove arbitrary-
partial equivalence with G6c AF/AO, or the final generic lineage/RawHandoff.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04MultiResourceGames
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RouteExecution POS04ResourceRuntime POS04RawFiniteAutonomy
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

abbrev M := model (protocol baseline)
abbrev HR := canonical_resource_ready
def HA : PackageRuntime.AcquisitionReady M canonical := by
  change AcquisitionExecution.Ready acquisition (PackageRuntime.target M canonical)
  rw [target_eq,image_canonical]
  exact POS04RouteExecution.ready canonical (canonical_complete _)

def invariant (r : Registers Unit FrameValue) : Prop :=
  ∃ s : KState, ∃ rid : RouteId, ∃ n ticks : Nat,
    r = frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩

theorem target_canonical : PackageRuntime.target M canonical = canonical :=
  (target_eq _ _).trans image_canonical

theorem actual_update (x : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    ResourceRuntime.update (RuntimeComponents.resources M.runtime) (PackageRuntime.target M canonical)
      HR (frame .target x) d act o =
      frame .target (actualUpdate6 (runInputs6 canonical .target) x act o) := by
  have he := POS04RouteExecution.update_eq canonical (canonical_complete _ ) .target x d act o
  simpa only [ResourceRuntime.update,AcquisitionExecution.update,target_canonical] using he

theorem actual_rows (x : Run6) (d : LaneDisturbance) (act : Action) :
    ResourceRuntime.rows (RuntimeComponents.resources M.runtime) (PackageRuntime.target M canonical)
      (frame .target x) d act = actualRows6 (runInputs6 canonical .target) x act := by
  have he := POS04RouteExecution.rows_eq canonical (canonical_complete _) .target x d act
  simpa only [ResourceRuntime.rows,AcquisitionExecution.rows,target_canonical] using he

theorem entries_inside (r : Registers Unit FrameValue) (he : PackageRuntime.Entries M canonical HA r) :
    invariant r := by
  change AcquisitionExecution.Entry POS04ExecutionFrontier.schema acquisition
    (PackageRuntime.target M canonical) HA r at he
  have he' : AcquisitionExecution.Entry POS04ExecutionFrontier.schema acquisition canonical
      (POS04RouteExecution.ready canonical (canonical_complete _)) r := by
    simpa only [target_canonical] using he
  obtain ⟨rid,hresult⟩ := (RouteComponent.result_entry_iff _ routeRaw canonical _ r).mpr he'
  rcases hresult with ⟨_,arrived,rs,da,o,ha,hr,hresp,_,_,_,hp,hu⟩
  rw [canonical_arrival_unique rid arrived ha] at hresp hp hu
  have hda : da = (LaneDisturbance.nominal,Action.cw) := by
    have hrq := Option.some.inj (hr.symm.trans canonical_routes_read)
    subst rs
    cases rid <;> exact (Option.some.inj hresp).symm
  subst da
  dsimp only [routeRaw] at hp hu
  unfold StrategyGame.PositiveSupport at hp
  rw [POS04RouteExecution.rows_eq canonical (canonical_complete _)] at hp
  have hrow : actualRows6 (runInputs6 canonical .target) (arrivalFor rid) .cw = [(.inK .p2w1,1)] := by
    cases rid <;> decide +kernel
  rw [hrow] at hp
  obtain ⟨w,hm,_⟩ := hp
  have ho := congrArg Prod.fst (List.mem_singleton.mp hm)
  dsimp only at ho
  subst o
  rw [POS04RouteExecution.update_eq canonical (canonical_complete _)] at hu
  exact ⟨.p2w1,rid,1,1,hu⟩

theorem entries_nonempty : ∃ r, PackageRuntime.Entries M canonical HA r := by
  refine ⟨frame .target (resultFor .a),?_⟩
  have he := (RouteComponent.result_entry_iff _ routeRaw canonical _ _).mp ⟨.a,canonical_result .a⟩
  change AcquisitionExecution.Entry POS04ExecutionFrontier.schema acquisition
    (PackageRuntime.target M canonical) HA _
  simpa only [target_canonical] using he

theorem package_inside (r : Registers Unit FrameValue) (hi : invariant r) :
    PackageRuntime.PackageAt M canonical r := by
  obtain ⟨s,rid,n,ticks,rfl⟩ := hi
  refine ⟨(package_readout_iff baseline).mpr package_lane_positive,?_,?_⟩
  · refine ⟨s,?_,rfl⟩
    change s ∈ kernel
    cases s <;> decide
  · have he := run_assignment_eq baseline (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩)
    rw [baseline_withdrawn] at he
    change (POS04Dispatcher.package .target).accept (PackageRuntime.runAssignment (model (protocol baseline)) baseline.assignment _)
    rw [he]
    exact POS04Dispatcher.canonical_accept .target

theorem resource_inside (r : Registers Unit FrameValue) (hi : invariant r) :
    ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema M.runtimeSchema)
      (RuntimeComponents.resources M.runtime) (PackageRuntime.target M canonical) r := by
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

theorem legal (r : Registers Unit FrameValue) (hi : invariant r) (d : LaneDisturbance) (act : Action) :
    ResourceRuntime.Legal (RuntimeComponents.resourceSchema M.runtimeSchema)
      (RuntimeComponents.resources M.runtime) (PackageRuntime.target M canonical) r d act := by
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
    ResourceRuntime.rows (RuntimeComponents.resources M.runtime) (PackageRuntime.target M canonical)
      (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩) d act =
      (actionRow .target s act).map (fun e => (e.1,(e.2 : Rat)/4)) := by
  rw [actual_rows]
  rfl

theorem policy_normalized (s : KState) (rid : RouteId) (n ticks : Nat) (d : LaneDisturbance) :
    StrategyGame.Normalized (ResourceRuntime.rows (RuntimeComponents.resources M.runtime)
      (PackageRuntime.target M canonical)) (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩)
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
    (hp : StrategyGame.PositiveSupport (ResourceRuntime.rows (RuntimeComponents.resources M.runtime)
      (PackageRuntime.target M canonical)) (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩)
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
    ResourceRuntime.update (RuntimeComponents.resources M.runtime) (PackageRuntime.target M canonical)
      HR (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩) d (canonicalAction s) (.inK t) =
      frame .target ⟨.inK t,n+1,ticks+1,routeRegister rid,true⟩ := by
  rw [actual_update]
  rfl

theorem policy_step (s t : KState) (rid : RouteId) (n ticks : Nat) (d : LaneDisturbance) :
    ResourceRuntime.StepLaw (RuntimeComponents.resourceSchema M.runtimeSchema)
      (RuntimeComponents.resources M.runtime) (PackageRuntime.target M canonical) HR
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

/-- The invariant and causal responses are constructed; the game readout is
derived by the generic strategy induction, not stored in this certificate. -/
theorem positive_certificate : Nonempty (PackageRuntime.FullCertificate M canonical HA HR) := by
  refine ⟨{ inside := invariant
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

theorem positive_full : PackageRuntime.PostWithdrawalFullAutonomy M canonical :=
  PackageRuntime.full_soundness M canonical ⟨HA,HR,positive_certificate⟩

theorem positive_operational : PackageRuntime.PostWithdrawalOperationalAutonomy M canonical :=
  PackageRuntime.full_autonomy_implies_operational M canonical positive_full

theorem positive_each_entry_exact :
    ∃ cert : PackageRuntime.FullCertificate M canonical HA HR,
      ∀ entry, PackageRuntime.Entries M canonical HA entry →
        Nonempty (CSTTT.AutonomyTheory.ExactAutonomyCertificate (GameAutonomyTransport.projectedData
          (RawFiniteAutonomy.factor M (factorFrame (protocol baseline)) canonical canonical_checked)
          cert (RawFiniteAutonomy.project M (factorFrame (protocol baseline)) canonical canonical_checked) entry)) :=
  RawFiniteAutonomy.each_entry_exact _ _ _ canonical_checked positive_lift HA
    (by
      obtain ⟨cert⟩ := positive_certificate
      exact StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert)

theorem positive_each_entry_words :
    ∃ cert : PackageRuntime.FullCertificate M canonical HA HR,
      ∀ entry, PackageRuntime.Entries M canonical HA entry → ∀ word : List LaneDisturbance,
        ∃ y, CSTTT.AutonomyTheory.ControlledRun (GameAutonomyTransport.projectedData
          (RawFiniteAutonomy.factor M (factorFrame (protocol baseline)) canonical canonical_checked)
          cert (RawFiniteAutonomy.project M (factorFrame (protocol baseline)) canonical canonical_checked) entry)
          (RawFiniteAutonomy.project M (factorFrame (protocol baseline)) canonical canonical_checked entry) word y ∧
          RawFiniteAutonomy.FactorPackage M (factorFrame (protocol baseline)) canonical y :=
  RawFiniteAutonomy.each_entry_words _ _ _ canonical_checked positive_lift HA
    (by
      obtain ⟨cert⟩ := positive_certificate
      exact StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert)

/-- Actual removal of the required recharge rejects resource safety at EVERY
run, hence both games. A failed sufficient check is not used as a negative
semantic readout. -/
theorem no_recharge_resources (m : RawLaneModel)
    (empty : m.retained = []) (r : Registers Unit FrameValue) :
    ¬ ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema (model (protocol m)).runtimeSchema)
      (RuntimeComponents.resources (model (protocol m)).runtime)
      (PackageRuntime.target (model (protocol m)) m.assignment) r := by
  rintro ⟨ac,req,w,ha,hreq,hw,_,_,_,hsub,_⟩
  change some ([Resource.recharge] : List Resource) = some req at hreq
  have hreq' := Option.some.inj hreq
  subst req
  rw [target_eq] at hw
  change (image m.assignment Cell.maintenance).map (fun _ => withdrawal (protocol m)) = some w at hw
  cases hv : image m.assignment Cell.maintenance with
  | none => simp [hv] at hw
  | some val =>
    rw [hv] at hw
    have heq := Option.some.inj hw
    subst w
    have impossible := hsub (by simp : Resource.recharge ∈ [Resource.recharge])
    simp [withdrawal,protocol,empty] at impossible

theorem no_recharge_no_games (m : RawLaneModel) (empty : m.retained = []) :
    ¬ PackageRuntime.PostWithdrawalFullAutonomy (model (protocol m)) m.assignment ∧
      ¬ PackageRuntime.PostWithdrawalOperationalAutonomy (model (protocol m)) m.assignment := by
  constructor
  · rintro ⟨ha,hr,hw,⟨entry,he⟩,strategy,hs⟩
    exact no_recharge_resources m empty entry (hs entry he entry [] StrategyGame.Play.initial).2.1
  · rintro ⟨ha,hr,hw,⟨entry,he⟩,strategy,hs⟩
    exact no_recharge_resources m empty entry (hs entry he entry [] StrategyGame.Play.initial).2.1

theorem withdrawal_control :
    ¬ PackageRuntime.PostWithdrawalFullAutonomy (model (protocol withdrawalDeletion)) canonical ∧
      ¬ PackageRuntime.PostWithdrawalOperationalAutonomy (model (protocol withdrawalDeletion)) canonical :=
  no_recharge_no_games withdrawalDeletion rfl

theorem postwithdrawal_source_present_resources (m : RawLaneModel)
    (present : m.sourcePresentAfterWithdrawal = true) (r : Registers Unit FrameValue) :
    ¬ ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema (model (protocol m)).runtimeSchema)
      (RuntimeComponents.resources (model (protocol m)).runtime)
      (PackageRuntime.target (model (protocol m)) m.assignment) r := by
  rintro ⟨_,_,_,_,_,_,hs,_⟩
  change some m.sourcePresentAfterWithdrawal = some false at hs
  rw [present] at hs
  contradiction

theorem source_present_no_games (m : RawLaneModel)
    (present : m.sourcePresentAfterWithdrawal = true) :
    ¬ PackageRuntime.PostWithdrawalFullAutonomy (model (protocol m)) m.assignment ∧
      ¬ PackageRuntime.PostWithdrawalOperationalAutonomy (model (protocol m)) m.assignment := by
  constructor
  · rintro ⟨ha,hr,hw,⟨entry,he⟩,strategy,hs⟩
    exact postwithdrawal_source_present_resources m present entry
      (hs entry he entry [] StrategyGame.Play.initial).2.1
  · rintro ⟨ha,hr,hw,⟨entry,he⟩,strategy,hs⟩
    exact postwithdrawal_source_present_resources m present entry
      (hs entry he entry [] StrategyGame.Play.initial).2.1

theorem package_deletion_no_full :
    ¬ PackageRuntime.PostWithdrawalFullAutonomy (model (protocol packageDeletion)) packageDeletion.assignment := by
  intro h
  have hp := (package_readout_iff packageDeletion).mp
    (PackageRuntime.full_autonomy_implies_package _ _ h)
  exact package_deletion_package hp

/-- Acquisition absence and resource absence are separately tested; both are
semantic negatives with no assumed readiness alongside a missing input. -/
theorem missing_acquisition_no_games (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (k : Cell) (hk : k ∈ acquisition.dependencies) (hm : image a k = none) :
    ¬ PackageRuntime.PostWithdrawalFullAutonomy (model p) a ∧
      ¬ PackageRuntime.PostWithdrawalOperationalAutonomy (model p) a := by
  apply PackageRuntime.missing_acquisition_no_games (model p) a k hk
  rw [target_eq]
  exact hm

theorem missing_resource_no_games (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (k : Cell) (hk : k ∈ (resourceRaw p).readDependencies) (hm : image a k = none) :
    ¬ PackageRuntime.PostWithdrawalFullAutonomy (model p) a ∧
      ¬ PackageRuntime.PostWithdrawalOperationalAutonomy (model p) a := by
  apply PackageRuntime.missing_resource_no_games (model p) a k hk
  rw [target_eq]
  exact hm

/-- Sensitivity proposals cap ONE evolving readout at the declared source
snapshot occurrence two. The updater and resource accounts are unchanged. -/
def capped (field : ResourceRuntime.GrowthField) :=
  let raw := resourceRaw (protocol baseline)
  let cap : E Unit Nat := .map (fun x : Frame => min (x.2.counter) 2) (.register ())
  match field with
  | .order => {raw with order := cap}
  | .ticks => {raw with ticks := cap}
  | .progress => {raw with progress := cap}
  | .record => {raw with record := cap}

theorem capped_ready (field : ResourceRuntime.GrowthField) :
    ResourceRuntime.Ready (capped field) canonical := by
  refine ⟨?_,?_,?_⟩
  · cases field <;> exact (POS04RouteExecution.ready canonical (canonical_complete _)).2.2.1
  · cases field <;> exact (POS04RouteExecution.ready canonical (canonical_complete _)).2.2.2.1
  · intro k _; rfl

/-- A single-field guard for every resource-game growth readout, evaluated at
a genuine invariant state. It does not assume absence alongside readiness. -/
theorem capped_field_rejected (field : ResourceRuntime.GrowthField) :
    ¬ ResourceRuntime.StepLaw (RuntimeComponents.resourceSchema cfg) (capped field) canonical
      (capped_ready field) (frame .target ⟨.inK .p1w0,2,2,routeRegister .a,true⟩)
      .nominal .cw (.inK .p2w1) := by
  apply ResourceRuntime.nonadvancing_field_rejected _ _ _ _ _ _ _ _ field 2 2
  · cases field <;> rfl
  · have hnext : ResourceRuntime.update (capped field) canonical (capped_ready field)
        (frame .target ⟨.inK .p1w0,2,2,routeRegister .a,true⟩) .nominal .cw (.inK .p2w1) =
        frame .target ⟨.inK .p2w1,3,3,routeRegister .a,true⟩ := by
      cases field <;> exact policy_update .p1w0 .p2w1 .a 2 2 .nominal
    rw [hnext]
    cases field <;> rfl
  · exact Nat.le_refl _

end CSTTT.TargetTheory.GenericHandoff.POS04MultiResourceGames
