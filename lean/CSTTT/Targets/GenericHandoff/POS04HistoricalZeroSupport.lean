import CSTTT.Targets.GenericHandoff.POS04HistoricalResourceEquivalence
import CSTTT.Targets.GenericHandoff.ResourceGameLocality

/-! TTH-06: diagnostic of the requested unrestricted AF/AO game equivalence.
RULE BEFORE COMPUTATION: append one ZERO-MASS exit entry to every target
response row at p2w1, the factor reached by phase-2 acquisition. Leave all other
raw fields unchanged. Staging swaps source/target row namespaces, so the source
assignment edit is rows.source. No probability, policy, resource, event, history,
or positive-support branch changes. This is a representation diagnostic, not a
new positive model declaration or a modification of the frozen models.

Frozen rowClosed8 requires EVERY listed entry to have positive mass. The causal
game quantifies EVERY positive-support successor and permits zero-mass entries.
The requested arbitrary-partial O equivalence is therefore false. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalZeroSupport
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RouteExecution POS04ResourceRuntime
open POS04HistoricalEntryEquivalence
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def rowsWithNullEntry (rows : KState → Action → List (Ambient × Nat)) :=
  fun s a => if s = .p2w1 then rows s a ++ [(.p2w0,0)] else rows s a

def assignment : CSTTT.POS04.Assigned.Assignment :=
  mapCell canonical (.rows .source) rowsWithNullEntry

def diagnostic : RawLaneModel := {baseline with assignment := assignment}

theorem assignment_complete : Complete primitiveCells assignment :=
  mapCell_complete _ _ (CSTTT.POS04.Assigned.canonical_complete primitiveCells)

theorem nominal_protocol : POS04OperationalGame.Protocol diagnostic :=
  (POS04HistoricalRuntimeProtocol.raw_check_iff _).mp (by decide +kernel)

theorem frozen_ao_rejects : ¬ AO diagnostic := by
  change operationalAutonomyCheck diagnostic ≠ true
  decide +kernel

theorem staged_assignment : image assignment = mapCell canonical (.rows .target) rowsWithNullEntry := by
  funext k
  cases k <;> try rfl
  all_goals rename_i t; cases t <;> first | rfl | exact congrFun image_canonical _

abbrev M := POS04HistoricalRuntime.model (protocol diagnostic)
abbrev HA := ready diagnostic nominal_protocol
abbrev HR := POS04HistoricalRuntime.resource_ready_of_protocol diagnostic nominal_protocol
abbrev B := POS04HistoricalRuntimeInstance.M
abbrev BA := POS04HistoricalRuntimeInstance.HA
abbrev BR := POS04HistoricalRuntimeInstance.HR

theorem target_assignment : HistoricalPackageRuntime.target M assignment =
    mapCell canonical (.rows .target) rowsWithNullEntry :=
  (POS04HistoricalRuntime.target_eq _ _).trans staged_assignment

theorem agreement (scope : List Cell) (hn : Cell.rows .target ∉ scope) :
    Agrees scope (HistoricalPackageRuntime.target M assignment) canonical := by
  intro k hk
  rw [target_assignment]
  exact mapCell_other_cell _ _ _ _ (fun eq => hn (eq ▸ hk))

theorem resource_agreement :
    Agrees (HistoricalPackageRuntime.resources M).readDependencies
      (HistoricalPackageRuntime.target M assignment) canonical :=
  agreement _ (by decide +kernel)

theorem program_agreement (reg : Unit) :
    Agrees ((HistoricalPackageRuntime.resources M).execution.program reg).dependencies
      (HistoricalPackageRuntime.target M assignment) canonical :=
  agreement _ (by cases reg; decide +kernel)

theorem update_unchanged (r : Registers Unit FrameValue) (d : LaneDisturbance) (a : Action) (o : Ambient) :
    ResourceRuntime.update (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M assignment) HR r d a o =
    ResourceRuntime.update (HistoricalPackageRuntime.resources B) (HistoricalPackageRuntime.target B canonical) BR r d a o := by
  have hu := ResourceRuntime.update_locality (HistoricalPackageRuntime.resources M) HR
    (by simpa only [HistoricalPackageRuntime.ResourceReady,POS04HistoricalRuntimeInstance.target_canonical] using BR) program_agreement r d a o
  simpa only [POS04HistoricalRuntimeInstance.target_canonical] using hu

theorem inside_unchanged (r : Registers Unit FrameValue) :
    ResourceRuntime.Inside M.resourceSchema (HistoricalPackageRuntime.resources M)
      (HistoricalPackageRuntime.target M assignment) r ↔
    ResourceRuntime.Inside B.resourceSchema (HistoricalPackageRuntime.resources B)
      (HistoricalPackageRuntime.target B canonical) r := by
  simpa only [POS04HistoricalRuntimeInstance.target_canonical] using
    ResourceRuntime.inside_locality M.resourceSchema (HistoricalPackageRuntime.resources M) resource_agreement r

theorem resources_unchanged (r : Registers Unit FrameValue) :
    ResourceRuntime.ResourceClosed M.resourceSchema (HistoricalPackageRuntime.resources M)
      (HistoricalPackageRuntime.target M assignment) r ↔
    ResourceRuntime.ResourceClosed B.resourceSchema (HistoricalPackageRuntime.resources B)
      (HistoricalPackageRuntime.target B canonical) r := by
  simpa only [POS04HistoricalRuntimeInstance.target_canonical] using
    ResourceRuntime.resource_locality M.resourceSchema (HistoricalPackageRuntime.resources M) resource_agreement r

theorem legal_unchanged (r : Registers Unit FrameValue) (d : LaneDisturbance) (a : Action) :
    ResourceRuntime.Legal M.resourceSchema (HistoricalPackageRuntime.resources M)
      (HistoricalPackageRuntime.target M assignment) r d a ↔
    ResourceRuntime.Legal B.resourceSchema (HistoricalPackageRuntime.resources B)
      (HistoricalPackageRuntime.target B canonical) r d a := by
  simpa only [POS04HistoricalRuntimeInstance.target_canonical] using
    ResourceRuntime.legal_locality M.resourceSchema (HistoricalPackageRuntime.resources M) resource_agreement r d a

theorem step_unchanged (r : Registers Unit FrameValue) (d : LaneDisturbance) (a : Action) (o : Ambient) :
    ResourceRuntime.StepLaw M.resourceSchema (HistoricalPackageRuntime.resources M)
      (HistoricalPackageRuntime.target M assignment) HR r d a o ↔
    ResourceRuntime.StepLaw B.resourceSchema (HistoricalPackageRuntime.resources B)
      (HistoricalPackageRuntime.target B canonical) BR r d a o := by
  simpa only [POS04HistoricalRuntimeInstance.target_canonical] using
    ResourceRuntime.step_locality M.resourceSchema (HistoricalPackageRuntime.resources M) HR
      (by simpa only [HistoricalPackageRuntime.ResourceReady,POS04HistoricalRuntimeInstance.target_canonical] using BR)
      resource_agreement program_agreement r d a o

theorem legacy_entries_unchanged : entries diagnostic = entries baseline := by decide +kernel

theorem legacy_entry_runs_unchanged (e : WithdrawalEntry) :
    POS04OperationalGame.entryRun diagnostic e = POS04OperationalGame.entryRun baseline e := by rfl

theorem entries_unchanged (r : Registers Unit FrameValue) :
    HistoricalPackageRuntime.Entries M assignment HA r ↔
      HistoricalPackageRuntime.Entries B canonical BA r := by
  constructor
  · intro he
    obtain ⟨x,rfl,hx⟩ := entries_target diagnostic nominal_protocol r he
    apply (baseline_entries_iff x).mpr
    rcases hx with ⟨e,he,hr⟩
    exact ⟨e,by rw [← legacy_entries_unchanged]; exact he,hr.trans (legacy_entry_runs_unchanged e)⟩
  · intro he
    obtain ⟨x,rfl,hx⟩ := entries_target baseline POS04ExactGames.positive_games.2.1 r he
    apply (entries_iff diagnostic nominal_protocol x).mpr
    rcases hx with ⟨e,he,hr⟩
    exact ⟨e,by rw [legacy_entries_unchanged]; exact he,hr.trans (legacy_entry_runs_unchanged e).symm⟩

theorem rows_on_kernel (s : KState) (rid : RouteId) (n ticks : Nat) (d : LaneDisturbance) (a : Action) :
    ResourceRuntime.rows (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M assignment)
      (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩) d a =
    if s = .p2w1 then
      ResourceRuntime.rows (HistoricalPackageRuntime.resources B) (HistoricalPackageRuntime.target B canonical)
        (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩) d a ++ [(.p2w0,0)]
    else ResourceRuntime.rows (HistoricalPackageRuntime.resources B) (HistoricalPackageRuntime.target B canonical)
      (frame .target ⟨.inK s,n,ticks,routeRegister rid,true⟩) d a := by
  rw [POS04HistoricalRuntime.target_eq]
  change HistoricalAcquisition.rows (POS04HistoricalRuntime.acquisitionRaw (protocol diagnostic))
    (image assignment) _ d a = _
  rw [POS04HistoricalRuntime.rows_eq (protocol diagnostic) (image assignment)
    (rawReady diagnostic nominal_protocol) ⟨.inK s,n,ticks,routeRegister rid,true⟩ d a,staged_assignment,
    POS04HistoricalRuntimeInstance.actual_rows]
  change ((rowsWithNullEntry (actionRow .target)) s a).map (fun e => (e.1,(e.2 : Rat)/4)) =
    if s = .p2w1 then (actionRow .target s a).map (fun e => (e.1,(e.2 : Rat)/4)) ++ [(.p2w0,0)]
    else (actionRow .target s a).map (fun e => (e.1,(e.2 : Rat)/4))
  unfold rowsWithNullEntry
  split
  · rw [List.map_append]
    have hz : ((0 : Nat) : Rat) = 0 := by decide +kernel
    simp only [List.map_cons,List.map_nil,hz,Rat.div_def,Rat.zero_mul]
  · rfl

/-- Probability-zero entries have no positive-support successor. This is a
proof about the interpreted probability, not an omitted branch filter. -/
theorem null_entry_support {X D A O : Type} (row : StrategyGame.Rows X D A O)
    (x : X) (d : D) (a : A) (dead o : O) :
    StrategyGame.PositiveSupport (fun x d a => row x d a ++ [(dead,0)]) x d a o ↔
      StrategyGame.PositiveSupport row x d a o := by
  constructor
  · rintro ⟨w,hm,hp⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact ⟨w,hm,hp⟩
    · have hw : (0 : Rat) = w := (congrArg Prod.snd (List.mem_singleton.mp hm)).symm
      rw [← hw] at hp
      exact False.elim (Rat.lt_irrefl hp)
  · rintro ⟨w,hm,hp⟩
    exact ⟨w,List.mem_append_left _ hm,hp⟩

theorem null_entry_normalized {X D A O : Type} (row : StrategyGame.Rows X D A O)
    (x : X) (d : D) (a : A) (dead : O) (hn : StrategyGame.Normalized row x d a) :
    StrategyGame.Normalized (fun x d a => row x d a ++ [(dead,0)]) x d a := by
  refine ⟨?_,?_,?_⟩
  · intro e hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hn.1 e hm
    · rw [List.mem_singleton.mp hm]; change (0 : Rat) ≤ 0; decide
  · have hz (xs : List Rat) : (xs ++ [0]).sum = xs.sum := by
      induction xs with
      | nil => simp only [List.nil_append,List.sum_cons,List.sum_nil,Rat.add_zero]
      | cons h t ih => simp only [List.cons_append,List.sum_cons,ih]
    simp only [List.map_append,List.map_cons,List.map_nil]
    exact (hz _).trans hn.2.1
  · obtain ⟨o,ho⟩ := hn.2.2
    exact ⟨o,(null_entry_support row x d a dead o).mpr ho⟩

theorem supported_unchanged (r : Registers Unit FrameValue) (hi : POS04MultiResourceGames.invariant r)
    (d : LaneDisturbance) (a : Action) (o : Ambient) :
    StrategyGame.PositiveSupport
      (ResourceRuntime.rows (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M assignment)) r d a o ↔
    StrategyGame.PositiveSupport
      (ResourceRuntime.rows (HistoricalPackageRuntime.resources B) (HistoricalPackageRuntime.target B canonical)) r d a o := by
  obtain ⟨s,rid,n,ticks,rfl⟩ := hi
  unfold StrategyGame.PositiveSupport
  rw [rows_on_kernel]
  by_cases hs : s = .p2w1
  · rw [if_pos hs]
    exact null_entry_support _ _ _ _ .p2w0 o
  · rw [if_neg hs]

theorem normalized_unchanged (r : Registers Unit FrameValue) (hi : POS04MultiResourceGames.invariant r)
    (d : LaneDisturbance) (a : Action)
    (hn : StrategyGame.Normalized
      (ResourceRuntime.rows (HistoricalPackageRuntime.resources B) (HistoricalPackageRuntime.target B canonical)) r d a) :
    StrategyGame.Normalized
      (ResourceRuntime.rows (HistoricalPackageRuntime.resources M) (HistoricalPackageRuntime.target M assignment)) r d a := by
  obtain ⟨s,rid,n,ticks,rfl⟩ := hi
  have hz := null_entry_normalized _ _ _ _ Ambient.p2w0 hn
  unfold StrategyGame.Normalized StrategyGame.PositiveSupport at hn hz ⊢
  rw [rows_on_kernel]
  by_cases hs : s = .p2w1
  · rw [if_pos hs]; exact hz
  · rw [if_neg hs]; exact hn

theorem operational_certificate : Nonempty (HistoricalPackageRuntime.OperationalCertificate M assignment HA HR) := by
  refine ⟨{ inside := POS04MultiResourceGames.invariant
            withdrawn := POS04HistoricalRuntime.withdrawal_of_protocol diagnostic nominal_protocol
            entriesNonempty := ?_
            entriesInside := ?_
            packageInside := ?_
            resourcesInside := ?_
            response := ?_ }⟩
  · obtain ⟨r,hr⟩ := POS04HistoricalRuntimeInstance.entries_nonempty
    exact ⟨r,(entries_unchanged r).mpr hr⟩
  · intro r hr
    exact POS04HistoricalRuntimeInstance.entries_inside r ((entries_unchanged r).mp hr)
  · intro r hr
    exact (inside_unchanged r).mpr (POS04HistoricalRuntimeInstance.package_inside r hr).2.1
  · intro r hr
    exact (resources_unchanged r).mpr (POS04HistoricalRuntimeInstance.resource_inside r hr)
  · intro r hr d
    obtain ⟨s,rid,n,ticks,rfl⟩ := hr
    let x := frame .target (⟨.inK s,n,ticks,routeRegister rid,true⟩ : Run6)
    have hi : POS04MultiResourceGames.invariant x := ⟨s,rid,n,ticks,rfl⟩
    refine ⟨canonicalAction s,
      (legal_unchanged x d _).mpr (POS04HistoricalRuntimeInstance.legal x hi d _),
      normalized_unchanged x hi d _ (POS04HistoricalRuntimeInstance.policy_normalized s rid n ticks d),?_⟩
    intro o ho
    have hbase := (supported_unchanged x hi d _ o).mp ho
    obtain ⟨t,rfl⟩ := POS04HistoricalRuntimeInstance.policy_supported s rid n ticks d o hbase
    refine ⟨?_,(step_unchanged x d _ _).mpr (POS04HistoricalRuntimeInstance.policy_step s t rid n ticks d)⟩
    rw [update_unchanged,POS04HistoricalRuntimeInstance.policy_update]
    exact ⟨t,rid,n+1,ticks+1,rfl⟩

/-- Direct causal-game readout: soundness inducts over all plays, retaining
all positive-support outcomes. No bounded horizon or AO proof is substituted. -/
theorem operational_game_accepts : HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy M assignment :=
  HistoricalPackageRuntime.operational_soundness M assignment ⟨HA,HR,operational_certificate⟩

theorem counterexample :
    (POS04HistoricalRuntimeProtocol.check diagnostic).read (image assignment) = some true ∧
    HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy M assignment ∧ ¬ AO diagnostic :=
  ⟨(POS04HistoricalRuntimeProtocol.check_iff _).mpr nominal_protocol,operational_game_accepts,frozen_ao_rejects⟩

theorem whole_operational_equivalence_false :
    ¬ (∀ m : RawLaneModel,
      (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) = some true →
      (HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy
        (POS04HistoricalRuntime.model (protocol m)) m.assignment ↔ AO m)) := by
  intro h
  exact frozen_ao_rejects ((h diagnostic counterexample.1).mp operational_game_accepts)

/-- The nominal canonical probability kernel is unchanged; no retention or
price parameter was adjusted to produce the diagnostic. -/
theorem canonical_p_unchanged : PUnchanged8 (withdrawnInputs diagnostic) :=
  nominal_protocol.2.2.2.1

def mass (rows : List (Ambient × Nat)) (o : Ambient) : Nat :=
  (rows.filter (fun e => e.1 == o) |>.map Prod.snd).sum

theorem mass_unchanged (s : KState) (a : Action) (o : Ambient) :
    mass (rowsWithNullEntry (actionRow .target) s a) o = mass (actionRow .target s a) o := by
  cases s <;> cases a <;> cases o
  all_goals try (rename_i t; cases t)
  all_goals decide +kernel

/-- The scale four is T1's already-declared action-row denominator. Equality
holds for every outcome and every action, not just canonical responses. -/
theorem probabilities_unchanged (s : KState) (a : Action) (o : Ambient) :
    (mass (rowsWithNullEntry (actionRow .target) s a) o : Rat)/4 =
      (mass (actionRow .target s a) o : Rat)/4 :=
  congrArg (fun n : Nat => (n : Rat)/4) (mass_unchanged s a o)

/-- Protocol rejection agrees for both versions when the readouts are bound
to that computed raw instruction. This does not repair the positive O mismatch. -/
theorem protocol_failure_cases (m : RawLaneModel)
    (bad : (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) ≠ some true) :
    (¬ ((POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) = some true ∧
      HistoricalPackageRuntime.PostWithdrawalFullAutonomy
        (POS04HistoricalRuntime.model (protocol m)) m.assignment)) ∧ ¬ AF m ∧
    (¬ ((POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) = some true ∧
      HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy
        (POS04HistoricalRuntime.model (protocol m)) m.assignment)) ∧ ¬ AO m := by
  refine ⟨fun h => bad h.1,?_,fun h => bad h.1,?_⟩
  · intro h
    exact bad ((POS04HistoricalRuntimeProtocol.check_iff m).mpr (POS04FullGame.af_parts m h).1)
  · intro h
    exact bad ((POS04HistoricalRuntimeProtocol.check_iff m).mpr (POS04OperationalGame.ao_parts m h).1)

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalZeroSupport
