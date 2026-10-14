import CSTTT.Targets.GenericHandoff.POS04HistoricalProtocol

/-! The whole raw nominal protocol of frozen F/O, extracted as an instruction
on the same staged twelve-cell slice. Withdrawal metadata are raw parameters.
This check is NOT the game readout: safe responses/package preservation still
have to be proved by the runtime game. Its exact arbitrary-partial equivalence
is a component of the pending whole-game adapter, not its replacement. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalRuntimeProtocol
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter RegisterInitialization
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def atTarget (m : RawLaneModel) (a : CSTTT.POS04.Assigned.Assignment) : RawLaneModel :=
  {m with assignment := exchangeAssignment a}

theorem image_at_target (m : RawLaneModel) (a : CSTTT.POS04.Assigned.Assignment) :
    image (atTarget m a).assignment = a := exchange_assignment_involution a

def rawCheck (m : RawLaneModel) : Bool :=
  decide (Assigned.Complete autonomyInputs (image m.assignment)) && withdrawalCheck m &&
  advancementCheck m && decide (PUnchanged8 (withdrawnInputs m)) &&
  routeIds.all (phase2Check m)

theorem raw_check_iff (m : RawLaneModel) : rawCheck m = true ↔ POS04OperationalGame.Protocol m := by
  simp only [rawCheck,POS04OperationalGame.Protocol,Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨hc,hw⟩,ha⟩,hp⟩,he⟩; exact ⟨hc,hw,ha,hp,he⟩
  · rintro ⟨hc,hw,ha,hp,he⟩; exact ⟨⟨⟨⟨hc,hw⟩,ha⟩,hp⟩,he⟩

/-- Exact slice: every protocol input is one of the frozen twelve cells. -/
theorem locality (m n : RawLaneModel)
    (he : Assigned.Agrees phase2Dependencies (image m.assignment) (image n.assignment))
    (hret : m.retained = n.retained) (hrem : m.removed = n.removed)
    (hsrc : m.sourcePresentAfterWithdrawal = n.sourcePresentAfterWithdrawal) :
    rawCheck m = rawCheck n := by
  have hcom : decide (Assigned.Complete autonomyInputs (image m.assignment)) =
      decide (Assigned.Complete autonomyInputs (image n.assignment)) := by
    have ha : Assigned.Agrees autonomyInputs (image m.assignment) (image n.assignment) :=
      fun k hk => he k ((POS04HistoricalAutonomy.exact_dependency_scope k).mp
        (List.mem_append_left phase2Dependencies hk : k ∈ POS04OperationalGame.dependencies))
    have eqv := Assigned.complete_locality ha
    by_cases h : Assigned.Complete autonomyInputs (image m.assignment)
    · simp only [decide_eq_true h,decide_eq_true (eqv.mp h)]
    · have hn : ¬ Assigned.Complete autonomyInputs (image n.assignment) := fun hn => h (eqv.mpr hn)
      simp only [decide_eq_false h,decide_eq_false hn]
  have hph : routeIds.all (phase2Check m) = routeIds.all (phase2Check n) := by
    apply congrArg (fun f => routeIds.all f)
    funext rid
    exact POS04HistoricalProtocol.phase2_locality m n he rid
  simp only [rawCheck,hcom,hph,withdrawalCheck,hrem,hsrc]
  simp only [advancementCheck,withdrawnInputs,withdrawnAssignment,
    ticks6,writers6,available8,PUnchanged8,Ledger8,
    runInputs6,extraInputs,inputs,clause8,viabilityInputs,Assigned.decode,
    clauseScope,commonScope,mapCell,Assigned.put,hret]
  dsimp only
  simp only [he (.rows .target) (by decide),he .policy (by decide),
    he (.ticks .target) (by decide),he (.resources .target) (by decide),
    he .maintenance (by decide),he .routeTable (by decide),
    he .writers (by decide)]

/-- The decoder receives only the slice computed by eager cell instructions.
No caller supplies a protocol outcome, candidate assignment, or game verdict. -/
def check (m : RawLaneModel) : StaticView Cell Value Bool :=
  ⟨.map (fun a => rawCheck (atTarget m a)) (StaticSlice.instruction phase2Dependencies)⟩

theorem dependencies (m : RawLaneModel) : (check m).dependencies = phase2Dependencies := by
  simp only [check,StaticView.dependencies,Expr.dependencies,StaticSlice.dependencies]

theorem computed (m : RawLaneModel) (hc : Assigned.Complete phase2Dependencies (image m.assignment)) :
    (check m).read (image m.assignment) = some (rawCheck m) := by
  change ((StaticSlice.instruction phase2Dependencies).eval (image m.assignment) noRegisters ()).map _ = _
  rw [StaticSlice.evaluation _ _ hc]
  simp only [Option.map_some]
  apply congrArg some
  apply locality
  · intro k hk
    rw [image_at_target]
    simp [GenericHandoff.decode,hk]
  · rfl
  · rfl
  · rfl

/-- Arbitrary partial assignments, in both directions. In particular an
unused hazard/source-tick/source-funding cell is not made mandatory. -/
theorem check_iff (m : RawLaneModel) :
    (check m).read (image m.assignment) = some true ↔ POS04OperationalGame.Protocol m := by
  constructor
  · intro he
    have hc : Assigned.Complete phase2Dependencies (image m.assignment) := by
      intro k hk
      cases hv : image m.assignment k with
      | some v => rfl
      | none =>
        have bad := (check m).missing _ k (by rw [dependencies]; exact hk) hv
        rw [bad] at he
        contradiction
    rw [computed m hc] at he
    exact (raw_check_iff m).mp (Option.some.inj he)
  · intro hp
    have hc := POS04OperationalGame.protocol_complete m hp
    have hc' : Assigned.Complete phase2Dependencies (image m.assignment) :=
      fun k hk => hc k (List.mem_append_right autonomyInputs hk)
    rw [computed m hc',(raw_check_iff m).mpr hp]

theorem missing_rejected (m : RawLaneModel) (k : Cell) (hk : k ∈ phase2Dependencies)
    (hm : image m.assignment k = none) : (check m).read (image m.assignment) = none :=
  (check m).missing _ k (by rw [dependencies]; exact hk) hm

theorem baseline_protocol : (check baseline).read (image baseline.assignment) = some true :=
  (check_iff _).mpr POS04ExactGames.positive_games.2.1

theorem duplicate_event_protocol :
    (check POS04HistoricalDuplicateEvents.diagnostic).read
      (image POS04HistoricalDuplicateEvents.diagnostic.assignment) = some true :=
  (check_iff _).mpr ((POS04OperationalGame.game_iff_ao _).mpr
    POS04HistoricalDuplicateEvents.legacy_ao_accepts).1

theorem missing_past_ticks_protocol :
    (check POS04RuntimeEquivalenceBoundary.missingPastTicks).read
      (image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment) = some true :=
  (check_iff _).mpr POS04RuntimeEquivalenceBoundary.legacy_operational_game_accepts.1

theorem source_recharge_protocol :
    (check POS04ReceiverResetProjection.sourceRechargeUnavailable).read
      (image POS04ReceiverResetProjection.sourceRechargeUnavailable.assignment) = some true :=
  (check_iff _).mpr POS04ReceiverResetProjection.diagnostic_legacy_operational_game_accepts.1

/-- Necessary post-withdrawal absence, checked from the raw metadata.
This is independent of receiver activation's separate source-present check. -/
theorem postwithdrawal_source_present_rejected (m : RawLaneModel)
    (hs : m.sourcePresentAfterWithdrawal = true) :
    (check m).read (image m.assignment) ≠ some true := by
  intro he
  have hw := ((check_iff m).mp he).2.1
  simp only [withdrawalCheck,hs,Bool.not_true,Bool.and_false] at hw
  contradiction

/-- In-memory one-field sensitivity proposal; no frozen model is edited. -/
def zeroLedger : RawLaneModel :=
  {baseline with assignment := Assigned.put canonical .maintenance (some {canonicalValue .maintenance with initialBudget := 0, actionCost := 0, rechargePerAction := 0})}

theorem zero_ledger_rejected : (check zeroLedger).read (image zeroLedger.assignment) ≠ some true := by
  intro he
  have hp := (check_iff zeroLedger).mp he
  have bad := (POS04OperationalGame.protocol_resources zeroLedger hp).2.1.2.1
  change (0 : Nat) = 1 at bad
  contradiction

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalRuntimeProtocol
