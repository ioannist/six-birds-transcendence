import CSTTT.Targets.GenericHandoff.GameAutonomyTransport
import CSTTT.Targets.GenericHandoff.POS04RegisterGames

/-! A genuine POS-04 instance of the finite projection engine, for arbitrary
partial assignments. The run invariant is extracted from the game, not chosen
as a baseline safe set. ALL actual positive-support branches project to the
existing factor step relation. Static withdrawal/boundary facts reuse the
computed TTH-05 certificate; its response/inside fields are not used for the
new projected invariant or response proof. The broader raw-component binding
of this engine remains an enclosing RawHandoff obligation.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04GameAutonomyTransport
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.AutonomyTheory
open POS04OperationalGame
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def factor (m : RawLaneModel) : GameAutonomyTransport.FactorData :=
  let d := computedExactAutonomy m .p0w0
  ⟨d.sys,d.withdrawal,d.resourceOwner,d.antiStall,d.budgetSolvent,
    d.boundaryFixedBeforeEvaluation,d.disturbanceClassFixedBeforeEvaluation⟩

def project (r : Run) : KState := match r.factor with
  | .inK s => s
  | .p2w0 | .p5w1 => .p0w0

theorem project_inK (r : Run) (s : KState) (hs : r.factor = .inK s) : project r = s := by
  simp only [project,hs]

/-- Every law is proved against the assigned actual updater. No assumption
that ledger, tape or counter context is irrelevant is introduced. -/
theorem projection_laws (m : RawLaneModel) (hf : AF m) :
    GameAutonomyTransport.ProjectionLaws (factor m) (rows m) (update m) (Protocol m)
      (POS04FullGame.PackageAt m) (ResourceClosed m) (Legal m) (StepLaw m) project := by
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ (POS04FullGame.af_parts m hf).2.2.1
  obtain ⟨s,hs,⟨old⟩⟩ := AF_each_entry_exact_autonomy m hf e he
  have hp := (POS04FullGame.af_parts m hf).1
  constructor
  · intro _; exact old.sourceRemoved
  · intro _; exact old.bridgeRemoved
  · intro _; exact old.migrationControllerRemoved
  · intro _; exact old.externalDecoderRemoved
  · intro _; exact old.externalSchedulerRemoved
  · intro _; exact old.undeclaredRepairRemoved
  · intro _; exact old.boundaryFixed
  · intro _; exact old.disturbanceClassFixed
  · rintro r ⟨_,s,hs,hpkg⟩
    change packageAtCheck m (project r) = true
    rw [project_inK r s hs]
    exact hpkg
  · intro r hr res hres
    change res ∈ [rechargeResourceCode] at hres
    have heq := List.mem_singleton.mp hres
    subst res
    exact List.mem_map.mpr ⟨.targetRecharge,AF_retained_recharge m hf,rfl⟩
  · intro _; exact old.retainedResourcesTargetOwned
  · intro r d a hr hlegal
    have ho : (inputs m).viability.resource.owner = .target :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hr.1).2
    rw [viability_eq] at ho
    exact congrArg tagCarrierId ho
  · intro r d a o hlegal hsupport
    obtain ⟨_,s,hs,hclosed⟩ := hlegal
    obtain ⟨w,hw,_⟩ := hsupport
    simp only [rows,if_pos (protocol_complete m hp),rawRow,hs] at hw
    obtain ⟨e,he,heq⟩ := List.mem_map.mp hw
    obtain ⟨hn,y,hy,_⟩ := (closed_fields _ _ _ _ hclosed).2.2 e he
    have heo : e.1 = o := congrArg Prod.fst heq
    have hout : o = .inK y := heo.symm.trans hy
    have hproject : project (update m r d a o) = y := by
      apply project_inK; exact hout
    change (computedAutonomySystem m).step (project r) d a (project (update m r d a o))
    rw [project_inK r s hs,hproject]
    refine ⟨e.2,hn,?_⟩
    rw [← viability_eq]
    have hpair : (.inK y,e.2) = e := by cases e with | mk dest n => cases hy; rfl
    rw [hpair]
    exact he
  · intro r d a o hstep
    exact (AF_shared_parts m hf).2.2.1
  · intro r d a o hstep
    exact (protocol_resources m hp).2.1

/-- Every entry of the semantic full game has a TTH-05 certificate whose
inside region is the actual strategy-invariant image, not an assumed set. -/
theorem full_game_each_entry_exact (m : RawLaneModel) (hg : POS04FullGame.Autonomy m) :
    ∃ cert : POS04FullGame.Certificate m,
      ∀ entry, Entries m entry →
        Nonempty (ExactAutonomyCertificate (GameAutonomyTransport.projectedData (factor m) cert project entry)) :=
  GameAutonomyTransport.game_each_entry_exact (factor m) project
    (projection_laws m ((POS04FullGame.game_iff_af m).mp hg)) hg

theorem full_game_each_entry_words (m : RawLaneModel) (hg : POS04FullGame.Autonomy m) :
    ∃ cert : POS04FullGame.Certificate m,
      ∀ entry, Entries m entry → ∀ word : List LaneDisturbance,
        ∃ y, ControlledRun (GameAutonomyTransport.projectedData (factor m) cert project entry)
          (project entry) word y ∧ packageAtCheck m y = true :=
  GameAutonomyTransport.game_each_entry_finite_words (factor m) project
    (projection_laws m ((POS04FullGame.game_iff_af m).mp hg)) hg

theorem register_game_each_entry_exact (m : RawLaneModel) (hg : POS04RegisterGames.Full m) :
    ∃ cert : POS04FullGame.Certificate m,
      ∀ entry, Entries m entry →
        Nonempty (ExactAutonomyCertificate (GameAutonomyTransport.projectedData (factor m) cert project entry)) :=
  full_game_each_entry_exact m ((POS04RegisterGames.full_iff_game m).mp hg)

theorem positive :
    ∃ cert : POS04FullGame.Certificate baseline,
      ∀ entry, Entries baseline entry →
        Nonempty (ExactAutonomyCertificate (GameAutonomyTransport.projectedData (factor baseline) cert project entry)) :=
  full_game_each_entry_exact baseline POS04ExactGames.positive_games.1

/-- Nonemptiness is separate from the universal entry statement, and the
projection retains every positive branch, not merely a lucky successor. -/
theorem positive_entries_and_support :
    (∃ entry, Entries baseline entry) ∧
    ∃ cert : POS04FullGame.Certificate baseline,
      (∀ entry, Entries baseline entry →
        Nonempty (ExactAutonomyCertificate (GameAutonomyTransport.projectedData (factor baseline) cert project entry))) ∧
      ∀ r, cert.inside r → ∀ d,
        ∃ act, (factor baseline).sys.actionOwner act = (factor baseline).sys.carrier.id ∧
          StrategyGame.Normalized (rows baseline) r d act ∧
          ∀ o, StrategyGame.PositiveSupport (rows baseline) r d act o →
            cert.inside (update baseline r d act o) ∧
            (factor baseline).sys.step (project r) d act (project (update baseline r d act o)) ∧
            (factor baseline).antiStall (project r) d act (project (update baseline r d act o)) ∧
            (factor baseline).budgetSolvent (project r) d act (project (update baseline r d act o)) := by
  obtain ⟨cert,hcert⟩ := positive
  exact ⟨POS04ExactGames.positive_games.1.2.1,cert,hcert,
    fun r hr d => GameAutonomyTransport.projected_response_all_support (factor baseline)
      cert project (projection_laws baseline baseline_AF) r hr d⟩

/-- Removing the acquisition corridor does not remove post-exit autonomy.
The registered lineage-only control retains the genuine entry transport. -/
theorem lineage_control_each_entry :
    ∃ cert : POS04FullGame.Certificate lineageDeletion,
      ∀ entry, Entries lineageDeletion entry →
        Nonempty (ExactAutonomyCertificate (GameAutonomyTransport.projectedData
          (factor lineageDeletion) cert project entry)) :=
  full_game_each_entry_exact lineageDeletion ((POS04FullGame.game_iff_af _).mpr lineage_deletion_AF)

end CSTTT.TargetTheory.GenericHandoff.POS04GameAutonomyTransport
