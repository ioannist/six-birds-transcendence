import CSTTT.Targets.GenericHandoff.POS04HistoricalResourceEquivalence
import CSTTT.Targets.GenericHandoff.POS04HistoricalPackageEquivalence
import CSTTT.Targets.GenericHandoff.HistoricalSparseRuntime
import CSTTT.Targets.GenericHandoff.SparseScaledRows

/-! Arbitrary-partial nominal row/actual-step laws. All row transport below
requires actual resource closure; unfunded raw rows are not silently equated
to frozen rows. Sparse closure derives from normalization and all-support
successor safety, not from resource legality. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseLaws
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RouteExecution POS04ResourceRuntime POS04OperationalGame
open POS04HistoricalEntryEquivalence POS04HistoricalResourceEquivalence
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Exact sparse-format safety of one assigned row; no duplicate/order gate. -/
theorem row_closed_iff (m : RawLaneModel) (hp : Protocol m) (r : Run6) (s : KState)
    (hs : r.factor = .inK s) (d : LaneDisturbance) (act : Action) (S : List KState) :
    rowClosed8 (inputs m).viability s act S = true ↔
      StrictSparseGame.StrictSparse (rows m r d act) ∧
      StrategyGame.Normalized (rows m) r d act ∧
      ∀ o, StrategyGame.PositiveSupport (rows m) r d act o → ∃ t, o = .inK t ∧ t ∈ S := by
  have eqv := SparseScaledRows.closed_iff 4 ((inputs m).viability.rows s act) (by decide)
    (fun o => ∃ t, o = Ambient.inK t ∧ t ∈ S)
  have check : rowClosed8 (inputs m).viability s act S = true ↔
      ((inputs m).viability.rows s act ≠ [] ∧
      (((inputs m).viability.rows s act).map Prod.snd).sum = 4 ∧
      ∀ e ∈ (inputs m).viability.rows s act, e.2 > 0 ∧ ∃ t, e.1 = .inK t ∧ t ∈ S) := by
    constructor
    · exact closed_fields _ _ _ _
    · rintro ⟨hn,ht,hi⟩
      simp only [rowClosed8,Bool.and_eq_true,List.all_eq_true]
      refine ⟨⟨by simpa using List.isEmpty_eq_false_iff.mpr hn,decide_eq_true ht⟩,?_⟩
      intro e he
      obtain ⟨hw,t,ho,hm⟩ := hi e he
      simp [ho,hw,hm]
  rw [check,eqv]
  have four : ((4 : Nat) : Rat) = 4 := by decide +kernel
  simp only [rows,if_pos (protocol_complete m hp),rawRow,hs,ScaledRows.probabilities,
    StrategyGame.Normalized,StrategyGame.PositiveSupport,four]

/-- Derive the complete resource/counter law from the actual conserved unit
ledger, writer, assigned tick and ACTUAL updater, not a supplied step verdict. -/
theorem raw_step (m : RawLaneModel) (hp : Protocol m)
    (hr : HistoricalPackageRuntime.ResourceReady (model m) m.assignment)
    (r : Run6) (hc : ResourceClosed m r) (s : KState) (hs : r.factor = .inK s)
    (d : LaneDisturbance) (act : Action)
    (hn : ((inputs m).viability.rows s act).isEmpty = false) (o : Ambient) :
    ResourceRuntime.StepLaw (model m).resourceSchema (rawResource m)
      (HistoricalPackageRuntime.target (model m) m.assignment) hr (frame .target r) d act o := by
  have ht := protocol_tick m hp s act hn
  have next := step_preserves m hp r hc s hs d act hn o
  have he := update_eq m hp hr r d act o
  have tickRead : (rawResource m).ticks.eval (image m.assignment) (frame .target r) () = some r.ticks := rfl
  have adv : (rawResource m).advances.eval (image m.assignment) (frame .target r) (d,act,o) =
      some (⟨1,1,1,1⟩ : ResourceRuntime.Advances) := by
    have hcell := POS04RegisterDynamics.cell_value ((protocol_complete m hp) (.ticks .target) (by decide))
    change POS04ResourceRuntime.advances.eval _ _ _ = _
    simp only [POS04ResourceRuntime.advances,Expr.eval,frame,RunFrame.pack]
    rw [hcell]
    change some (⟨1,(match r.factor with | .inK s => (inputs m).ticks s act | _ => 0),1,1⟩ : ResourceRuntime.Advances) = _
    simp only [hs]
    rw [ht]
  unfold ResourceRuntime.StepLaw
  rw [he,POS04HistoricalRuntime.target_eq]
  refine ⟨(resource_closed_iff m hp _).mpr next.1,account r,account (update m r d act o),
    unitCharge,⟨1,1,1,1⟩,r.counter,r.ticks,r.counter,record m r,
    accounts_eval m hp r,accounts_eval m hp _,charge_eval m hp r d act,adv,
    by decide,by decide,by decide,by decide,?_,rfl,?_,tickRead,?_,rfl,?_,record_eval m hp r,?_,rfl⟩
  · intro res hres
    have hres' : res = .recharge := List.mem_singleton.mp hres
    subst res
    simp only [account,hc.2.2.1,next.1.2.2.1,unitCharge,if_true]
  · change some (update m r d act o).counter = some (r.counter+1)
    exact congrArg some next.2.2.1
  · change some (update m r d act o).ticks = some (r.ticks+1)
    exact congrArg some next.2.2.2.1
  · change some (update m r d act o).counter = some (r.counter+1)
    exact congrArg some next.2.2.1
  · rw [record_eval m hp _]
    exact congrArg some next.2.2.2.2.1

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseLaws
