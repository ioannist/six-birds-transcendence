import CSTTT.Targets.GenericHandoff.NominalHandoff
import CSTTT.Targets.GenericHandoff.POS04NominalProtocol

/-! Exact owning nominal-protocol adapter on every partial assignment.
The shared raw recipes supply withdrawal/source-presence data, and the target
closed C8 constructor uses exactly the derived operational primitive bindings.
AF/AO correspond to the newly defined nominal-qualified game readouts. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04NominalHandoff
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04ResourceRuntime
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def instructions (p : POS04ResourceRuntime.Protocol) : NominalHandoff.Instructions Cell Value KState Resource :=
  ⟨⟨ledger.initialBudget,ledger.actionCost,ledger.rechargePerAction⟩,
    (fun s t => pNum (index s) (index t)),[.recharge],⟨.literal p.sourcePresent⟩⟩

theorem specification_eq (p : POS04ResourceRuntime.Protocol) :
    NominalHandoff.specification (POS04RawHandoff.raw p) (instructions p) = POS04NominalProtocol.specification := rfl

theorem views_eq (p : POS04ResourceRuntime.Protocol) :
    NominalProtocol.views (POS04RawHandoff.raw p).frames = POS04NominalProtocol.tableViews := rfl

theorem laws (p : POS04ResourceRuntime.Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    NominalHandoff.Laws (POS04RawHandoff.raw p) (instructions p) a := ⟨rfl,(fun _ => rfl),(fun _ => rfl)⟩

theorem metadata_computed (m : RawLaneModel)
    (hc : Assigned.Complete phase2Dependencies (image m.assignment)) :
    (NominalHandoff.metadata (POS04RawHandoff.raw (protocol m)) (instructions (protocol m))).read
      (image m.assignment) = some (POS04NominalProtocol.withdrawalData m) := by
  have hl := POS04RegisterDynamics.cell_value (hc .maintenance (by decide))
  simp only [NominalHandoff.metadata,StaticView.read,StaticView.ofCell,Expr.eval,
    POS04RawHandoff.raw,POS04ResourceRuntime.runtime,POS04ResourceRuntime.bindings,instructions]
  rw [hl]
  rfl

theorem protocol_iff (m : RawLaneModel) :
    NominalHandoff.Pass (POS04RawHandoff.raw (protocol m)) (instructions (protocol m))
      (OwningHandoff.target (POS04RawHandoff.raw (protocol m)) m.assignment) ↔ POS04OperationalGame.Protocol m := by
  rw [POS04RawHandoff.target_eq]
  constructor
  · rintro ⟨wd,hwd,d,hd,hchecked⟩
    rw [views_eq] at hd
    have hc : Assigned.Complete phase2Dependencies (image m.assignment) := by
      intro k hk
      by_cases hm : image m.assignment k = none
      · have absent := (NominalProtocol.reader POS04NominalProtocol.tableViews).missing (image m.assignment) k
          ((POS04NominalProtocol.dependency_iff k).mpr hk) hm
        rw [absent] at hd
        contradiction
      · exact Option.isSome_iff_ne_none.mpr hm
    rw [metadata_computed m hc] at hwd
    have equal := Option.some.inj hwd
    subst wd
    exact (POS04NominalProtocol.pass_iff m).mp ⟨d,hd,hchecked⟩
  · intro hp
    have hc : Assigned.Complete phase2Dependencies (image m.assignment) :=
      fun k hk => POS04OperationalGame.protocol_complete m hp k (List.mem_append_right _ hk)
    refine ⟨POS04NominalProtocol.withdrawalData m,metadata_computed m hc,?_⟩
    rw [specification_eq,views_eq]
    exact (POS04NominalProtocol.pass_iff m).mpr hp

theorem full_iff_af (m : RawLaneModel) :
    NominalHandoff.FullAutonomy (POS04RawHandoff.raw (protocol m)) (instructions (protocol m)) m.assignment ↔ AF m := by
  change (NominalHandoff.Pass _ _ _ ∧ _) ↔ _
  rw [protocol_iff,← POS04HistoricalRuntimeProtocol.check_iff]
  simpa only [POS04RawHandoff.FullAutonomy,POS04RawHandoff.target_eq] using POS04RawHandoff.full_iff_af m

theorem operational_iff_ao (m : RawLaneModel) :
    NominalHandoff.OperationalAutonomy (POS04RawHandoff.raw (protocol m)) (instructions (protocol m)) m.assignment ↔ AO m := by
  change (NominalHandoff.Pass _ _ _ ∧ _) ↔ _
  rw [protocol_iff,← POS04HistoricalRuntimeProtocol.check_iff]
  simpa only [POS04RawHandoff.OperationalAutonomy,POS04RawHandoff.target_eq] using POS04RawHandoff.operational_iff_ao m

theorem baseline_readouts :
    NominalHandoff.FullAutonomy (POS04RawHandoff.raw (protocol baseline)) (instructions (protocol baseline)) baseline.assignment ∧
    NominalHandoff.OperationalAutonomy (POS04RawHandoff.raw (protocol baseline)) (instructions (protocol baseline)) baseline.assignment :=
  ⟨(full_iff_af _).mpr baseline_AF,(operational_iff_ao _).mpr baseline_AO⟩

/-- Direct negatives refute the defined nominal-qualified semantic readouts. -/
theorem source_present_no_readouts (m : RawLaneModel) (hs : m.sourcePresentAfterWithdrawal = true) :
    ¬ NominalHandoff.FullAutonomy (POS04RawHandoff.raw (protocol m)) (instructions (protocol m)) m.assignment ∧
    ¬ NominalHandoff.OperationalAutonomy (POS04RawHandoff.raw (protocol m)) (instructions (protocol m)) m.assignment := by
  have absent := NominalHandoff.source_present_no_pass (POS04RawHandoff.raw (protocol m))
    (instructions (protocol m)) (OwningHandoff.target (POS04RawHandoff.raw (protocol m)) m.assignment)
    (show _ from congrArg some hs)
  exact ⟨fun h => absent h.1,fun h => absent h.1⟩

end CSTTT.TargetTheory.GenericHandoff.POS04NominalHandoff
