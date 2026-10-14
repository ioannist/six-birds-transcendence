import CSTTT.Targets.GenericHandoff.NativeComposition.NativeResourceGame

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter AcquisitionExecution

def removeTargetRecharge (i : Input) : Input :=
  {i with temporal := {i.temporal with resource := {i.temporal.resource with rechargeAvailable := false}}}
def removeSourcePresence (i : Input) : Input :=
  {i with receiver := {i.receiver with sourcePresent := false}}

/-- Target-only intervention preserves the whole actual copied source table,
including its owner, funding, histories and rows, on every partial assignment. -/
theorem recharge_control_preserves_source (a : Assignment Owner MemoryValue) :
    sourceInputs (intervene removeTargetRecharge a) = sourceInputs a :=
  intervention_source removeTargetRecharge a

theorem presence_control_preserves_source (a : Assignment Owner MemoryValue) :
    sourceInputs (intervene removeSourcePresence a) = sourceInputs a :=
  intervention_source removeSourcePresence a

/-- Actual received target funding disables every supported post-exit outcome.
The source history is not changed or used as substitute target maintenance. -/
theorem unfunded_target_no_entry (cell sourceOwner : Owner) (start stride : Nat)
    (cfg : Schema Stage Bool History Route) (a : Assignment Owner MemoryValue)
    (hr : Ready (acquisition cell sourceOwner start stride) a)
    (p : Input × Input) (hp : a cell=some p) (bad : p.1.temporal.resource.rechargeAvailable=false)
    (entry : Registers) : ¬ Entry cfg (acquisition cell sourceOwner start stride) a hr entry := by
  rintro ⟨_,rid,arrived,routes,da,o,ha,_,_,_,_,_,hs,_⟩
  rcases ha with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,source,_,he⟩
  rw [he,acquisition_receive cell sourceOwner start stride a hr p hp] at hs
  rw [StrategyGame.PositiveSupport,acquisition_rows cell sourceOwner start stride a p hp] at hs
  simp only [pack,received,ite_true,TemporalFactorRules.actualRows,TemporalFactorRules.enabled,bad,
    Bool.and_false,Bool.false_and] at hs
  obtain ⟨w,hw,_⟩ := hs
  simp at hw

theorem source_absent_no_entry (cell sourceOwner : Owner) (start stride : Nat)
    (cfg : Schema Stage Bool History Route) (a : Assignment Owner MemoryValue)
    (hr : Ready (acquisition cell sourceOwner start stride) a)
    (p : Input × Input) (hp : a cell=some p) (bad : p.1.receiver.sourcePresent=false)
    (entry : Registers) : ¬ Entry cfg (acquisition cell sourceOwner start stride) a hr entry := by
  rintro ⟨_,_,_,_,_,_,ha,_⟩
  rcases ha with ⟨_,_,_,_,receiver,_,_,_,_,hrecv,_,_,_,hactive,_⟩
  have he : p.1.receiver=receiver := Option.some.inj (by simpa [acquisition,CellView.read,hp] using hrecv)
  have hsource := hactive.1
  rw [← he,bad] at hsource
  contradiction

def rechargeCut := intervene removeTargetRecharge nativeAssignment
def sourceCut := intervene removeSourcePresence nativeAssignment

theorem recharge_cut_ready : Ready secondAcquisition rechargeCut :=
  acquisition_ready false true 2 2 rechargeCut rfl

theorem source_cut_ready : Ready secondAcquisition sourceCut :=
  acquisition_ready false true 2 2 sourceCut rfl

theorem recharge_cut_no_actual_entry (hr : Ready secondAcquisition rechargeCut) (entry : Registers) :
    ¬ Entry secondSchema secondAcquisition rechargeCut hr entry :=
  unfunded_target_no_entry false true 2 2 secondSchema rechargeCut hr
    (removeTargetRecharge (roundInput 2),roundInput 1) rfl rfl entry

theorem source_cut_no_actual_entry (hr : Ready secondAcquisition sourceCut) (entry : Registers) :
    ¬ Entry secondSchema secondAcquisition sourceCut hr entry :=
  source_absent_no_entry false true 2 2 secondSchema sourceCut hr
    (removeSourcePresence (roundInput 2),roundInput 1) rfl rfl entry

/-- A game requires a real entry. These controls directly refute the defined
operational readout, regardless of the resource-ready proof supplied. -/
theorem recharge_cut_no_game (hr : ResourceRuntime.Ready finalResources rechargeCut)
    (ha : Ready secondAcquisition rechargeCut) :
    ¬ ResourceRuntime.OperationalReadout finalResourceSchema finalResources rechargeCut hr
      (Entry secondSchema secondAcquisition rechargeCut ha) := by
  intro h
  obtain ⟨entry,he⟩ := h.2.1
  exact recharge_cut_no_actual_entry ha entry he

theorem source_cut_no_game (hr : ResourceRuntime.Ready finalResources sourceCut)
    (ha : Ready secondAcquisition sourceCut) :
    ¬ ResourceRuntime.OperationalReadout finalResourceSchema finalResources sourceCut hr
      (Entry secondSchema secondAcquisition sourceCut ha) := by
  intro h
  obtain ⟨entry,he⟩ := h.2.1
  exact source_cut_no_actual_entry ha entry he

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
