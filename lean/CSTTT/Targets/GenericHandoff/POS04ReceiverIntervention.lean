import CSTTT.Targets.GenericHandoff.ReceiverIntervention
import CSTTT.Targets.GenericHandoff.POS04ReceiverContent

/-! Every-partial-assignment source-absence counterfactual. The same owning
model and receiver recipe are rerun after changing only the raw source-present
field. Latent factor decoding and actual receiver initialization remain exact,
but activation rejects. No frozen fixture or family predicate is changed. -/

namespace CSTTT.TargetTheory.GenericHandoff.POS04ReceiverIntervention
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def erase (x : Value Cell.receiverInput) : Value Cell.receiverInput :=
  {x with sourcePresent := false}
def withoutSource (a : Assigned.Assignment) : Assigned.Assignment :=
  ReceiverIntervention.withoutSource POS04ExecutionFrontier.receiverView erase a

theorem erasure_law : ReceiverIntervention.ErasureLaw POS04ExecutionFrontier.receiverView erase := by
  intro x
  rfl

theorem latent_factor (a : Assigned.Assignment) (tag : Tag) :
    TemporalFactorCells.decoded (POS04TemporalFactor.bindings tag) (withoutSource a) =
    TemporalFactorCells.decoded (POS04TemporalFactor.bindings tag) a := by
  simp [TemporalFactorCells.decoded,POS04TemporalFactor.bindings,CellView.read,
    withoutSource,ReceiverIntervention.withoutSource,POS04ExecutionFrontier.receiverView,
    GenericHandoff.put,erase,Option.map_map,Function.comp_def]

theorem complete_iff (a : Assigned.Assignment) (scope : List Cell) :
    Assigned.Complete scope (withoutSource a) ↔ Assigned.Complete scope a :=
  ReceiverIntervention.complete_iff POS04ExecutionFrontier.receiverView erase a scope

theorem initial_ready_iff (a : Assigned.Assignment) :
    RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram (withoutSource a) ↔
    RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram a :=
  ReceiverIntervention.initial_ready_iff POS04ExecutionFrontier.receiverView erase a _

theorem target_ready_iff (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment) :
    TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target (withoutSource a) ↔
    TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target a := by
  change TemporalRuntimeCoherence.Ready (POS04TemporalCoherence.raw .target) (withoutSource a) ↔
    TemporalRuntimeCoherence.Ready (POS04TemporalCoherence.raw .target) a
  unfold TemporalRuntimeCoherence.Ready
  rw [show TemporalFactorCells.decoded (POS04TemporalCoherence.raw .target).bindings (withoutSource a) =
      TemporalFactorCells.decoded (POS04TemporalCoherence.raw .target).bindings a from latent_factor a .target]
  simp only [withoutSource,ReceiverIntervention.future_ready_iff,ReceiverIntervention.complete_iff]

/-- Every raw register evaluation remains identical, even on incomplete
assignments. Only source presence changes; the reset uses the same funding. -/
theorem evaluation_unchanged (a : Assigned.Assignment)
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId)
    (reg : POS04RegisterDynamics.Register) :
    RegisterInitialization.evaluate POS04ReceiverContent.instructions.resetProgram (withoutSource a) input reg =
    RegisterInitialization.evaluate POS04ReceiverContent.instructions.resetProgram a input reg := by
  cases reg
  all_goals try rfl
  change ((withoutSource a) Cell.receiverInput).map (fun r => r.funded) = (a Cell.receiverInput).map (fun r => r.funded)
  simp only [withoutSource,ReceiverIntervention.withoutSource,POS04ExecutionFrontier.receiverView,put_same,Option.map_map]
  rfl

theorem initial_unchanged (a : Assigned.Assignment)
    (ha : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram a)
    (hb : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram (withoutSource a))
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    RegisterInitialization.initial POS04ReceiverContent.instructions.resetProgram (withoutSource a) hb input =
    RegisterInitialization.initial POS04ReceiverContent.instructions.resetProgram a ha input := by
  funext reg
  apply Option.some.inj
  rw [← RegisterInitialization.initial_eq,← RegisterInitialization.initial_eq]
  exact evaluation_unchanged a input reg

theorem prepared_run_unchanged (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment)
    (ha : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram a)
    (hb : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram (withoutSource a))
    (hta : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target a)
    (htb : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target (withoutSource a))
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverContent.receivedRun (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (withoutSource a) hb htb input =
    ReceiverContent.receivedRun (POS04RawHandoff.raw p) POS04ReceiverContent.instructions a ha hta input := by
  change TemporalRuntimeCoherence.project (POS04TemporalCoherence.raw .target) (withoutSource a) htb _ =
    TemporalRuntimeCoherence.project (POS04TemporalCoherence.raw .target) a hta _
  rw [POS04TemporalCoherence.project_eq,POS04TemporalCoherence.project_eq,initial_unchanged a ha hb input]

theorem no_reception (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment)
    (hi : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram (withoutSource a))
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target (withoutSource a))
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverContent.receive (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (withoutSource a) hi ht input = none ∧
    ReceiverContent.receivedClass (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (withoutSource a) hi ht input = none :=
  ReceiverIntervention.no_reception (POS04RawHandoff.raw p) POS04ReceiverContent.instructions erase erasure_law a hi ht input

theorem not_faithful (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment)
    (hi : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram (withoutSource a))
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target (withoutSource a)) :
    ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (withoutSource a) hi ht :=
  ReceiverIntervention.not_faithful (POS04RawHandoff.raw p) POS04ReceiverContent.instructions erase erasure_law a hi ht

/-- Readiness is transported from the original receiver before rerunning it.
The unchanged prepared run and rejected actual reception coexist. -/
theorem rerun_rejected (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment)
    (hi : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target a) :
    ∃ hib : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram (withoutSource a),
      ∃ htb : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target (withoutSource a),
        (∀ input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId,
          ReceiverContent.receivedRun (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (withoutSource a) hib htb input =
            ReceiverContent.receivedRun (POS04RawHandoff.raw p) POS04ReceiverContent.instructions a hi ht input ∧
          ReceiverContent.receive (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (withoutSource a) hib htb input = none ∧
          ReceiverContent.receivedClass (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (withoutSource a) hib htb input = none) ∧
        ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (withoutSource a) hib htb := by
  let hib := (initial_ready_iff a).mpr hi
  let htb := (target_ready_iff p a).mpr ht
  exact ⟨hib,htb,(fun input => ⟨prepared_run_unchanged p a hi hib ht htb input,no_reception p a hib htb input⟩),
    not_faithful p a hib htb⟩

theorem baseline_rerun_rejected (p : POS04ResourceRuntime.Protocol) :
    ∃ hib : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram (withoutSource canonical),
      ∃ htb : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target (withoutSource canonical),
        ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (withoutSource canonical) hib htb := by
  obtain ⟨hib,htb,_,negative⟩ := rerun_rejected p canonical
    (POS04ReceiverContent.ready canonical (canonical_complete _))
    (POS04ReceiverContent.target_ready p canonical (canonical_complete _))
  exact ⟨hib,htb,negative⟩

end CSTTT.TargetTheory.GenericHandoff.POS04ReceiverIntervention
