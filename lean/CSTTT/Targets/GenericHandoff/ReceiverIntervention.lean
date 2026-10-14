import CSTTT.Targets.GenericHandoff.ReceiverContent

/-! Raw source-presence intervention and actual receiver rerun. Erasure is a
primitive value transformation checked against the existing receiver view;
absence is never replaced by a default. Generic laws preserve projected
receiver fields and all other cells. POS04 additionally checks latent factor
and actual prepared-run preservation. This remains a receiver component. -/

namespace CSTTT.TargetTheory.GenericHandoff.ReceiverIntervention
open RegisterInterpreter
variable {Cell : Type} {Value : Cell → Type} [DecidableEq Cell]

def withoutSource (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) (a : Assignment Cell Value) : Assignment Cell Value :=
  put a v.cell ((a v.cell).map erase)

def ErasureLaw (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) : Prop :=
  ∀ x, v.project (erase x) = {v.project x with sourcePresent := false}

theorem missing_unchanged (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) (a : Assignment Cell Value) (k : Cell) :
    withoutSource v erase a k = none ↔ a k = none := by
  by_cases hk : k = v.cell
  · subst k; simp [withoutSource]
  · simp [withoutSource,put_other a v.cell k _ hk]

theorem other_unchanged (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) (a : Assignment Cell Value) (k : Cell) (hk : k ≠ v.cell) :
    withoutSource v erase a k = a k := put_other _ _ _ _ hk

theorem complete_iff (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) (a : Assignment Cell Value) (scope : List Cell) :
    Complete scope (withoutSource v erase a) ↔ Complete scope a := by
  have presence (k : Cell) : (withoutSource v erase a k).isSome = (a k).isSome := by
    by_cases hk : k = v.cell
    · subst k; simp [withoutSource]
    · rw [other_unchanged v erase a k hk]
  simp only [Complete,presence]

theorem initial_ready_iff {R Selector : Type} {RV : R → Type}
    (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) (a : Assignment Cell Value)
    (program : RegisterInitialization.InitialProgram Cell Value R RV Selector) :
    RegisterInitialization.Ready program (withoutSource v erase a) ↔ RegisterInitialization.Ready program a := by
  simp only [RegisterInitialization.Ready,complete_iff]

theorem program_ready_iff {R Env : Type} {RV : R → Type}
    (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) (a : Assignment Cell Value)
    (program : Program Cell Value R RV Env) :
    ProgramReady program (withoutSource v erase a) ↔ ProgramReady program a := by
  simp only [ProgramReady,complete_iff]

theorem future_ready_iff {R D A O P Residue Maintenance : Type} {RV : R → Type}
    (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) (a : Assignment Cell Value)
    (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance) :
    RegisterFuture.RawReady raw (withoutSource v erase a) ↔ RegisterFuture.RawReady raw a := by
  simp only [RegisterFuture.RawReady,complete_iff,program_ready_iff]

theorem receiver_read (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) (law : ErasureLaw v erase) (a : Assignment Cell Value) :
    v.read (withoutSource v erase a) =
      (v.read a).map (fun x => {x with sourcePresent := false}) := by
  simp only [CellView.read,withoutSource,put_same,Option.map_map]
  apply congrArg (fun f => (a v.cell).map f)
  funext x
  exact law x

theorem receiver_absent (v : CellView Cell Value AcquisitionExecution.Receiver)
    (erase : Value v.cell → Value v.cell) (law : ErasureLaw v erase)
    (a : Assignment Cell Value) (receiver : AcquisitionExecution.Receiver)
    (read : v.read (withoutSource v erase a) = some receiver) : receiver.sourcePresent = false := by
  rw [receiver_read v erase law a] at read
  cases hr : v.read a with
  | none => simp [hr] at read
  | some value =>
    have eq : {value with sourcePresent := false} = receiver := by simpa [hr] using read
    rw [← eq]

end CSTTT.TargetTheory.GenericHandoff.ReceiverIntervention



namespace CSTTT.TargetTheory.GenericHandoff.ReceiverIntervention
open RegisterInterpreter
variable {Cell S A O HF Route Stage Id Owner : Type} {Value : Cell → Type}

theorem decoded_receiver (v : AcquisitionEndpoint.Bindings Cell Value S A O HF Route Stage Id Owner)
    (a : Assignment Cell Value) (data : AcquisitionEndpoint.Data S A O HF Route Stage Id Owner)
    (decoded : AcquisitionEndpoint.decoded v a = some data) : v.receiver.read a = some data.receiver := by
  unfold AcquisitionEndpoint.decoded at decoded
  cases hs : TemporalFactorCells.decoded v.source a <;> simp_all
  cases ht : TemporalFactorCells.decoded v.target a <;> simp_all
  cases he : v.events.read a <;> simp_all
  cases hr : v.receiver.read a <;> simp_all
  cases decoded
  rfl

variable {SC R SR TR H D P Q Factor Resource Endpoint : Type}
  {SourceValue : SC → Type} {RV : R → Type} {SRV : SR → Type} {TRV : TR → Type}
  [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route]
  [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner]
local notation "Model" => OwningHandoff.RawHandoff SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint
local notation "Recipe" => ReceiverContent.Instructions Cell TR S O H Id Route Value TRV

theorem no_reception (m : Model) (r : Recipe)
    (erase : Value m.frames.receiver.cell → Value m.frames.receiver.cell)
    (law : ErasureLaw m.frames.receiver erase) (a : Assignment Cell Value)
    (hi : RegisterInitialization.Ready r.resetProgram (withoutSource m.frames.receiver erase a))
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target (withoutSource m.frames.receiver erase a))
    (input : HistoricalAcquisition.ReceiverInput S H Id Route) :
    ReceiverContent.receive m r (withoutSource m.frames.receiver erase a) hi ht input = none ∧
    ReceiverContent.receivedClass m r (withoutSource m.frames.receiver erase a) hi ht input = none := by
  cases hd : AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings (withoutSource m.frames.receiver erase a) with
  | none => exact ReceiverContent.missing_endpoint hd input
  | some data =>
    have read := decoded_receiver _ _ data hd
    have absent := receiver_absent m.frames.receiver erase law a data.receiver read
    exact ⟨ReceiverContent.source_absent hd absent input,ReceiverContent.source_absent_class hd absent input⟩

theorem not_faithful (m : Model) (r : Recipe)
    (erase : Value m.frames.receiver.cell → Value m.frames.receiver.cell)
    (law : ErasureLaw m.frames.receiver erase) (a : Assignment Cell Value)
    (hi : RegisterInitialization.Ready r.resetProgram (withoutSource m.frames.receiver erase a))
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target (withoutSource m.frames.receiver erase a)) :
    ¬ ReceiverContent.ContentFaithful m r (withoutSource m.frames.receiver erase a) hi ht := by
  cases hd : AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings (withoutSource m.frames.receiver erase a) with
  | none => exact ReceiverContent.missing_endpoint_not_faithful hd
  | some data =>
    have read := decoded_receiver _ _ data hd
    exact ReceiverContent.source_absent_not_faithful hd (receiver_absent m.frames.receiver erase law a data.receiver read)

end CSTTT.TargetTheory.GenericHandoff.ReceiverIntervention
