import CSTTT.Targets.GenericHandoff.RuntimeLineage
import CSTTT.Targets.GenericHandoff.HistoricalSparseRuntime

/-! Public package/runtime binding (TTH-06, mathematical addition).
ONE staged target is read by package, historical games, actual lineage and
endpoint. Resource instructions and schemas come from the lineage runtime.
Historical source support is deliberately different from funded source
execution. Target agreement is a checked commuting span through one typed
frame, on every run and positive branch. This is not the final RawHandoff:
endpoint/factor/record presentation coherence still needs its public binding. -/
namespace CSTTT.TargetTheory.GenericHandoff.PublicRuntime
open RegisterInterpreter
structure Raw (SC Cell : Type) (SourceValue : SC → Type) (Value : Cell → Type)
    (R S T : Type) (RV : R → Type) (SV : S → Type) (TV : T → Type)
    (D A O P Q SourceFactor HistoricalTargetFactor Factor Resource Residue Maintenance Endpoint Stage Id History RouteId : Type) where
  package : DispatchedPackage.Raw SC Cell SourceValue Value
  lineage : RuntimeLineage.Raw Cell Value R S T RV SV TV D A O P Q Factor Resource Residue Maintenance Endpoint Stage Id History RouteId
  historicalExecution : ResourceRuntime.Execution Cell Value R RV D A O
  historical : HistoricalAcquisition.Bindings Cell Value R RV D A SourceFactor HistoricalTargetFactor Stage Id History RouteId
  runCells : (k : Cell) → Expr Cell Value R RV Unit (Value k)
variable {SC Cell R S T D A O P Q SourceFactor HistoricalTargetFactor Factor Resource Residue Maintenance Endpoint Stage Id History RouteId : Type}
  {SourceValue : SC → Type} {Value : Cell → Type} {RV : R → Type} {SV : S → Type} {TV : T → Type}
local notation "Model" => Raw SC Cell SourceValue Value R S T RV SV TV D A O P Q SourceFactor HistoricalTargetFactor Factor Resource Residue Maintenance Endpoint Stage Id History RouteId

def autonomy (raw : Model) : HistoricalPackageRuntime.Raw SC Cell SourceValue Value R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId where
  package := raw.package
  resourceSchema := RuntimeComponents.resourceSchema raw.lineage.schema
  acquisitionSchema := RuntimeComponents.acquisitionSchema raw.lineage.schema
  execution := raw.historicalExecution
  resource := raw.lineage.runtime.resource
  historical := raw.historical
  runCells := raw.runCells
variable [DecidableEq Cell]
def target (raw : Model) (a : Assignment SC SourceValue) : Assignment Cell Value :=
  DispatchedPackage.global raw.package a
/-- Neither lineage nor endpoint receives an independent target assignment. -/
def lineageAssignment (raw : Model) (a : Assignment SC SourceValue) : Assignment Cell Value := target raw a

theorem package_target (raw : Model) (a : Assignment SC SourceValue) :
    HistoricalPackageRuntime.target (autonomy raw) a = target raw a := rfl
theorem lineage_target (raw : Model) (a : Assignment SC SourceValue) : lineageAssignment raw a = target raw a := rfl
theorem endpoint_target (raw : Model) (a : Assignment SC SourceValue) :
    AcquisitionEndpoint.Readout raw.lineage.endpoint (lineageAssignment raw a) ↔
      AcquisitionEndpoint.Readout raw.lineage.endpoint (HistoricalPackageRuntime.target (autonomy raw) a) := Iff.rfl
omit [DecidableEq Cell] in
theorem resource_instructions (raw : Model) :
    (HistoricalPackageRuntime.resources (autonomy raw)).toBindings = raw.lineage.runtime.resource := rfl
omit [DecidableEq Cell] in
theorem resource_schema (raw : Model) : (autonomy raw).resourceSchema =
    RuntimeComponents.resourceSchema raw.lineage.schema := rfl
omit [DecidableEq Cell] in
theorem acquisition_schema (raw : Model) : (autonomy raw).acquisitionSchema =
    RuntimeComponents.acquisitionSchema raw.lineage.schema := rfl
/-- These equations hold on ALL runs, including unfunded contexts, independently
of whether a game exists. Both sides use the SAME resource instructions. -/
theorem resource_closed_iff (raw : Model) (a : Assignment SC SourceValue) (r : Registers R RV) :
    ResourceRuntime.ResourceClosed (autonomy raw).resourceSchema
      (HistoricalPackageRuntime.resources (autonomy raw)) (target raw a) r ↔
    ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema raw.lineage.schema)
      (RuntimeComponents.resources raw.lineage.runtime) (lineageAssignment raw a) r := Iff.rfl
theorem factor_inside_iff (raw : Model) (a : Assignment SC SourceValue) (r : Registers R RV) :
    ResourceRuntime.Inside (autonomy raw).resourceSchema
      (HistoricalPackageRuntime.resources (autonomy raw)) (target raw a) r ↔
    ResourceRuntime.Inside (RuntimeComponents.resourceSchema raw.lineage.schema)
      (RuntimeComponents.resources raw.lineage.runtime) (lineageAssignment raw a) r := Iff.rfl

def historicalLink (raw : Model) : ExecutionLink.Raw Cell Value T R TV RV D A O :=
  ⟨raw.lineage.target.acquisition.execution,raw.historicalExecution,raw.lineage.targetEmbedding⟩
def TargetExecutionCoherent (raw : Model) (a : Assignment SC SourceValue) : Prop :=
  ExecutionLink.Pass (RuntimeLineage.targetLink raw.lineage) (target raw a) ∧
    ExecutionLink.Pass (historicalLink raw) (target raw a)

theorem frame_eq (raw : Model) (a : Assignment SC SourceValue)
    (hl : ExecutionLink.Ready (RuntimeLineage.targetLink raw.lineage) (target raw a))
    (hh : ExecutionLink.Ready (historicalLink raw) (target raw a)) (x : Registers T TV) :
    ExecutionLink.embed (RuntimeLineage.targetLink raw.lineage) (target raw a) hl x =
      ExecutionLink.embed (historicalLink raw) (target raw a) hh x := rfl

theorem rows_eq (raw : Model) (a : Assignment SC SourceValue)
    (hl : ExecutionLink.Ready (RuntimeLineage.targetLink raw.lineage) (target raw a))
    (hh : ExecutionLink.Ready (historicalLink raw) (target raw a))
    (ll : ExecutionLink.Laws (RuntimeLineage.targetLink raw.lineage) (target raw a) hl)
    (lh : ExecutionLink.Laws (historicalLink raw) (target raw a) hh)
    (x : Registers T TV) (d : D) (act : A) :
    ExecutionLink.rows raw.historicalExecution (target raw a)
        (ExecutionLink.embed (historicalLink raw) (target raw a) hh x) d act =
      ExecutionLink.rows raw.lineage.runtime.execution (target raw a)
        (ExecutionLink.embed (RuntimeLineage.targetLink raw.lineage) (target raw a) hl x) d act :=
  (lh.rows x d act).trans (ll.rows x d act).symm

/-- Whole counter/ledger/record/provenance updates, for EVERY actual positive
branch. Positive-support coverage supplies outcome-domain membership. -/
theorem positive_successor_eq (raw : Model) (a : Assignment SC SourceValue)
    (hl : ExecutionLink.Ready (RuntimeLineage.targetLink raw.lineage) (target raw a))
    (hh : ExecutionLink.Ready (historicalLink raw) (target raw a))
    (ll : ExecutionLink.Laws (RuntimeLineage.targetLink raw.lineage) (target raw a) hl)
    (lh : ExecutionLink.Laws (historicalLink raw) (target raw a) hh)
    (x : Registers T TV) (d : D) (hd : d ∈ raw.lineage.target.acquisition.execution.disturbances)
    (act : A) (ha : act ∈ raw.lineage.target.acquisition.execution.actions) (o : O)
    (hp : StrategyGame.PositiveSupport (ExecutionLink.rows raw.lineage.target.acquisition.execution (target raw a)) x d act o) :
    ExecutionLink.update raw.historicalExecution (target raw a) hh.2.1
        (ExecutionLink.embed (historicalLink raw) (target raw a) hh x) d act o =
      ExecutionLink.update raw.lineage.runtime.execution (target raw a) hl.2.1
        (ExecutionLink.embed (RuntimeLineage.targetLink raw.lineage) (target raw a) hl x) d act o :=
  (ExecutionLink.positive_successor _ _ hh lh x d hd act ha o hp).symm.trans
    (ExecutionLink.positive_successor _ _ hl ll x d hd act ha o hp)

theorem every_supported_word_eq (raw : Model) (a : Assignment SC SourceValue)
    (hl : ExecutionLink.Ready (RuntimeLineage.targetLink raw.lineage) (target raw a))
    (hh : ExecutionLink.Ready (historicalLink raw) (target raw a))
    (ll : ExecutionLink.Laws (RuntimeLineage.targetLink raw.lineage) (target raw a) hl)
    (lh : ExecutionLink.Laws (historicalLink raw) (target raw a) hh)
    (x : Registers T TV) (word : List (D × A × O))
    (hw : ExecutionLink.Supported raw.lineage.target.acquisition.execution (target raw a) hl.1 x word) :
    ExecutionLink.fold raw.historicalExecution (target raw a) hh.2.1
        (ExecutionLink.embed (historicalLink raw) (target raw a) hh x) word =
      ExecutionLink.fold raw.lineage.runtime.execution (target raw a) hl.2.1
        (ExecutionLink.embed (RuntimeLineage.targetLink raw.lineage) (target raw a) hl x) word :=
  (ExecutionLink.supported_fold _ _ hh lh x word hw).symm.trans
    (ExecutionLink.supported_fold _ _ hl ll x word hw)

/-- Withdrawal roles, source absence, ownership and prices are not separately
supplied interpretations. The same assigned instructions are used in both. -/
theorem withdrawal_iff (raw : Model) (a : Assignment SC SourceValue) :
    ResourceRuntime.WithdrawalCheck (autonomy raw).resourceSchema
      (HistoricalPackageRuntime.resources (autonomy raw)) (target raw a) ↔
    ResourceRuntime.WithdrawalCheck (RuntimeComponents.resourceSchema raw.lineage.schema)
      (RuntimeComponents.resources raw.lineage.runtime) (lineageAssignment raw a) := Iff.rfl

theorem legal_iff (raw : Model) (a : Assignment SC SourceValue)
    (hl : ExecutionLink.Ready (RuntimeLineage.targetLink raw.lineage) (target raw a))
    (hh : ExecutionLink.Ready (historicalLink raw) (target raw a))
    (ll : ExecutionLink.Laws (RuntimeLineage.targetLink raw.lineage) (target raw a) hl)
    (lh : ExecutionLink.Laws (historicalLink raw) (target raw a) hh)
    (r : Registers R RV) (d : D) (act : A) :
    ResourceRuntime.Legal (autonomy raw).resourceSchema
      (HistoricalPackageRuntime.resources (autonomy raw)) (target raw a) r d act ↔
    ResourceRuntime.Legal (RuntimeComponents.resourceSchema raw.lineage.schema)
      (RuntimeComponents.resources raw.lineage.runtime) (lineageAssignment raw a) r d act := by
  have hd : raw.historicalExecution.disturbances = raw.lineage.runtime.execution.disturbances :=
    lh.disturbances.trans ll.disturbances.symm
  have ha : raw.historicalExecution.actions = raw.lineage.runtime.execution.actions :=
    lh.actions.trans ll.actions.symm
  change (d ∈ raw.historicalExecution.disturbances ∧ act ∈ raw.historicalExecution.actions ∧ _) ↔
    (d ∈ raw.lineage.runtime.execution.disturbances ∧ act ∈ raw.lineage.runtime.execution.actions ∧ _)
  rw [hd,ha]
  rfl

/-- Representation-sensitive legality also agrees on the common target frame;
no ordering or duplicate-freedom requirement is introduced. -/
theorem strict_sparse_iff (raw : Model) (a : Assignment SC SourceValue)
    (hl : ExecutionLink.Ready (RuntimeLineage.targetLink raw.lineage) (target raw a))
    (hh : ExecutionLink.Ready (historicalLink raw) (target raw a))
    (ll : ExecutionLink.Laws (RuntimeLineage.targetLink raw.lineage) (target raw a) hl)
    (lh : ExecutionLink.Laws (historicalLink raw) (target raw a) hh)
    (x : Registers T TV) (d : D) (act : A) :
    StrictSparseGame.StrictSparse (ExecutionLink.rows raw.historicalExecution (target raw a)
      (ExecutionLink.embed (historicalLink raw) (target raw a) hh x) d act) ↔
    StrictSparseGame.StrictSparse (ExecutionLink.rows raw.lineage.runtime.execution (target raw a)
      (ExecutionLink.embed (RuntimeLineage.targetLink raw.lineage) (target raw a) hl x) d act) := by
  rw [rows_eq raw a hl hh ll lh]

theorem missing_target_frame_rejected (raw : Model) (a : Assignment SC SourceValue)
    (r : R) (k : Cell) (hk : k ∈ (raw.lineage.targetEmbedding r).dependencies)
    (hm : target raw a k = none) : ¬ TargetExecutionCoherent raw a :=
  fun h => ExecutionLink.missing_embedding_rejected (historicalLink raw) _ k r hk hm h.2

theorem mismatched_historical_successor_rejected (raw : Model) (a : Assignment SC SourceValue)
    (h : ExecutionLink.Ready (historicalLink raw) (target raw a))
    (x : Registers T TV) (d : D) (hd : d ∈ raw.lineage.target.acquisition.execution.disturbances)
    (act : A) (ha : act ∈ raw.lineage.target.acquisition.execution.actions)
    (o : O) (ho : o ∈ raw.lineage.target.acquisition.execution.outcomes)
    (bad : ExecutionLink.embed (historicalLink raw) (target raw a) h
        (ExecutionLink.update raw.lineage.target.acquisition.execution (target raw a) h.1 x d act o) ≠
      ExecutionLink.update raw.historicalExecution (target raw a) h.2.1
        (ExecutionLink.embed (historicalLink raw) (target raw a) h x) d act o) :
    ¬ TargetExecutionCoherent raw a :=
  fun hc => ExecutionLink.successor_mismatch_rejected (historicalLink raw) _ h x d hd act ha o ho bad hc.2

theorem missing_historical_row_rejected (raw : Model) (a : Assignment SC SourceValue)
    (k : Cell) (hk : k ∈ raw.historicalExecution.row.dependencies)
    (hm : target raw a k = none) : ¬ TargetExecutionCoherent raw a :=
  fun h => ExecutionLink.missing_target_row_rejected (historicalLink raw) _ k hk hm h.2
theorem mismatched_historical_rows_rejected (raw : Model) (a : Assignment SC SourceValue)
    (h : ExecutionLink.Ready (historicalLink raw) (target raw a))
    (x : Registers T TV) (d : D) (act : A)
    (bad : ExecutionLink.rows raw.historicalExecution (target raw a)
      (ExecutionLink.embed (historicalLink raw) (target raw a) h x) d act ≠
      ExecutionLink.rows raw.lineage.target.acquisition.execution (target raw a) x d act) :
    ¬ TargetExecutionCoherent raw a :=
  fun hc => ExecutionLink.rows_mismatch_rejected (historicalLink raw) _ h x d act bad hc.2
end CSTTT.TargetTheory.GenericHandoff.PublicRuntime
