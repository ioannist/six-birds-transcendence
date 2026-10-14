import CSTTT.Targets.GenericHandoff.ExecutionFrontier

/-! The executed codec boundary of G6d-4b. Separately typed source/target
readouts are interpreted on ONE execution and ONE assignment. Raw initial and
readout instructions may differ; rows and successor instructions cannot.
Finite alphabets are exact images of the executed frontier. This proves the
eight-field snapshot transport, NOT yet G1c's factor/record/route bridge laws,
nor the atomic corridor or final StrictTemporalLineage readout. -/
namespace CSTTT.TargetTheory.GenericHandoff.ExecutionSnapshotTransport
open RegisterInterpreter CSTTT.TransportTheory

structure Blueprint (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O P Residue Maintenance Stage Id History RouteId : Type) where
  acquisition : AcquisitionExecution.Bindings Cell Value R RV D A O Stage Id History RouteId
  readouts : RegisterFuture.Readouts Cell Value R RV P Residue Maintenance
  recipes : RegisterFuture.StepRecipes Cell Value R RV D A O P Residue Maintenance
  tickPeriod : Nat

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O P Q Residue Maintenance Stage Id History RouteId : Type) where
  execution : ResourceRuntime.Execution Cell Value R RV D A O
  source : Blueprint Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId
  target : Blueprint Cell Value R RV D A O Q Residue Maintenance Stage Id History RouteId
  schema : AcquisitionExecution.Schema Stage Id History RouteId
  audit : List (History × Nat)
  auditRoute : History × Nat → RouteId
  maps : SnapshotRawMaps P Q Residue Maintenance

variable {Cell R D A O P Q Residue Maintenance Stage Id History RouteId : Type}
    {Value : Cell → Type} {RV : R → Type}

def frame (execution : ResourceRuntime.Execution Cell Value R RV D A O)
    (blueprint : Blueprint Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (schema : AcquisitionExecution.Schema Stage Id History RouteId)
    (audit : List (History × Nat)) (auditRoute : History × Nat → RouteId) :
    ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId :=
  ⟨{blueprint.acquisition with execution := execution},blueprint.readouts,blueprint.recipes,
    blueprint.tickPeriod,audit,schema,auditRoute⟩
def source (raw : Raw Cell Value R RV D A O P Q Residue Maintenance Stage Id History RouteId) :=
  frame raw.execution raw.source raw.schema raw.audit raw.auditRoute
def target (raw : Raw Cell Value R RV D A O P Q Residue Maintenance Stage Id History RouteId) :=
  frame raw.execution raw.target raw.schema raw.audit raw.auditRoute

theorem shared_execution (raw : Raw Cell Value R RV D A O P Q Residue Maintenance Stage Id History RouteId) :
    (source raw).acquisition.execution = (target raw).acquisition.execution := rfl

variable [DecidableEq O] [DecidableEq Stage] [DecidableEq P] [DecidableEq Q]
    [DecidableEq Residue] [DecidableEq Maintenance]

def Valid (raw : Raw Cell Value R RV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  ExecutionFrontier.Valid (source raw) a ∧ ExecutionFrontier.Valid (target raw) a ∧
    ∀ hs : ExecutionFrontier.Ready (source raw) a, ∀ ht : ExecutionFrontier.Ready (target raw) a,
      SnapshotMapCheck raw.audit (ExecutionFrontier.observation (source raw) a hs)
        (ExecutionFrontier.observation (target raw) a ht) raw.maps

/-- Equality is in the frozen TemporalSignature type, including the proved
future proposition. No candidate snapshots or future models are parameters. -/
theorem frozen_transport
    (raw : Raw Cell Value R RV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hv : Valid raw a) :
    ∃ hs : ExecutionFrontier.Ready (source raw) a, ∃ ht : ExecutionFrontier.Ready (target raw) a,
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal (source raw)) a hs.2) ∧
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal (target raw)) a ht.2) ∧
      ∀ i : Audited raw.audit,
        transportFrozenSnapshot raw.audit (ExecutionFrontier.observation (source raw) a hs)
          (ExecutionFrontier.observation (target raw) a ht) raw.maps (hv.2.2 hs ht)
          (ExecutionFrontier.frozen (source raw) a hs i) = ExecutionFrontier.frozen (target raw) a ht i := by
  obtain ⟨hs,_,hfs,_,_⟩ := ExecutionFrontier.soundness (source raw) a hv.1
  obtain ⟨ht,_,hft,_,_⟩ := ExecutionFrontier.soundness (target raw) a hv.2.1
  refine ⟨hs,ht,hfs,hft,?_⟩
  intro i
  have hf : FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal (source raw)) a hs.2) =
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal (target raw)) a ht.2) :=
    propext ⟨fun _ => hft,fun _ => hfs⟩
  change transportFrozenSnapshot raw.audit (ExecutionFrontier.observation (source raw) a hs)
    (ExecutionFrontier.observation (target raw) a ht) raw.maps (hv.2.2 hs ht)
    (frozenSnapshot (RegisterFuture.future (ExecutionFrontier.temporal (source raw)) a hs.2)
      raw.audit (ExecutionFrontier.observation (source raw) a hs) i) =
    frozenSnapshot (RegisterFuture.future (ExecutionFrontier.temporal (target raw)) a ht.2)
      raw.audit (ExecutionFrontier.observation (target raw) a ht) i
  simp only [transportFrozenSnapshot,frozenSnapshot,snapshot_map_encode,
    TemporalSignature.mk.injEq,true_and,hf]
  exact congrArg TemporalSnapshotReadout.owner (hv.2.2 hs ht i.val i.property)

theorem representative_independence
    (raw : Raw Cell Value R RV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hv : Valid raw a)
    (hs : ExecutionFrontier.Ready (source raw) a) (ht : ExecutionFrontier.Ready (target raw) a)
    (i j : Audited raw.audit)
    (he : (ExecutionFrontier.observation (source raw) a hs i.val).predictive =
      (ExecutionFrontier.observation (source raw) a hs j.val).predictive) :
    (ExecutionFrontier.observation (target raw) a ht i.val).predictive =
      (ExecutionFrontier.observation (target raw) a ht j.val).predictive := by
  have hi := congrArg TemporalSnapshotReadout.predictive (hv.2.2 hs ht i.val i.property)
  have hj := congrArg TemporalSnapshotReadout.predictive (hv.2.2 hs ht j.val j.property)
  exact hi.symm.trans ((congrArg raw.maps.predictive he).trans hj)

theorem missing_atomic_view
    (raw : Raw Cell Value R RV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hm : raw.source.acquisition.events.read a = none) : ¬ Valid raw a :=
  fun hv => ExecutionFrontier.missing_atomic_view (source raw) a hm hv.1

theorem map_field_guard {X : Type}
    (raw : Raw Cell Value R RV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready (source raw) a)
    (ht : ExecutionFrontier.Ready (target raw) a) (i : Audited raw.audit)
    (field : TemporalSnapshotReadout Q Residue Maintenance → X)
    (bad : field (mapSnapshotReadout raw.maps (ExecutionFrontier.observation (source raw) a hs i.val)) ≠
      field (ExecutionFrontier.observation (target raw) a ht i.val)) : ¬ Valid raw a :=
  fun hv => bad (congrArg field (hv.2.2 hs ht i.val i.property))
end CSTTT.TargetTheory.GenericHandoff.ExecutionSnapshotTransport
