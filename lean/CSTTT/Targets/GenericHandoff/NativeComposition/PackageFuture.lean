import CSTTT.Targets.GenericHandoff.NativeComposition.ClosedPackage

/-! Each actual shared-package native selection independently supplies a full
C6 future for every finite word and unbounded register context. The fixed raw
instructions consume the actual bundle, and readiness rejects missing cells. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackageFuture
open RegisterInterpreter NativePackageBundle

def value (copy : Bool) (_ : Owner) (p : Bundle × Bundle) : Input := (select copy p).native
def inputs (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) : Assignment Owner NativeComposition.Value :=
  CellReindex.pullback id (value copy) a
def raw (cell : Owner) (copy : Bool) (owner : Owner) (names : Owner → CarrierId) :
    RegisterFuture.Raw Owner NativePackageBundle.Value Unit (fun _ => Frame.State) Unit Bool Factor Frame.Predictive Frame.Residue Bool :=
  FutureCellReindex.raw (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
    id (value copy) (Frame.raw cell false owner names)

theorem selected_input (cell : Owner) (copy : Bool) :
    inputs copy NativePackageBundle.canonical cell=some (AvailabilityPublication.selected cell copy) := by
  cases cell <;> cases copy <;> rfl
theorem ready_iff (cell : Owner) (copy : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner NativePackageBundle.Value) :
    RegisterFuture.RawReady (raw cell copy owner names) a ↔ (a cell).isSome=true := by
  constructor
  · intro h
    apply h.1 cell
    simp [raw,FutureCellReindex.raw,CellReindex.expression,Frame.raw,Frame.rowExpr,Frame.pairExpr,
      Frame.dataExpr,Expr.dependencies,Expr.reenv]
  · intro h
    apply (FutureCellReindex.ready_iff (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
      id (value copy) (Frame.raw cell false owner names) a).mpr
    apply Frame.ready cell false owner names _
    simpa [CellReindex.pullback] using h

local instance : DecidableEq (CSTTT.TransportTheory.TemporalSnapshotReadout Frame.Predictive Frame.Residue Bool) :=
  CSTTT.TransportTheory.instDecidableEqTemporalSnapshotReadout

theorem all_unbounded_words (cell : Owner) (copy : Bool) (names : Owner → CarrierId)
    (injective : Function.Injective names) :
    ∃ h : RegisterFuture.RawReady (raw cell copy (AvailabilityPublication.dataOwner cell copy) names) NativePackageBundle.canonical,
      CSTTT.TransportTheory.FullFutureSufficient (RegisterFuture.future
        (raw cell copy (AvailabilityPublication.dataOwner cell copy) names) NativePackageBundle.canonical h) := by
  obtain ⟨hb,hfuture⟩ := Frame.all_unbounded_words cell false (AvailabilityPublication.dataOwner cell copy) names
    injective (inputs copy NativePackageBundle.canonical) (AvailabilityPublication.selected cell copy)
    (selected_input cell copy) (AvailabilityPublication.selected_factor_accept cell copy)
  have hr : RegisterFuture.RawReady (raw cell copy (AvailabilityPublication.dataOwner cell copy) names) NativePackageBundle.canonical :=
    (FutureCellReindex.ready_iff (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
      id (value copy) (Frame.raw cell false (AvailabilityPublication.dataOwner cell copy) names) NativePackageBundle.canonical).mpr hb.2.1
  refine ⟨hr,?_⟩
  change CSTTT.TransportTheory.FullFutureSufficient (RegisterFuture.future
    (FutureCellReindex.raw (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
      id (value copy) (Frame.raw cell false (AvailabilityPublication.dataOwner cell copy) names))
      NativePackageBundle.canonical hr)
  rw [FutureCellReindex.future_equation (SV := NativeComposition.Value) (TV := NativePackageBundle.Value)
      id (value copy) (Frame.raw cell false (AvailabilityPublication.dataOwner cell copy) names)
      NativePackageBundle.canonical hr hb.2.1]
  exact hfuture

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackageFuture
