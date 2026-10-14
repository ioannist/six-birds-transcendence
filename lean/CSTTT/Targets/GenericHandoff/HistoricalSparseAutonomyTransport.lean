import CSTTT.Targets.GenericHandoff.HistoricalFiniteAutonomy
import CSTTT.Targets.GenericHandoff.HistoricalSparseRuntime

/-! Format-qualified generic TTH-05 transport, TTH-06. StrictSparse is checked
on selected responses on all plays; forgetting only that format obligation
preserves the actual updater, package and positive support. The finite-context
primitive/resource/ownership lift remains proved evidence per instance, never
assumed irrelevant. Every genuine entry and nominal word remain quantified. -/
namespace CSTTT.TargetTheory.GenericHandoff.HistoricalFiniteAutonomy
open RegisterInterpreter CSTTT.AutonomyTheory
variable {SC TC R X D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type}
  [DecidableEq TC]

local notation "Model" => HistoricalPackageRuntime.Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId
local notation "FactorFrame" => Frame TC TV R RV X D A Resource

theorem sparse_full_each_entry_exact (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (hl : Lift m f source h)
    (hg : HistoricalPackageRuntime.SparseFullAutonomy m source) :
    ∃ ha : HistoricalPackageRuntime.AcquisitionReady m source,
      ∃ cert : HistoricalPackageRuntime.FullCertificate m source ha h.ready,
        ∀ entry, HistoricalPackageRuntime.Entries m source ha entry →
          Nonempty (ExactAutonomyCertificate (GameAutonomyTransport.projectedData
            (factor m f source h) cert (project m f source h) entry)) :=
  full_readout_each_entry_exact m f source h hl
    (HistoricalPackageRuntime.sparse_full_implies_support_only m source hg)

theorem sparse_full_each_entry_words (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (hl : Lift m f source h)
    (hg : HistoricalPackageRuntime.SparseFullAutonomy m source) :
    ∃ ha : HistoricalPackageRuntime.AcquisitionReady m source,
      ∃ cert : HistoricalPackageRuntime.FullCertificate m source ha h.ready,
        ∀ entry, HistoricalPackageRuntime.Entries m source ha entry → ∀ word : List D,
          ∃ y, ControlledRun (GameAutonomyTransport.projectedData
            (factor m f source h) cert (project m f source h) entry)
            (project m f source h entry) word y ∧ FactorPackage m f source y :=
  full_readout_each_entry_words m f source h hl
    (HistoricalPackageRuntime.sparse_full_implies_support_only m source hg)

end CSTTT.TargetTheory.GenericHandoff.HistoricalFiniteAutonomy
