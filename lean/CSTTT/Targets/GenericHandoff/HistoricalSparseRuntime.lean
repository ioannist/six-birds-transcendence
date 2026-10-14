import CSTTT.Targets.GenericHandoff.HistoricalPackageRuntime
import CSTTT.Targets.GenericHandoff.StrictSparseGame

/-! TTH-06 (b): representation-sensitive selected-response legality.
The old historical F/O readouts remain SUPPORT-ONLY, unchanged. New Sparse
readouts inspect the defined raw response row on every strategy play.
Entries, package, resources and updater remain shared, with missing-input
rejection before decoding. No extra ordering/duplicate condition. -/
namespace CSTTT.TargetTheory.GenericHandoff.HistoricalPackageRuntime
open RegisterInterpreter
variable {SC TC R D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type} [DecidableEq TC]


def SparseFullGame (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (ha : AcquisitionReady m a) (hr : ResourceReady m a) : Prop :=
  StrictSparseGame.Readout (ResourceRuntime.rows (resources m) (target m a))
    (ResourceRuntime.update (resources m) (target m a) hr) (Entries m a ha) (Withdrawal m a)
    (PackageAt m a) (ResourceRuntime.ResourceClosed m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.Legal m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.StepLaw m.resourceSchema (resources m) (target m a) hr)

abbrev SparseFullCertificate (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (ha : AcquisitionReady m a) (hr : ResourceReady m a) :=
  StrictSparseGame.Certificate (ResourceRuntime.rows (resources m) (target m a))
    (ResourceRuntime.update (resources m) (target m a) hr) (Entries m a ha) (Withdrawal m a)
    (PackageAt m a) (ResourceRuntime.ResourceClosed m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.Legal m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.StepLaw m.resourceSchema (resources m) (target m a) hr)

def SparseFullAutonomy (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m a, ∃ hr : ResourceReady m a, SparseFullGame m a ha hr

theorem sparse_full_implies_support_only (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (h : SparseFullAutonomy m a) : PostWithdrawalFullAutonomy m a := by
  obtain ⟨ha,hr,hg⟩ := h
  exact ⟨ha,hr,StrictSparseGame.implies_support_only hg⟩

theorem sparse_full_soundness (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (ha : AcquisitionReady m a) (hr : ResourceReady m a)
    (cert : SparseFullCertificate m a ha hr) : SparseFullAutonomy m a :=
  ⟨ha,hr,StrictSparseGame.soundness cert⟩

def SparseOperationalGame (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (ha : AcquisitionReady m a) (hr : ResourceReady m a) : Prop :=
  StrictSparseGame.Readout (ResourceRuntime.rows (resources m) (target m a))
    (ResourceRuntime.update (resources m) (target m a) hr) (Entries m a ha) (Withdrawal m a)
    (ResourceRuntime.Inside m.resourceSchema (resources m) (target m a)) (ResourceRuntime.ResourceClosed m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.Legal m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.StepLaw m.resourceSchema (resources m) (target m a) hr)

abbrev SparseOperationalCertificate (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (ha : AcquisitionReady m a) (hr : ResourceReady m a) :=
  StrictSparseGame.Certificate (ResourceRuntime.rows (resources m) (target m a))
    (ResourceRuntime.update (resources m) (target m a) hr) (Entries m a ha) (Withdrawal m a)
    (ResourceRuntime.Inside m.resourceSchema (resources m) (target m a)) (ResourceRuntime.ResourceClosed m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.Legal m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.StepLaw m.resourceSchema (resources m) (target m a) hr)

def SparseOperationalAutonomy (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m a, ∃ hr : ResourceReady m a, SparseOperationalGame m a ha hr

theorem sparse_operational_implies_support_only (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (h : SparseOperationalAutonomy m a) : PostWithdrawalOperationalAutonomy m a := by
  obtain ⟨ha,hr,hg⟩ := h
  exact ⟨ha,hr,StrictSparseGame.implies_support_only hg⟩

theorem sparse_operational_soundness (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (ha : AcquisitionReady m a) (hr : ResourceReady m a)
    (cert : SparseOperationalCertificate m a ha hr) : SparseOperationalAutonomy m a :=
  ⟨ha,hr,StrictSparseGame.soundness cert⟩

theorem sparse_full_implies_package (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (h : SparseFullAutonomy m a) : IntegratedTargetRealization m a :=
  full_autonomy_implies_package m a (sparse_full_implies_support_only m a h)

theorem sparse_full_implies_operational (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) (a : Assignment SC SV)
    (h : SparseFullAutonomy m a) : SparseOperationalAutonomy m a := by
  obtain ⟨ha,hr,hw,he,strategy,hs⟩ := h
  refine ⟨ha,hr,hw,he,strategy,?_⟩
  intro entry hin r past hp
  have safe := hs entry hin r past hp
  exact ⟨safe.1.2.1,safe.2⟩

end CSTTT.TargetTheory.GenericHandoff.HistoricalPackageRuntime
