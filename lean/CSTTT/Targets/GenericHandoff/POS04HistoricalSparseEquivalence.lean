import CSTTT.Targets.GenericHandoff.POS04HistoricalSparseLaws

/-! Whole format-qualified historical F/O game adapters, arbitrary partial
POS-04 assignments. The computed nominal protocol gates both versions. Closure
is derived from normalization, strict sparse format and invariant preservation
of EVERY positive branch. Resource legality alone never supplies row closure.
The generic historical raw interpreters are unchanged; support-only readouts
remain named separately. This is the POS-04 adapter, not final RawHandoff. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseEquivalence
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RouteExecution POS04ResourceRuntime POS04OperationalGame
open POS04HistoricalEntryEquivalence POS04HistoricalResourceEquivalence POS04HistoricalSparseLaws
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Bool selects only the declared F or O package ceiling; it does not supply
an independently chosen predicate. -/
def legacyPackage (full : Bool) (m : RawLaneModel) (r : Run6) : Prop :=
  if full then POS04FullGame.PackageAt m r else Inside m r

def rawPackage (full : Bool) (m : RawLaneModel) (r : Registers Unit FrameValue) : Prop :=
  if full then HistoricalPackageRuntime.PackageAt (model m) m.assignment r else
    ResourceRuntime.Inside (model m).resourceSchema (rawResource m) (image m.assignment) r

abbrev LegacyCertificate (full : Bool) (m : RawLaneModel) :=
  StrategyGame.InvariantCertificate (rows m) (update m) (Entries m) (Protocol m)
    (legacyPackage full m) (ResourceClosed m) (Legal m) (StepLaw m)

abbrev RawCertificate (full : Bool) (m : RawLaneModel) (hp : Protocol m)
    (hr : HistoricalPackageRuntime.ResourceReady (model m) m.assignment) :=
  StrictSparseGame.Certificate (ResourceRuntime.rows (rawResource m) (HistoricalPackageRuntime.target (model m) m.assignment))
    (ResourceRuntime.update (rawResource m) (HistoricalPackageRuntime.target (model m) m.assignment) hr)
    (HistoricalPackageRuntime.Entries (model m) m.assignment (ready m hp))
    (HistoricalPackageRuntime.Withdrawal (model m) m.assignment)
    (rawPackage full m) (ResourceRuntime.ResourceClosed (model m).resourceSchema (rawResource m) (HistoricalPackageRuntime.target (model m) m.assignment))
    (ResourceRuntime.Legal (model m).resourceSchema (rawResource m) (HistoricalPackageRuntime.target (model m) m.assignment))
    (ResourceRuntime.StepLaw (model m).resourceSchema (rawResource m) (HistoricalPackageRuntime.target (model m) m.assignment) hr)

theorem package_iff (full : Bool) (m : RawLaneModel) (hp : Protocol m) (r : Run6) :
    rawPackage full m (frame .target r) ↔ legacyPackage full m r := by
  cases full
  · exact POS04HistoricalPackageEquivalence.inside_iff m r
  · exact POS04HistoricalPackageEquivalence.package_at_iff m hp r

theorem package_inside (full : Bool) (m : RawLaneModel) (r : Run6)
    (h : legacyPackage full m r) : Inside m r := by
  cases full
  · exact h
  · obtain ⟨_,s,hs,_⟩ := h
    exact ⟨s,hs⟩

/-- Construct the format-qualified runtime invariant from the frozen one.
Its selected rows are already sparse, but unselected actions are not checked. -/
def toRaw (full : Bool) (m : RawLaneModel) (cert : LegacyCertificate full m)
    (hr : HistoricalPackageRuntime.ResourceReady (model m) m.assignment) :
    RawCertificate full m cert.withdrawn hr where
  inside x := ∃ r, x = frame .target r ∧ cert.inside r
  withdrawn := POS04HistoricalRuntime.withdrawal_of_protocol m cert.withdrawn
  entriesNonempty := by
    obtain ⟨r,he⟩ := cert.entriesNonempty
    exact ⟨frame .target r,(entries_iff m cert.withdrawn r).mpr he⟩
  entriesInside x he := by
    obtain ⟨r,heq,hl⟩ := entries_target m cert.withdrawn x he
    subst x
    exact ⟨r,rfl,cert.entriesInside r hl⟩
  packageInside x hx := by
    obtain ⟨r,rfl,hi⟩ := hx
    exact (package_iff full m cert.withdrawn r).mpr (cert.packageInside r hi)
  resourcesInside x hx := by
    obtain ⟨r,rfl,hi⟩ := hx
    simpa only [POS04HistoricalRuntime.target_eq] using
      (resource_closed_iff m cert.withdrawn r).mpr (cert.resourcesInside r hi)
  response x hx d := by
    obtain ⟨r,rfl,hi⟩ := hx
    obtain ⟨act,ha,hn,hnext⟩ := cert.response r hi d
    have hc := cert.resourcesInside r hi
    have eqRows := response_rows_eq m cert.withdrawn r hc d act
    obtain ⟨_,s,hs,hrow⟩ := ha
    have sparse := ((row_closed_iff m cert.withdrawn r s hs d act kernel).mp hrow).1
    have rawlegal := legal_of_resource_closed m cert.withdrawn r hc d act
    refine ⟨act,⟨by simpa only [POS04HistoricalRuntime.target_eq] using rawlegal,
      by rw [POS04HistoricalRuntime.target_eq,eqRows]; exact sparse⟩,?_,?_⟩
    · simpa only [StrategyGame.Normalized,StrategyGame.PositiveSupport,POS04HistoricalRuntime.target_eq,eqRows] using hn
    · intro o ho
      have hsupp : StrategyGame.PositiveSupport (rows m) r d act o := by
        simpa only [StrategyGame.PositiveSupport,POS04HistoricalRuntime.target_eq,eqRows] using ho
      have next := hnext o hsupp
      have up := update_eq m cert.withdrawn hr r d act o
      refine ⟨⟨update m r d act o,up,next.1⟩,?_⟩
      exact raw_step m cert.withdrawn hr r hc s hs d act
        (List.isEmpty_eq_false_iff.mpr (closed_fields _ _ _ _ hrow).1) o

/-- Converse uses each actual positive branch of the invariant. It does not
assume a safe factor set or derive closure from resource ownership alone. -/
def toLegacy (full : Bool) (m : RawLaneModel) (hp : Protocol m)
    (hr : HistoricalPackageRuntime.ResourceReady (model m) m.assignment)
    (cert : RawCertificate full m hp hr) : LegacyCertificate full m where
  inside r := cert.inside (frame .target r)
  withdrawn := hp
  entriesNonempty := by
    obtain ⟨x,he⟩ := cert.entriesNonempty
    obtain ⟨r,_heq,hl⟩ := entries_target m hp x he
    exact ⟨r,hl⟩
  entriesInside r he := cert.entriesInside _ ((entries_iff m hp r).mpr he)
  packageInside r hi := (package_iff full m hp r).mp (cert.packageInside _ hi)
  resourcesInside r hi := (resource_closed_iff m hp r).mp (by simpa only [POS04HistoricalRuntime.target_eq] using cert.resourcesInside _ hi)
  response r hi d := by
    have pkg := (package_iff full m hp r).mp (cert.packageInside _ hi)
    obtain ⟨s,hs⟩ := package_inside full m r pkg
    have hc := (resource_closed_iff m hp r).mp (by simpa only [POS04HistoricalRuntime.target_eq] using cert.resourcesInside _ hi)
    obtain ⟨act,ha,hn,hnext⟩ := cert.response _ hi d
    have eqRows := response_rows_eq m hp r hc d act
    have normalized : StrategyGame.Normalized (rows m) r d act := by
      simpa only [StrategyGame.Normalized,StrategyGame.PositiveSupport,POS04HistoricalRuntime.target_eq,eqRows] using hn
    have sparse : StrictSparseGame.StrictSparse (rows m r d act) := by
      rw [← eqRows]
      simpa only [POS04HistoricalRuntime.target_eq] using ha.2
    have nextInside : ∀ o, StrategyGame.PositiveSupport (rows m) r d act o →
        cert.inside (frame .target (update m r d act o)) := by
      intro o ho
      have rawsupp : StrategyGame.PositiveSupport (ResourceRuntime.rows (rawResource m) (HistoricalPackageRuntime.target (model m) m.assignment))
          (frame .target r) d act o := by
        simpa only [StrategyGame.PositiveSupport,POS04HistoricalRuntime.target_eq,eqRows] using ho
      have hinside := (hnext o rawsupp).1
      simpa only [POS04HistoricalRuntime.target_eq,update_eq m hp hr r d act o] using hinside
    have safe : ∀ o, StrategyGame.PositiveSupport (rows m) r d act o →
        ∃ t, o = .inK t ∧ t ∈ kernel := by
      intro o ho
      have pkg' := (package_iff full m hp (update m r d act o)).mp (cert.packageInside _ (nextInside o ho))
      obtain ⟨t,ht⟩ := package_inside full m _ pkg'
      exact ⟨t,ht,by cases t <;> decide⟩
    have hrow := (row_closed_iff m hp r s hs d act kernel).mpr ⟨sparse,normalized,safe⟩
    refine ⟨act,⟨ha.1.2.1,s,hs,hrow⟩,normalized,?_⟩
    intro o ho
    exact ⟨nextInside o ho,(step_preserves m hp r hc s hs d act
      (List.isEmpty_eq_false_iff.mpr (closed_fields _ _ _ _ hrow).1) o).2⟩

/-- The protocol is defined by the raw eager interpreter, not supplied as a
verdict. This wrapper rejects protocol failures, including missing inputs. -/
def FullAutonomy (m : RawLaneModel) : Prop :=
  (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) = some true ∧
    HistoricalPackageRuntime.SparseFullAutonomy (model m) m.assignment

def OperationalAutonomy (m : RawLaneModel) : Prop :=
  (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) = some true ∧
    HistoricalPackageRuntime.SparseOperationalAutonomy (model m) m.assignment

theorem full_iff_af (m : RawLaneModel) : FullAutonomy m ↔ AF m := by
  constructor
  · rintro ⟨hc,ha,hr,hg⟩
    have hp := (POS04HistoricalRuntimeProtocol.check_iff m).mp hc
    obtain ⟨cert⟩ := StrictSparseGame.invariant_iff.mp hg
    have cert' : RawCertificate true m hp hr := by
      simpa only [RawCertificate,rawPackage,HistoricalPackageRuntime.SparseFullGame,
        POS04HistoricalRuntime.target_eq] using cert
    exact POS04FullGame.certificate_implies_af m (toLegacy true m hp hr cert')
  · intro hf
    let cert := POS04FullGame.certificateOfAF m hf
    let hr := POS04HistoricalRuntime.resource_ready_of_protocol m cert.withdrawn
    have raw := toRaw true m cert hr
    refine ⟨(POS04HistoricalRuntimeProtocol.check_iff m).mpr cert.withdrawn,
      ready m cert.withdrawn,hr,?_⟩
    apply StrictSparseGame.soundness
    simpa only [RawCertificate,rawPackage,HistoricalPackageRuntime.SparseFullGame,
      POS04HistoricalRuntime.target_eq] using raw

theorem operational_iff_ao (m : RawLaneModel) : OperationalAutonomy m ↔ AO m := by
  constructor
  · rintro ⟨hc,ha,hr,hg⟩
    have hp := (POS04HistoricalRuntimeProtocol.check_iff m).mp hc
    obtain ⟨cert⟩ := StrictSparseGame.invariant_iff.mp hg
    have cert' : RawCertificate false m hp hr := by
      simpa only [RawCertificate,rawPackage,HistoricalPackageRuntime.SparseOperationalGame,
        POS04HistoricalRuntime.target_eq] using cert
    exact POS04OperationalGame.certificate_implies_ao m (toLegacy false m hp hr cert')
  · intro ho
    let cert := POS04OperationalGame.certificateOfAO m ho
    let hr := POS04HistoricalRuntime.resource_ready_of_protocol m cert.withdrawn
    have raw := toRaw false m cert hr
    refine ⟨(POS04HistoricalRuntimeProtocol.check_iff m).mpr cert.withdrawn,
      ready m cert.withdrawn,hr,?_⟩
    apply StrictSparseGame.soundness
    simpa only [RawCertificate,rawPackage,HistoricalPackageRuntime.SparseOperationalGame,
      POS04HistoricalRuntime.target_eq] using raw

theorem protocol_failure (m : RawLaneModel)
    (bad : (POS04HistoricalRuntimeProtocol.check m).read (image m.assignment) ≠ some true) :
    (¬ FullAutonomy m ∧ ¬ AF m) ∧ (¬ OperationalAutonomy m ∧ ¬ AO m) :=
  ⟨⟨fun h => bad h.1,fun h => bad ((full_iff_af m).mpr h).1⟩,
    ⟨fun h => bad h.1,fun h => bad ((operational_iff_ao m).mpr h).1⟩⟩

/-- Every consumed nominal protocol cell rejects before decoding defaults.
This parameterized guard includes source support, target rows and receiver. -/
theorem missing_protocol_dependency (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) (hm : image m.assignment k = none) :
    (¬ FullAutonomy m ∧ ¬ AF m) ∧ (¬ OperationalAutonomy m ∧ ¬ AO m) := by
  apply protocol_failure
  intro he
  rw [POS04HistoricalRuntimeProtocol.missing_rejected m k hk hm] at he
  contradiction

/-- F additionally requires every same-package primitive. The nonempty
entry and its package, not an acquisition-history substitute, supply this. -/
theorem missing_package_primitive (m : RawLaneModel) (k : Cell)
    (hm : m.assignment k = none) : ¬ FullAutonomy m := by
  intro h
  have hc := ((package_lane_iff _).mp (fullAutonomy_implies_package m ((full_iff_af m).mp h))).1
    k (primitive_cells_complete k)
  rw [hm] at hc
  contradiction

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseEquivalence
