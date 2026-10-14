import CSTTT.Targets.GenericHandoff.PublicRuntime
import CSTTT.Targets.GenericHandoff.FramePresentation
import CSTTT.Targets.GenericHandoff.HistoricalSparseAutonomyTransport

/-! Owning raw interface, TTH-06 (b).
One stage constructs the target assignment. One pair of raw acquisition frames
constructs the endpoint, factor and temporal presentations. The public resource
runtime is shared by historical F/O games and funded actual lineage. Historical
source support and funded source execution remain deliberately different.

StrictSparse inspects selected response representations, without ordering or
duplicate restrictions. Execution links cover EVERY positive-support branch.
Auxiliary invariants and finite lifting laws are evidence against these defined
semantics; no finite-context completeness is assumed. This is the owning component boundary, not yet the complete G0 contract.
The nominal protocol and receiver-content
coherence remain enclosing completion obligations. These bare game readouts
are not claimed equivalent to a frozen protocol-qualified family.
-/
namespace CSTTT.TargetTheory.GenericHandoff.OwningHandoff
open RegisterInterpreter

structure RawHandoff (SC Cell : Type) (SourceValue : SC → Type) (Value : Cell → Type)
    (R SR TR : Type) (RV : R → Type) (SRV : SR → Type) (TRV : TR → Type)
    (S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type) where
  sourceClauses : ClauseDispatcher.Package SC SourceValue
  package : DispatchedPackage.Raw SC Cell SourceValue Value
  frames : FramePresentation.Raw Cell Value SR TR SRV TRV S A O H HF Route Stage Id Owner D P Q
  schema : RuntimeComponents.Schema Factor Resource Stage Id H Route
  runtime : RuntimeComponents.Raw Cell Value R RV D A O P Factor Resource (List S × List Id) Stage Id H Route
  sourceEmbedding : (k : R) → Expr Cell Value SR SRV Unit (RV k)
  targetEmbedding : (k : R) → Expr Cell Value TR TRV Unit (RV k)
  translation : (k : TR) → Expr Cell Value SR SRV Unit (TRV k)
  maps : CSTTT.TransportTheory.SnapshotRawMaps P Q (List S × List Id) Bool
  names : AcquisitionCorridor.Names Id
  seeds : StaticView Cell Value (AcquisitionCorridor.Seeds H)
  predictiveCoordinate : StaticView Cell Value (P → Nat)
  historyCoordinate : (List S × List Id) → List String
  routeCoordinate : (List S × List Id) → List String
  route : RuntimeComponents.RouteInstructions Cell Value R RV D A O Id H (List S × List Id) Endpoint
  historicalExecution : ResourceRuntime.Execution Cell Value R RV D A O
  historical : HistoricalAcquisition.Bindings Cell Value R RV D A S S Stage Id H Route
  runCells : (k : Cell) → Expr Cell Value R RV Unit (Value k)

variable {SC Cell R SR TR S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type}
  {SourceValue : SC → Type} {Value : Cell → Type} {RV : R → Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => RawHandoff SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint
variable [DecidableEq S] [DecidableEq O] [DecidableEq Route] [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner]

/-- No factor table, M classifier, endpoint or temporal observer is supplied. -/
def presentation (m : Model) := FramePresentation.presentation m.frames

def factor (m : Model) : RuntimeLineage.FactorRaw Cell Value where
  Source := S
  Target := S
  SourceAction := A
  TargetAction := A
  SourceOutcome := O
  TargetOutcome := O
  History := HF
  Route := Route
  Stage := Stage
  Id := Id
  Owner := Owner
  sourceEq := inferInstance
  targetEq := inferInstance
  ownerEq := inferInstance
  source := m.frames.sourceSchema
  target := m.frames.targetSchema
  instructions := PresentationCoherence.factorBindings (presentation m)

def endpoint (m : Model) : AcquisitionEndpoint.Interface Cell Value where
  State := S
  Action := A
  Outcome := O
  History := HF
  Route := Route
  Stage := Stage
  Id := Id
  Owner := Owner
  stateEq := inferInstance
  outcomeEq := inferInstance
  routeEq := inferInstance
  stageEq := inferInstance
  idEq := inferInstance
  ownerEq := inferInstance
  schema := PresentationCoherence.endpointSchema (presentation m)
  bindings := PresentationCoherence.endpointBindings (presentation m)

def lineage (m : Model) : RuntimeLineage.Raw Cell Value R SR TR RV SRV TRV D A O P Q
    Factor Resource (List S × List Id) Bool Endpoint Stage Id H Route where
  schema := m.schema
  runtime := m.runtime
  source := m.frames.sourceFrame
  target := m.frames.targetFrame
  sourceEmbedding := m.sourceEmbedding
  targetEmbedding := m.targetEmbedding
  translation := m.translation
  maps := m.maps
  names := m.names
  seeds := m.seeds
  predictiveCoordinate := m.predictiveCoordinate
  historyCoordinate := m.historyCoordinate
  routeCoordinate := m.routeCoordinate
  factor := factor m
  recordSchema := ⟨m.schema.eventIds,m.schema.routes⟩
  record := m.frames.record
  endpoint := endpoint m
  route := m.route

def publicRuntime (m : Model) : PublicRuntime.Raw SC Cell SourceValue Value R SR TR RV SRV TRV
    D A O P Q S S Factor Resource (List S × List Id) Bool Endpoint Stage Id H Route :=
  ⟨m.package,lineage m,m.historicalExecution,m.historical,m.runCells⟩

def autonomy (m : Model) := PublicRuntime.autonomy (publicRuntime m)
variable [DecidableEq Cell]
def target (m : Model) (a : Assignment SC SourceValue) := PublicRuntime.target (publicRuntime m) a

/-- Explicit carrier/owner translation, including injectivity. No proof flag. -/
def OwnershipCheck (m : Model) : Prop :=
  Function.Injective m.frames.owner ∧ RuntimeComponents.CarrierCheck m.schema ∧
  m.schema.source = m.frames.owner m.frames.sourceSchema.owner ∧
  m.schema.target = m.frames.owner m.frames.targetSchema.owner

/-- Public coherence combines checked raw equations and all-context laws.
The dispatcher C6 rule is linked to the SAME primitive decoder, not a second
accepted predicate. Other clause rules stay closed dispatcher constructors. -/
def Coherence (m : Model) (a : Assignment SC SourceValue) : Prop :=
  OwnershipCheck m ∧ FramePresentation.SchemaCheck m.frames ∧
  m.package.clauses.rule .c6 = TemporalRuntimeCoherence.rule (presentation m).target ∧
  PresentationCoherence.Pass (presentation m) (target m a) ∧
  PublicRuntime.TargetExecutionCoherent (publicRuntime m) a

/-- Each named semantic readout is defined independently of the enclosing gate. -/
def IntegratedTargetRealization (m : Model) (a : Assignment SC SourceValue) : Prop :=
  HistoricalPackageRuntime.IntegratedTargetRealization (autonomy m) a
variable [DecidableEq P] [DecidableEq Q]
def StrictTemporalLineage (m : Model) (a : Assignment SC SourceValue) : Prop :=
  RuntimeLineage.StrictTemporalLineage (lineage m) (target m a)
def PostWithdrawalFullAutonomy (m : Model) (a : Assignment SC SourceValue) : Prop :=
  HistoricalPackageRuntime.SparseFullAutonomy (autonomy m) a
def PostWithdrawalOperationalAutonomy (m : Model) (a : Assignment SC SourceValue) : Prop :=
  HistoricalPackageRuntime.SparseOperationalAutonomy (autonomy m) a

def FullSubcheck (m : Model) (a : Assignment SC SourceValue) : Prop :=
  ∃ ha : HistoricalPackageRuntime.AcquisitionReady (autonomy m) a,
    ∃ hr : HistoricalPackageRuntime.ResourceReady (autonomy m) a,
      Nonempty (HistoricalPackageRuntime.SparseFullCertificate (autonomy m) a ha hr)
def OperationalSubcheck (m : Model) (a : Assignment SC SourceValue) : Prop :=
  ∃ ha : HistoricalPackageRuntime.AcquisitionReady (autonomy m) a,
    ∃ hr : HistoricalPackageRuntime.ResourceReady (autonomy m) a,
      Nonempty (HistoricalPackageRuntime.SparseOperationalCertificate (autonomy m) a ha hr)

def SourcePackagePass (m : Model) (a : Assignment SC SourceValue) : Prop :=
  m.sourceClauses.accept a

def recognitionStatusOf (_m : Model) : CSTTT.RecognitionStatus := .notAddressed

def HandoffPass_F (m : Model) (a : Assignment SC SourceValue) : Prop :=
  SourcePackagePass m a ∧ Coherence m a ∧ DispatchedPackage.Valid m.package a ∧
    RuntimeLineage.CompletePass (lineage m) (target m a) ∧ FullSubcheck m a
def HandoffPass_O (m : Model) (a : Assignment SC SourceValue) : Prop :=
  SourcePackagePass m a ∧ Coherence m a ∧ DispatchedPackage.Valid m.package a ∧
    RuntimeLineage.CompletePass (lineage m) (target m a) ∧ OperationalSubcheck m a

omit [DecidableEq P] [DecidableEq Q] in
theorem package_soundness (m : Model) (a : Assignment SC SourceValue)
    (h : DispatchedPackage.Valid m.package a) : IntegratedTargetRealization m a :=
  HistoricalPackageRuntime.package_soundness (autonomy m) a h

theorem lineage_soundness (m : Model) (a : Assignment SC SourceValue)
    (h : RuntimeLineage.CompletePass (lineage m) (target m a)) : StrictTemporalLineage m a :=
  RuntimeLineage.complete_soundness _ _ h

omit [DecidableEq P] [DecidableEq Q] in
theorem full_soundness (m : Model) (a : Assignment SC SourceValue)
    (h : FullSubcheck m a) : PostWithdrawalFullAutonomy m a := by
  obtain ⟨ha,hr,⟨cert⟩⟩ := h
  exact HistoricalPackageRuntime.sparse_full_soundness _ _ ha hr cert

omit [DecidableEq P] [DecidableEq Q] in
theorem operational_soundness (m : Model) (a : Assignment SC SourceValue)
    (h : OperationalSubcheck m a) : PostWithdrawalOperationalAutonomy m a := by
  obtain ⟨ha,hr,⟨cert⟩⟩ := h
  exact HistoricalPackageRuntime.sparse_operational_soundness _ _ ha hr cert

/-- Separate lane derivations: package consumes ONLY the package check;
lineage ONLY its own complete check; autonomy ONLY its invariant certificate. -/
theorem temporalFIACHCertificateSoundness_generic_F (m : Model) (a : Assignment SC SourceValue)
    (h : HandoffPass_F m a) :
    IntegratedTargetRealization m a ∧ StrictTemporalLineage m a ∧ PostWithdrawalFullAutonomy m a :=
  ⟨package_soundness m a h.2.2.1,lineage_soundness m a h.2.2.2.1,full_soundness m a h.2.2.2.2⟩

theorem temporalFIACHCertificateSoundness_generic_O (m : Model) (a : Assignment SC SourceValue)
    (h : HandoffPass_O m a) :
    IntegratedTargetRealization m a ∧ StrictTemporalLineage m a ∧ PostWithdrawalOperationalAutonomy m a :=
  ⟨package_soundness m a h.2.2.1,lineage_soundness m a h.2.2.2.1,operational_soundness m a h.2.2.2.2⟩

omit [DecidableEq P] [DecidableEq Q] in
/-- The logical F dependence is disclosed; it is not used in package_soundness. -/
theorem full_autonomy_implies_package (m : Model) (a : Assignment SC SourceValue)
    (h : PostWithdrawalFullAutonomy m a) : IntegratedTargetRealization m a :=
  HistoricalPackageRuntime.sparse_full_implies_package _ _ h

omit [DecidableEq P] [DecidableEq Q] in
/-- Literal public interface equations, valid even when the assignment is partial. -/
theorem shared_target (m : Model) (a : Assignment SC SourceValue) :
    HistoricalPackageRuntime.target (autonomy m) a = target m a := rfl

omit [DecidableEq Cell] [DecidableEq P] [DecidableEq Q] in
theorem shared_frames (m : Model) : (lineage m).source = m.frames.sourceFrame ∧
    (lineage m).target = m.frames.targetFrame := ⟨rfl,rfl⟩

omit [DecidableEq Cell] [DecidableEq P] [DecidableEq Q] in
theorem shared_primitives (m : Model) :
    (endpoint m).bindings.source = m.frames.sourceCells ∧
    (endpoint m).bindings.target = m.frames.targetCells := ⟨rfl,rfl⟩

omit [DecidableEq Cell] [DecidableEq P] [DecidableEq Q] in
theorem shared_resources (m : Model) :
    (autonomy m).resource = m.runtime.resource := rfl

omit [DecidableEq P] [DecidableEq Q] in
theorem owner_binding (m : Model) (a : Assignment SC SourceValue) (h : Coherence m a) :
    m.schema.source = m.frames.owner m.frames.sourceSchema.owner ∧
    m.schema.target = m.frames.owner m.frames.targetSchema.owner := ⟨h.1.2.2.1,h.1.2.2.2⟩

theorem route_status (m : Model) (a : Assignment SC SourceValue) (h : StrictTemporalLineage m a) :
    RuntimeComponents.retainedRouteStatus m.schema m.runtime m.route (target m a) = .routeIndexed :=
  RuntimeLineage.route_status _ _ h.1

theorem missing_endpoint_no_lineage (m : Model) (a : Assignment SC SourceValue) (k : Cell)
    (hk : k ∈ (endpoint m).bindings.scope) (hm : target m a k = none) : ¬ StrictTemporalLineage m a :=
  RuntimeLineage.missing_endpoint_no_lineage _ _ k hk hm

theorem missing_atomic_no_lineage (m : Model) (a : Assignment SC SourceValue)
    (hm : m.frames.sourceFrame.acquisition.events.read (target m a) = none) : ¬ StrictTemporalLineage m a :=
  fun h => RuntimeLineage.missing_atomic_no_readout _ _ hm h.1

omit [DecidableEq P] [DecidableEq Q] in
theorem full_subcheck_iff (m : Model) (a : Assignment SC SourceValue) :
    FullSubcheck m a ↔ PostWithdrawalFullAutonomy m a := by
  constructor
  · exact full_soundness m a
  · rintro ⟨ha,hr,hg⟩
    exact ⟨ha,hr,StrictSparseGame.invariant_iff.mp hg⟩

omit [DecidableEq P] [DecidableEq Q] in
theorem operational_subcheck_iff (m : Model) (a : Assignment SC SourceValue) :
    OperationalSubcheck m a ↔ PostWithdrawalOperationalAutonomy m a := by
  constructor
  · exact operational_soundness m a
  · rintro ⟨ha,hr,hg⟩
    exact ⟨ha,hr,StrictSparseGame.invariant_iff.mp hg⟩

/-- Ownership failure rejects the enclosing certificate directly. -/
theorem wrong_target_owner_no_pass (m : Model) (a : Assignment SC SourceValue)
    (bad : m.schema.target ≠ m.frames.owner m.frames.targetSchema.owner) :
    ¬ HandoffPass_F m a ∧ ¬ HandoffPass_O m a :=
  ⟨fun h => bad (owner_binding m a h.2.1).2,fun h => bad (owner_binding m a h.2.1).2⟩

theorem mismatched_clause_primitives_no_pass (m : Model) (a : Assignment SC SourceValue)
    (bad : m.package.clauses.rule .c6 ≠ TemporalRuntimeCoherence.rule (presentation m).target) :
    ¬ HandoffPass_F m a ∧ ¬ HandoffPass_O m a :=
  ⟨fun h => bad h.2.1.2.2.1,fun h => bad h.2.1.2.2.1⟩

omit [DecidableEq P] [DecidableEq Q] in
/-- Generic TTH-05 transport for EVERY historical entry. Finite-context lift
is checked proof-bearing evidence per instance, never silently assumed. -/
theorem full_each_entry_exact {X : Type} (m : Model)
    (f : HistoricalFiniteAutonomy.Frame Cell Value R RV X D A Resource)
    (a : Assignment SC SourceValue)
    (h : HistoricalFiniteAutonomy.Checked (autonomy m) f a)
    (hl : HistoricalFiniteAutonomy.Lift (autonomy m) f a h)
    (hg : PostWithdrawalFullAutonomy m a) :
    ∃ ha : HistoricalPackageRuntime.AcquisitionReady (autonomy m) a,
      ∃ cert : HistoricalPackageRuntime.FullCertificate (autonomy m) a ha h.ready,
        ∀ entry, HistoricalPackageRuntime.Entries (autonomy m) a ha entry →
          Nonempty (CSTTT.AutonomyTheory.ExactAutonomyCertificate
            (GameAutonomyTransport.projectedData
              (HistoricalFiniteAutonomy.factor (autonomy m) f a h) cert
              (HistoricalFiniteAutonomy.project (autonomy m) f a h) entry)) :=
  HistoricalFiniteAutonomy.sparse_full_each_entry_exact _ _ _ h hl hg

theorem missing_source_primitive_no_pass (m : Model) (a : Assignment SC SourceValue)
    (c : ClauseDispatcher.Kind) (k : SC) (hk : k ∈ (m.sourceClauses.rule c).scope) (hm : a k = none) :
    ¬ HandoffPass_F m a ∧ ¬ HandoffPass_O m a :=
  ⟨fun h => (m.sourceClauses.rule c).missing_rejected a k hk hm (h.1 c),
    fun h => (m.sourceClauses.rule c).missing_rejected a k hk hm (h.1 c)⟩

end CSTTT.TargetTheory.GenericHandoff.OwningHandoff
