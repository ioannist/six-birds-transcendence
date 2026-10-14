import CSTTT.Targets.GenericHandoff.HistoricalAcquisition
import CSTTT.Targets.GenericHandoff.DispatchedPackage
import CSTTT.Targets.GenericHandoff.GameInvariantCompleteness

/-! Polymorphic P/A binding with historical-support entries (TTH-06).
One staged/glued assignment is read by the eight-schema dispatcher, reception,
target execution and withdrawal resources. Historical source support is NOT
funded source execution. The target execution object is shared by definition.
The stronger lineage component must separately bind its actual source execution
and the typed receiver equations at the enclosing RawHandoff boundary.

Auxiliary invariants/strategies are allowed only with proofs against these
DEFINED semantics (hybrid decision). No finite-context lift is assumed. This
is a proved component boundary, not the final generic TTH-06 promotion. -/
namespace CSTTT.TargetTheory.GenericHandoff.HistoricalPackageRuntime
open RegisterInterpreter

structure Raw (SC TC : Type) (SV : SC → Type) (TV : TC → Type)
    (R : Type) (RV : R → Type)
    (D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId : Type) where
  package : DispatchedPackage.Raw SC TC SV TV
  resourceSchema : ResourceRuntime.Schema Factor Resource
  acquisitionSchema : AcquisitionExecution.Schema Stage Id History RouteId
  execution : ResourceRuntime.Execution TC TV R RV D A O
  resource : ResourceRuntime.Bindings TC TV R RV D A O Factor Resource Residue
  historical : HistoricalAcquisition.Bindings TC TV R RV D A SourceFactor HistoricalTargetFactor Stage Id History RouteId
  runCells : (k : TC) → Expr TC TV R RV Unit (TV k)

variable {SC TC R D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type} [DecidableEq TC]

/-- No supplied target assignment, game semantics, observer or entry set. -/
def target (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : Assignment TC TV := DispatchedPackage.global m.package a

def resources (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) :
    ResourceRuntime.Raw TC TV R RV D A O Factor Resource Residue :=
  {m.resource with execution := m.execution}

def acquisition (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId) :
    HistoricalAcquisition.Raw TC TV R RV D A O SourceFactor HistoricalTargetFactor Stage Id History RouteId :=
  {m.historical with execution := m.execution}

abbrev AcquisitionReady (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) := HistoricalAcquisition.Ready (acquisition m) (target m a)
abbrev ResourceReady (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) := ResourceRuntime.Ready (resources m) (target m a)

def IntegratedTargetRealization (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : Prop :=
  (∀ c k, k ∈ m.package.cover.scopes c → target m a k =
    mappedLocal m.package.language a m.package.stage m.package.cover.scopes c k) ∧
  (∀ k, (target m a k).isSome = true) ∧ m.package.clauses.accept (target m a)

def PackagePass (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : Prop := DispatchedPackage.Valid m.package a

theorem package_soundness (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (h : PackagePass m a) : IntegratedTargetRealization m a :=
  DispatchedPackage.constructs m.package a h

def runAssignment (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (r : Registers R RV) : Assignment TC TV :=
  fun k => (m.runCells k).eval (target m a) r ()

def PackageAt (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (r : Registers R RV) : Prop :=
  IntegratedTargetRealization m a ∧ ResourceRuntime.Inside m.resourceSchema (resources m) (target m a) r ∧
  m.package.clauses.accept (runAssignment m a r)

def Entries (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (ha : AcquisitionReady m a) : Registers R RV → Prop :=
  HistoricalAcquisition.Entry m.acquisitionSchema (acquisition m) (target m a) ha

def Withdrawal (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : Prop :=
  ResourceRuntime.DomainCheck m.resourceSchema (resources m) ∧
  ResourceRuntime.WithdrawalCheck m.resourceSchema (resources m) (target m a)

abbrev FullCertificate (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (ha : AcquisitionReady m a) (hr : ResourceReady m a) :=
  StrategyGame.InvariantCertificate (ResourceRuntime.rows (resources m) (target m a))
    (ResourceRuntime.update (resources m) (target m a) hr) (Entries m a ha) (Withdrawal m a)
    (PackageAt m a) (ResourceRuntime.ResourceClosed m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.Legal m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.StepLaw m.resourceSchema (resources m) (target m a) hr)

abbrev OperationalCertificate (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (ha : AcquisitionReady m a) (hr : ResourceReady m a) :=
  ResourceRuntime.Certificate m.resourceSchema (resources m) (target m a) hr (Entries m a ha)

def FullGame (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (ha : AcquisitionReady m a) (hr : ResourceReady m a) : Prop :=
  StrategyGame.GameReadout (ResourceRuntime.rows (resources m) (target m a))
    (ResourceRuntime.update (resources m) (target m a) hr) (Entries m a ha) (Withdrawal m a)
    (PackageAt m a) (ResourceRuntime.ResourceClosed m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.Legal m.resourceSchema (resources m) (target m a))
    (ResourceRuntime.StepLaw m.resourceSchema (resources m) (target m a) hr)

def OperationalGame (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (ha : AcquisitionReady m a) (hr : ResourceReady m a) : Prop :=
  ResourceRuntime.OperationalReadout m.resourceSchema (resources m) (target m a) hr (Entries m a ha)

def FullPass (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m a, ∃ hr : ResourceReady m a, Nonempty (FullCertificate m a ha hr)

def OperationalPass (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m a, ∃ hr : ResourceReady m a, Nonempty (OperationalCertificate m a ha hr)

def PostWithdrawalFullAutonomy (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m a, ∃ hr : ResourceReady m a, FullGame m a ha hr

def PostWithdrawalOperationalAutonomy (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m a, ∃ hr : ResourceReady m a, OperationalGame m a ha hr

theorem full_soundness (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (h : FullPass m a) : PostWithdrawalFullAutonomy m a := by
  obtain ⟨ha,hr,⟨cert⟩⟩ := h
  exact ⟨ha,hr,StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert⟩

theorem operational_soundness (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (h : OperationalPass m a) : PostWithdrawalOperationalAutonomy m a := by
  obtain ⟨ha,hr,⟨cert⟩⟩ := h
  exact ⟨ha,hr,ResourceRuntime.soundness _ _ _ _ _ cert⟩

/-- Semantic completeness of proof-bearing invariants, NOT decision
completeness of a finite constructor for unrestricted context recipes. -/
theorem full_pass_iff_readout (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : FullPass m a ↔ PostWithdrawalFullAutonomy m a := by
  constructor
  · exact full_soundness m a
  · rintro ⟨ha,hr,hg⟩
    exact ⟨ha,hr,StrategyGame.game_invariant_completeness hg⟩

theorem operational_pass_iff_readout (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) : OperationalPass m a ↔ PostWithdrawalOperationalAutonomy m a := by
  constructor
  · exact operational_soundness m a
  · rintro ⟨ha,hr,hg⟩
    exact ⟨ha,hr,StrategyGame.game_invariant_completeness hg⟩

/-- AF ⇒ P at a genuine activated entry. This dependency does NOT supply the
package_soundness derivation, which consumes only its separate raw subcheck. -/
theorem full_autonomy_implies_package (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (h : PostWithdrawalFullAutonomy m a) : IntegratedTargetRealization m a := by
  obtain ⟨ha,hr,hg⟩ := h
  obtain ⟨entry,he⟩ := hg.2.1
  exact (StrategyGame.game_entry_package hg entry he).1

theorem full_implies_operational (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (h : PostWithdrawalFullAutonomy m a) : PostWithdrawalOperationalAutonomy m a := by
  obtain ⟨ha,hr,hw,he,strategy,hs⟩ := h
  refine ⟨ha,hr,hw,he,strategy,?_⟩
  intro entry hin r past hp
  have safe := hs entry hin r past hp
  exact ⟨safe.1.2.1,safe.2⟩

theorem acquisition_resource_rows (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (r : Registers R RV) (d : D) (act : A) :
    HistoricalAcquisition.rows (acquisition m) (target m a) r d act =
      ResourceRuntime.rows (resources m) (target m a) r d act := rfl

theorem acquisition_resource_update (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (ha : AcquisitionReady m a) (hr : ResourceReady m a)
    (r : Registers R RV) (d : D) (act : A) (o : O) :
    HistoricalAcquisition.update (acquisition m) (target m a) ha r d act o =
      ResourceRuntime.update (resources m) (target m a) hr r d act o := rfl

/-- Missing historical inputs reject BOTH games before totalization; O is not
forced to read source funding/ticks unless the raw recipes actually read them. -/
theorem missing_acquisition_no_games (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (k : TC) (hk : k ∈ (acquisition m).dependencies)
    (hm : target m a k = none) :
    ¬ PostWithdrawalFullAutonomy m a ∧ ¬ PostWithdrawalOperationalAutonomy m a := by
  have bad := HistoricalAcquisition.missing_dependency_rejected (acquisition m) (target m a) k hk hm
  exact ⟨fun ⟨ha,_,_⟩ => bad ha,fun ⟨ha,_,_⟩ => bad ha⟩

theorem missing_resource_no_games (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (k : TC) (hk : k ∈ (resources m).readDependencies)
    (hm : target m a k = none) :
    ¬ PostWithdrawalFullAutonomy m a ∧ ¬ PostWithdrawalOperationalAutonomy m a := by
  have bad := ResourceRuntime.missing_read_rejected (resources m) (target m a) k hk hm
  exact ⟨fun ⟨_,hr,_⟩ => bad hr,fun ⟨_,hr,_⟩ => bad hr⟩

theorem source_absent_no_games (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (receiver : AcquisitionExecution.Receiver)
    (he : (acquisition m).receiver.read (target m a) = some receiver)
    (absent : receiver.sourcePresent = false) :
    ¬ PostWithdrawalFullAutonomy m a ∧ ¬ PostWithdrawalOperationalAutonomy m a := by
  have noEntry (ha : AcquisitionReady m a) (r : Registers R RV) : ¬ Entries m a ha r :=
    HistoricalAcquisition.source_absent_no_entry _ _ _ ha receiver he absent r
  exact ⟨fun ⟨ha,_,hg⟩ => StrategyGame.no_entries_no_game (noEntry ha) hg,
    fun ⟨ha,_,hg⟩ => StrategyGame.no_entries_no_game (noEntry ha) hg⟩

theorem failed_clause_no_full (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (c : ClauseDispatcher.Kind)
    (bad : ¬ (m.package.clauses.rule c).accept (target m a)) : ¬ PostWithdrawalFullAutonomy m a :=
  fun h => bad ((full_autonomy_implies_package m a h).2.2 c)

/-- Full future disturbance words, actual support and actual resource closure.
Safety is over the causal strategy's generated plays, not every available act. -/
theorem full_answers_every_word (m : Raw SC TC SV TV R RV D A O SourceFactor HistoricalTargetFactor Factor Resource Residue Stage Id History RouteId)
    (a : Assignment SC SV) (h : PostWithdrawalFullAutonomy m a) :
    ∃ ha : AcquisitionReady m a, ∃ hr : ResourceReady m a,
      ∃ strategy : StrategyGame.Strategy (Registers R RV) D A,
        ∀ entry, Entries m a ha entry → ∀ word : List D,
          ∃ final past,
            StrategyGame.WordExecution (ResourceRuntime.rows (resources m) (target m a))
              (ResourceRuntime.update (resources m) (target m a) hr) strategy [entry] word (final::past) ∧
            StrategyGame.Play (ResourceRuntime.rows (resources m) (target m a))
              (ResourceRuntime.update (resources m) (target m a) hr) strategy entry (final::past) ∧
            PackageAt m a final ∧ ResourceRuntime.ResourceClosed m.resourceSchema (resources m) (target m a) final := by
  obtain ⟨ha,hr,_,_,strategy,hs⟩ := h
  refine ⟨ha,hr,strategy,?_⟩
  intro entry he word
  obtain ⟨last,exec,hplay⟩ := StrategyGame.strategy_answers_word
    (fun r past hp d => ((hs entry he r past hp).2.2 d).2.1.2.2)
    entry [] StrategyGame.Play.initial word
  cases last with
  | nil => cases hplay
  | cons final past => exact ⟨final,past,exec,hplay,(hs entry he final past hplay).1,
      (hs entry he final past hplay).2.1⟩

end CSTTT.TargetTheory.GenericHandoff.HistoricalPackageRuntime
