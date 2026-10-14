import CSTTT.Targets.GenericHandoff.DispatchedPackage
import CSTTT.Targets.GenericHandoff.RuntimeExecutionFrontier
import CSTTT.Targets.GenericHandoff.GameInvariantCompleteness

/-! Polymorphic package/resource/acquisition binding for the final RawHandoff.
The target assignment is the DEFINED staged and glued global. Acquisition and
withdrawal resources use ONE execution program and this SAME assignment.
Run-indexed packages interpret raw primitive instructions through the CLOSED
eight-schema dispatcher; no predicate, entry set, updater or verdict is a raw
field. Auxiliary invariants are proved evidence under the hybrid architecture.
This is the P/A binding, NOT the complete lineage or final TTH-06 assembler.
No finite-context lift is assumed here. -/
namespace CSTTT.TargetTheory.GenericHandoff.PackageRuntime
open RegisterInterpreter

structure Raw (SC TC : Type) (SV : SC → Type) (TV : TC → Type)
    (R : Type) (RV : R → Type)
    (D A O P Factor Resource Residue Stage Id History RouteId : Type) where
  package : DispatchedPackage.Raw SC TC SV TV
  runtimeSchema : RuntimeComponents.Schema Factor Resource Stage Id History RouteId
  runtime : RuntimeComponents.Raw TC TV R RV D A O P Factor Resource Residue Stage Id History RouteId
  /-- Typed primitive instructions, not acceptance instructions. -/
  runCells : (k : TC) → Expr TC TV R RV Unit (TV k)

variable {SC TC R D A O P Factor Resource Residue Stage Id History RouteId : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type}
  [DecidableEq TC] [DecidableEq Stage]

/-- SOURCE data are the only supplied assignment. Missing staged inputs stay
absent; the global is never an independent argument. -/
def target (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) : Assignment TC TV :=
  DispatchedPackage.global m.package source

def runAssignment (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) (r : Registers R RV) : Assignment TC TV :=
  fun k => (m.runCells k).eval (target m source) r ()

def IntegratedTargetRealization (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) : Prop :=
  (∀ c k, k ∈ m.package.cover.scopes c → target m source k =
    mappedLocal m.package.language source m.package.stage m.package.cover.scopes c k) ∧
  (∀ k, (target m source k).isSome = true) ∧ m.package.clauses.accept (target m source)

def PackagePass (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) : Prop :=
  DispatchedPackage.Valid m.package source

omit [DecidableEq Stage] in
theorem package_soundness (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (h : PackagePass m source) : IntegratedTargetRealization m source :=
  DispatchedPackage.constructs m.package source h

/-- Same arrival package plus raw clauses re-evaluated on actual run cells.
The factor check rejects exits, independently of the primitive interpreter. -/
def PackageAt (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) (r : Registers R RV) : Prop :=
  IntegratedTargetRealization m source ∧
  ResourceRuntime.Inside (RuntimeComponents.resourceSchema m.runtimeSchema)
    (RuntimeComponents.resources m.runtime) (target m source) r ∧
  m.package.clauses.accept (runAssignment m source r)

abbrev AcquisitionReady (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) :=
  AcquisitionExecution.Ready (RuntimeComponents.acquisition m.runtime) (target m source)
abbrev ResourceReady (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) :=
  ResourceRuntime.Ready (RuntimeComponents.resources m.runtime) (target m source)

/-- Activated realized acquisition and every positive-support phase-2 branch. -/
def Entries (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) (ha : AcquisitionReady m source) :=
  RuntimeComponents.Entries m.runtimeSchema m.runtime (target m source) ha

def Withdrawal (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) : Prop :=
  ResourceRuntime.DomainCheck (RuntimeComponents.resourceSchema m.runtimeSchema)
    (RuntimeComponents.resources m.runtime) ∧
  ResourceRuntime.WithdrawalCheck (RuntimeComponents.resourceSchema m.runtimeSchema)
    (RuntimeComponents.resources m.runtime) (target m source)

def FullGame (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (ha : AcquisitionReady m source) (hr : ResourceReady m source) : Prop :=
  StrategyGame.GameReadout
    (ResourceRuntime.rows (RuntimeComponents.resources m.runtime) (target m source))
    (ResourceRuntime.update (RuntimeComponents.resources m.runtime) (target m source) hr)
    (Entries m source ha) (Withdrawal m source) (PackageAt m source)
    (ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (target m source))
    (ResourceRuntime.Legal (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (target m source))
    (ResourceRuntime.StepLaw (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (target m source) hr)

abbrev FullCertificate (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (ha : AcquisitionReady m source) (hr : ResourceReady m source) :=
  StrategyGame.InvariantCertificate
    (ResourceRuntime.rows (RuntimeComponents.resources m.runtime) (target m source))
    (ResourceRuntime.update (RuntimeComponents.resources m.runtime) (target m source) hr)
    (Entries m source ha) (Withdrawal m source) (PackageAt m source)
    (ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (target m source))
    (ResourceRuntime.Legal (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (target m source))
    (ResourceRuntime.StepLaw (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (target m source) hr)

def PostWithdrawalFullAutonomy (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m source, ∃ hr : ResourceReady m source, FullGame m source ha hr

def FullPass (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m source, ∃ hr : ResourceReady m source,
    Nonempty (FullCertificate m source ha hr)

def PostWithdrawalOperationalAutonomy (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m source, ∃ hr : ResourceReady m source,
    RuntimeComponents.OperationalReadout m.runtimeSchema m.runtime (target m source) ha hr

def OperationalPass (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) : Prop :=
  ∃ ha : AcquisitionReady m source, ∃ hr : ResourceReady m source,
    Nonempty (RuntimeComponents.OperationalCertificate m.runtimeSchema m.runtime (target m source) ha hr)

theorem full_soundness (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV) (h : FullPass m source) :
    PostWithdrawalFullAutonomy m source := by
  obtain ⟨ha,hr,⟨cert⟩⟩ := h
  exact ⟨ha,hr,StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert⟩

theorem operational_soundness (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (h : OperationalPass m source) : PostWithdrawalOperationalAutonomy m source := by
  obtain ⟨ha,hr,⟨cert⟩⟩ := h
  exact ⟨ha,hr,RuntimeComponents.operational_soundness _ _ _ _ _ cert⟩

/-- Exact proof-bearing certificate/game equivalence. This is not decision
completeness of a finite algorithm. The reverse direction constructs the
invariant of plays generated by the successful causal strategy. -/
theorem full_pass_iff_readout (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) : FullPass m source ↔ PostWithdrawalFullAutonomy m source := by
  constructor
  · exact full_soundness m source
  · rintro ⟨ha,hr,hgame⟩
    exact ⟨ha,hr,StrategyGame.game_invariant_completeness hgame⟩

theorem operational_pass_iff_readout (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) : OperationalPass m source ↔ PostWithdrawalOperationalAutonomy m source := by
  constructor
  · exact operational_soundness m source
  · rintro ⟨ha,hr,hgame⟩
    exact ⟨ha,hr,StrategyGame.game_invariant_completeness hgame⟩

/-- Dependence follows at a genuine activated entry, by game induction.
It is not the derivation used by package_soundness. -/
theorem full_autonomy_implies_package (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (h : PostWithdrawalFullAutonomy m source) : IntegratedTargetRealization m source := by
  obtain ⟨ha,hr,hgame⟩ := h
  obtain ⟨entry,he⟩ := hgame.2.1
  exact (StrategyGame.game_entry_package hgame entry he).1

/-- Same causal strategy, dropping only the additional package obligations.
This is game implication, not a projection from a stored operational verdict. -/
theorem full_autonomy_implies_operational
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (h : PostWithdrawalFullAutonomy m source) :
    PostWithdrawalOperationalAutonomy m source := by
  obtain ⟨ha,hr,hw,he,strategy,hs⟩ := h
  refine ⟨ha,hr,hw,he,strategy,?_⟩
  intro entry hentry r past hp
  have hsafe := hs entry hentry r past hp
  exact ⟨hsafe.1.2.1,hsafe.2⟩

/-- All finite declared disturbance words, with the full actual run context
retained. The terminal package is recomputed from the primitive programs on
that run. This does not replace the separately required finite-factor lift
or claim that unselected responses are safe. -/
theorem full_answers_every_word
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (h : PostWithdrawalFullAutonomy m source) :
    ∃ ha : AcquisitionReady m source, ∃ hr : ResourceReady m source,
      ∃ strategy : StrategyGame.Strategy (Registers R RV) D A,
        ∀ entry, Entries m source ha entry → ∀ word : List D,
          ∃ final past,
            StrategyGame.WordExecution
              (ResourceRuntime.rows (RuntimeComponents.resources m.runtime) (target m source))
              (ResourceRuntime.update (RuntimeComponents.resources m.runtime) (target m source) hr)
              strategy [entry] word (final :: past) ∧
            StrategyGame.Play
              (ResourceRuntime.rows (RuntimeComponents.resources m.runtime) (target m source))
              (ResourceRuntime.update (RuntimeComponents.resources m.runtime) (target m source) hr)
              strategy entry (final :: past) ∧
            PackageAt m source final ∧
            ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
              (RuntimeComponents.resources m.runtime) (target m source) final := by
  obtain ⟨ha,hr,_,_,strategy,hs⟩ := h
  refine ⟨ha,hr,strategy,?_⟩
  intro entry he word
  obtain ⟨last,exec,hplay⟩ := StrategyGame.strategy_answers_word
    (fun r past hp d => ((hs entry he r past hp).2.2 d).2.1.2.2)
    entry [] StrategyGame.Play.initial word
  cases last with
  | nil => cases hplay
  | cons final past =>
    exact ⟨final,past,exec,hplay,(hs entry he final past hplay).1,
      (hs entry he final past hplay).2.1⟩

theorem failed_target_clause_no_full
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (c : ClauseDispatcher.Kind)
    (bad : ¬ (m.package.clauses.rule c).accept (target m source)) :
    ¬ PostWithdrawalFullAutonomy m source :=
  fun h => bad ((full_autonomy_implies_package m source h).2.2 c)

theorem full_disturbances_nonempty (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (h : PostWithdrawalFullAutonomy m source) : m.runtime.execution.disturbances ≠ [] :=
  h.choose_spec.choose_spec.1.1.2.2.1

theorem operational_disturbances_nonempty (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (h : PostWithdrawalOperationalAutonomy m source) : m.runtime.execution.disturbances ≠ [] :=
  h.choose_spec.choose_spec.1.1.2.2.1

omit [DecidableEq Stage] in
theorem acquisition_resource_update (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (ha : AcquisitionReady m source) (hr : ResourceReady m source)
    (r : Registers R RV) (d : D) (act : A) (o : O) :
    AcquisitionExecution.update (RuntimeComponents.acquisition m.runtime) (target m source) ha r d act o =
      ResourceRuntime.update (RuntimeComponents.resources m.runtime) (target m source) hr r d act o := rfl

theorem source_absent_no_operational (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (receiver : AcquisitionExecution.Receiver)
    (he : (RuntimeComponents.acquisition m.runtime).receiver.read (target m source) = some receiver)
    (absent : receiver.sourcePresent = false) : ¬ PostWithdrawalOperationalAutonomy m source := by
  rintro ⟨ha,hr,hgame⟩
  exact RuntimeComponents.source_absent_no_operational_readout _ _ _ ha hr receiver he absent hgame

theorem source_absent_no_full (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (receiver : AcquisitionExecution.Receiver)
    (he : (RuntimeComponents.acquisition m.runtime).receiver.read (target m source) = some receiver)
    (absent : receiver.sourcePresent = false) : ¬ PostWithdrawalFullAutonomy m source := by
  rintro ⟨ha,hr,hgame⟩
  exact StrategyGame.no_entries_no_game
    (fun r => AcquisitionExecution.source_absent_no_entry _ _ _ ha receiver he absent r) hgame

theorem missing_run_primitive_no_full (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId) (source : Assignment SC SV)
    (ha : AcquisitionReady m source) (entry : Registers R RV) (he : Entries m source ha entry)
    (clause : ClauseDispatcher.Kind) (k : TC) (hk : k ∈ (m.package.clauses.rule clause).scope)
    (missing : runAssignment m source entry k = none) : ¬ PostWithdrawalFullAutonomy m source := by
  rintro ⟨ha',hr,hgame⟩
  have hp := (StrategyGame.game_entry_package hgame entry he).2.2 clause
  exact (m.package.clauses.rule clause).missing_rejected _ k hk missing hp

/-- Missing static primitives reject BOTH games before any total helper is
used. These quantify every consumed resource/read, row and update dependency,
rather than assuming readiness alongside an incompatible absence premise. -/
theorem missing_resource_no_games (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (k : TC)
    (hk : k ∈ (RuntimeComponents.resources m.runtime).readDependencies)
    (hm : target m source k = none) :
    ¬ PostWithdrawalFullAutonomy m source ∧ ¬ PostWithdrawalOperationalAutonomy m source := by
  have bad := ResourceRuntime.missing_read_rejected (RuntimeComponents.resources m.runtime) (target m source) k hk hm
  exact ⟨fun ⟨_,hr,_⟩ => bad hr,fun ⟨_,hr,_⟩ => bad hr⟩

theorem missing_row_no_games (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (k : TC)
    (hk : k ∈ m.runtime.execution.row.dependencies) (hm : target m source k = none) :
    ¬ PostWithdrawalFullAutonomy m source ∧ ¬ PostWithdrawalOperationalAutonomy m source := by
  have bad := ResourceRuntime.missing_row_rejected (RuntimeComponents.resources m.runtime) (target m source) k hk hm
  exact ⟨fun ⟨_,hr,_⟩ => bad hr,fun ⟨_,hr,_⟩ => bad hr⟩

theorem missing_update_no_games (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (reg : R) (k : TC)
    (hk : k ∈ (m.runtime.execution.program reg).dependencies) (hm : target m source k = none) :
    ¬ PostWithdrawalFullAutonomy m source ∧ ¬ PostWithdrawalOperationalAutonomy m source := by
  have bad := ResourceRuntime.missing_update_rejected (RuntimeComponents.resources m.runtime) (target m source) reg k hk hm
  exact ⟨fun ⟨_,hr,_⟩ => bad hr,fun ⟨_,hr,_⟩ => bad hr⟩

/-- Acquisition has its own complete dependency check. These guards also
reject operational autonomy, whose package-free resource scope alone need
not include the acquisition histories, events or receiver. -/
theorem missing_acquisition_no_games
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (k : TC)
    (hk : k ∈ (RuntimeComponents.acquisition m.runtime).dependencies)
    (hm : target m source k = none) :
    ¬ PostWithdrawalFullAutonomy m source ∧ ¬ PostWithdrawalOperationalAutonomy m source := by
  have bad := AcquisitionExecution.missing_dependency_rejected
    (RuntimeComponents.acquisition m.runtime) (target m source) k hk hm
  exact ⟨fun ⟨ha,_,_⟩ => bad ha,fun ⟨ha,_,_⟩ => bad ha⟩

theorem missing_initializer_no_games
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (reg : R) (k : TC)
    (hk : k ∈ (m.runtime.acquisition.initializer reg).dependencies)
    (hm : target m source k = none) :
    ¬ PostWithdrawalFullAutonomy m source ∧ ¬ PostWithdrawalOperationalAutonomy m source := by
  have bad := AcquisitionExecution.missing_initializer_rejected
    (RuntimeComponents.acquisition m.runtime) (target m source) reg k hk hm
  exact ⟨fun ⟨ha,_,_⟩ => bad ha,fun ⟨ha,_,_⟩ => bad ha⟩

theorem missing_receiver_program_no_games
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (reg : R) (k : TC)
    (hk : k ∈ (m.runtime.acquisition.receive reg).dependencies)
    (hm : target m source k = none) :
    ¬ PostWithdrawalFullAutonomy m source ∧ ¬ PostWithdrawalOperationalAutonomy m source := by
  have bad := AcquisitionExecution.missing_receiver_program_rejected
    (RuntimeComponents.acquisition m.runtime) (target m source) reg k hk hm
  exact ⟨fun ⟨ha,_,_⟩ => bad ha,fun ⟨ha,_,_⟩ => bad ha⟩

/-- A missing view rejects existence of a ready entry. Readiness is not
assumed alongside the incompatible missing-view premise. -/
theorem missing_entry_view_no_games
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV)
    (hm : m.runtime.acquisition.histories.read (target m source) = none ∨
      m.runtime.acquisition.routes.read (target m source) = none ∨
      m.runtime.acquisition.events.read (target m source) = none ∨
      m.runtime.acquisition.realized.read (target m source) = none ∨
      m.runtime.acquisition.receiver.read (target m source) = none) :
    ¬ PostWithdrawalFullAutonomy m source ∧ ¬ PostWithdrawalOperationalAutonomy m source := by
  have bad : ∀ ha : AcquisitionReady m source, ¬ ∃ r, Entries m source ha r := by
    intro ha
    rintro ⟨r,he⟩
    exact AcquisitionExecution.missing_entry_view _ _ _ r hm ⟨ha,he⟩
  constructor <;> rintro ⟨ha,_,game⟩ <;> exact bad ha game.2.1

theorem entry_resource_failure_no_full
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (ha : AcquisitionReady m source) (entry : Registers R RV)
    (he : Entries m source ha entry)
    (bad : ¬ ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (target m source) entry) :
    ¬ PostWithdrawalFullAutonomy m source := by
  rintro ⟨ha',hr,hgame⟩
  exact StrategyGame.entry_resource_failure_no_game entry he bad hgame

theorem entry_resource_failure_no_operational
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (ha : AcquisitionReady m source) (entry : Registers R RV)
    (he : Entries m source ha entry)
    (bad : ¬ ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (target m source) entry) :
    ¬ PostWithdrawalOperationalAutonomy m source := by
  rintro ⟨ha',hr,hgame⟩
  exact StrategyGame.entry_resource_failure_no_game entry he bad hgame

/-- A genuine entry and one declared disturbance with no legal owned response
reject both semantic readouts, independently of any choice of invariant. -/
theorem missing_response_no_games
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (ha : AcquisitionReady m source) (entry : Registers R RV)
    (he : Entries m source ha entry) (d : D)
    (bad : ∀ act, ¬ ResourceRuntime.Legal (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (target m source) entry d act) :
    ¬ PostWithdrawalFullAutonomy m source ∧ ¬ PostWithdrawalOperationalAutonomy m source := by
  constructor <;> rintro ⟨ha',hr,game⟩ <;>
    exact StrategyGame.missing_response_no_game entry he d bad game

theorem invalid_withdrawal_no_games
    (m : Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (source : Assignment SC SV) (bad : ¬ Withdrawal m source) :
    ¬ PostWithdrawalFullAutonomy m source ∧ ¬ PostWithdrawalOperationalAutonomy m source := by
  constructor <;> rintro ⟨_,_,game⟩ <;> exact bad game.1

end CSTTT.TargetTheory.GenericHandoff.PackageRuntime
