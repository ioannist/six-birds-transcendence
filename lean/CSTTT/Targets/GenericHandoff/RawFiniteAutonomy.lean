import CSTTT.Targets.GenericHandoff.PackageRuntime
import CSTTT.Targets.GenericHandoff.GameAutonomyTransport

/-! Raw finite-factor TTH-05 transport. The controlled system, withdrawal,
package, ownership and advancement relations are DEFINED from the shared raw
package/runtime and typed factor instructions. A factor step is the exact
image relation of an actual legal positive-support branch, not a chosen
representative or a caller-supplied transition predicate.

The remaining factor package/resource laws are checked, proof-bearing
per-instance obligations on ALL run contexts. No finite-context assumption or
decision completeness is claimed. This transport is not the final RawHandoff:
the finite frame still needs to be bound at that raw interface and instantiated
on POS-04's arbitrary partial assignments.
-/
namespace CSTTT.TargetTheory.GenericHandoff.RawFiniteAutonomy
open RegisterInterpreter CSTTT.AutonomyTheory

structure Frame (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (X D A Resource : Type) where
  states : FiniteEnum X
  disturbances : FiniteEnum D
  actions : FiniteEnum A
  projection : Expr Cell Value R RV Unit X
  cells : (k : Cell) → Expr Cell Value Unit (fun _ => Unit) X (Value k)
  maintenance : Expr Cell Value Unit (fun _ => Unit) X (List Resource)
  actionOwner : Expr Cell Value Unit (fun _ => Unit) A CarrierId
  resourceOwner : Expr Cell Value Unit (fun _ => Unit) Resource CarrierId
  resourceId : Resource → ResourceId

variable {SC TC R X D A O P Factor Resource Residue Stage Id History RouteId : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type}
  [DecidableEq TC] [DecidableEq Stage]

local notation "Model" => PackageRuntime.Raw SC TC SV TV R RV D A O P Factor Resource Residue Stage Id History RouteId
local notation "FactorFrame" => Frame TC TV R RV X D A Resource

/-- Only evidence on interpreted raw data. Disturbance/action enumerations are
checked against the SAME execution used by acquisition and the resource game. -/
structure Checked (m : Model) (f : FactorFrame) (source : Assignment SC SV) : Prop where
  ready : PackageRuntime.ResourceReady m source
  withdrawal : PackageRuntime.Withdrawal m source
  projection : Complete f.projection.dependencies (PackageRuntime.target m source)
  maintenance : Complete f.maintenance.dependencies (PackageRuntime.target m source)
  actionOwner : Complete f.actionOwner.dependencies (PackageRuntime.target m source)
  resourceOwner : Complete f.resourceOwner.dependencies (PackageRuntime.target m source)
  identifiers : Function.Injective f.resourceId
  carriers : RuntimeComponents.CarrierCheck m.runtimeSchema
  disturbances : f.disturbances.elems = m.runtime.execution.disturbances
  actions : f.actions.elems = m.runtime.execution.actions

noncomputable def readEnv {Env Y : Type}
    (e : Expr TC TV Unit (fun _ => Unit) Env Y) (a : Assignment TC TV)
    (h : Complete e.dependencies a) (v : Env) : Y :=
  Classical.choose (e.present_of_complete a h (fun _ => ()) v)

omit [DecidableEq TC] [DecidableEq Stage] in
theorem readEnv_eq {Env Y : Type}
    (e : Expr TC TV Unit (fun _ => Unit) Env Y) (a : Assignment TC TV)
    (h : Complete e.dependencies a) (v : Env) :
    e.eval a (fun _ => ()) v = some (readEnv e a h v) :=
  Classical.choose_spec (e.present_of_complete a h (fun _ => ()) v)

noncomputable def project (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) : Registers R RV → X :=
  RegisterFuture.read f.projection (PackageRuntime.target m source) h.projection

def factorAssignment (m : Model) (f : FactorFrame) (source : Assignment SC SV) (s : X) : Assignment TC TV :=
  fun k => (f.cells k).eval (PackageRuntime.target m source) (fun _ => ()) s

def FactorPackage (m : Model) (f : FactorFrame) (source : Assignment SC SV) (s : X) : Prop :=
  PackageRuntime.IntegratedTargetRealization m source ∧
  m.package.clauses.accept (factorAssignment m f source s)

noncomputable def required (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (s : X) : List Resource :=
  readEnv f.maintenance (PackageRuntime.target m source) h.maintenance s

noncomputable def withdrawalData (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) : ResourceRuntime.Withdrawal Resource :=
  Classical.choose h.withdrawal.2

omit [DecidableEq Stage] in
theorem withdrawal_fields (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) :
    let w := withdrawalData m f source h
    (RuntimeComponents.resources m.runtime).withdrawal.read (PackageRuntime.target m source) = some w ∧
    (∀ role ∈ ResourceRuntime.roles, role ∈ w.removedRoles) ∧
    (∀ role ∈ w.removedRoles, role ∈ ResourceRuntime.roles) ∧
    (∀ role ∈ ResourceRuntime.roles, w.roleResources role ⊆ w.removed) ∧
    w.removed ⊆ m.runtimeSchema.resources ∧ w.retained ⊆ m.runtimeSchema.resources ∧
    (∀ res ∈ w.removed, res ∉ w.retained) := Classical.choose_spec h.withdrawal.2

noncomputable def withdrawalSpec (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) : WithdrawalSpec where
  removedResources := (withdrawalData m f source h).removed.map f.resourceId
  retainedResources := (withdrawalData m f source h).retained.map f.resourceId
  disjoint := by
    intro rid hm hret
    obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
    obtain ⟨s,hs,he'⟩ := List.mem_map.mp hret
    have hrs := h.identifiers (he.trans he'.symm)
    subst s
    exact (withdrawal_fields m f source h).2.2.2.2.2.2 r hr hs
  sourceRemoved := ResourceRuntime.Role.source ∈ (withdrawalData m f source h).removedRoles
  bridgeRemoved := ResourceRuntime.Role.migrationBridge ∈ (withdrawalData m f source h).removedRoles
  migrationControllerRemoved := ResourceRuntime.Role.migrationController ∈ (withdrawalData m f source h).removedRoles
  externalDecoderRemoved := ResourceRuntime.Role.externalDecoder ∈ (withdrawalData m f source h).removedRoles
  externalSchedulerRemoved := ResourceRuntime.Role.externalScheduler ∈ (withdrawalData m f source h).removedRoles
  undeclaredRepairRemoved := ResourceRuntime.Role.undeclaredRepair ∈ (withdrawalData m f source h).removedRoles

abbrev rawRows (m : Model) (source : Assignment SC SV) :=
  ResourceRuntime.rows (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source)
noncomputable abbrev rawUpdate (m : Model) (f : FactorFrame) (source : Assignment SC SV) (h : Checked m f source) :=
  ResourceRuntime.update (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) h.ready
abbrev rawLegal (m : Model) (source : Assignment SC SV) :=
  ResourceRuntime.Legal (RuntimeComponents.resourceSchema m.runtimeSchema)
    (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source)
noncomputable abbrev rawLaw (m : Model) (f : FactorFrame) (source : Assignment SC SV) (h : Checked m f source) :=
  ResourceRuntime.StepLaw (RuntimeComponents.resourceSchema m.runtimeSchema)
    (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) h.ready

noncomputable def system (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) : ControlledSystem where
  carrier := ⟨m.runtimeSchema.target,X,f.states⟩
  Disturbance := D
  Action := A
  disturbanceEnum := f.disturbances
  actionEnum := f.actions
  step := fun s d act t => ∃ r o, project m f source h r = s ∧
    rawLegal m source r d act ∧ StrategyGame.PositiveSupport (rawRows m source) r d act o ∧
    project m f source h (rawUpdate m f source h r d act o) = t
  packageValid := FactorPackage m f source
  actionOwner := readEnv f.actionOwner (PackageRuntime.target m source) h.actionOwner
  maintenanceResources := fun s => (required m f source h s).map f.resourceId

/-- Actual updater/advancement witness, not a strictness flag on the recurrent
finite factor. The counters remain on the unbounded run space. -/
noncomputable def advancement (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (s : X) (d : D) (act : A) (t : X) : Prop :=
  ∃ r o, project m f source h r = s ∧
    project m f source h (rawUpdate m f source h r d act o) = t ∧ rawLaw m f source h r d act o

noncomputable def owner (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (rid : ResourceId) : CarrierId :=
  match ((withdrawalData m f source h).retained.find? (fun res => f.resourceId res == rid)) with
  | none => m.runtimeSchema.source
  | some res => readEnv f.resourceOwner (PackageRuntime.target m source) h.resourceOwner res

noncomputable def factor (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) : GameAutonomyTransport.FactorData :=
  ⟨system m f source h,withdrawalSpec m f source h,owner m f source h,
    advancement m f source h,advancement m f source h,
    RuntimeComponents.CarrierCheck m.runtimeSchema,
    f.disturbances.elems = m.runtime.execution.disturbances ∧ m.runtime.execution.disturbances ≠ []⟩

/-- These are the exact outstanding factor/coherence equations, quantified
over every package/resource-relevant run. No relevance premise is assumed. -/
structure Lift (m : Model) (f : FactorFrame) (source : Assignment SC SV) (h : Checked m f source) : Prop where
  cells : ∀ r, PackageRuntime.PackageAt m source r →
    factorAssignment m f source (project m f source h r) = PackageRuntime.runAssignment m source r
  resources : ∀ r, ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
    (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) r →
    (RuntimeComponents.resources m.runtime).required.eval (PackageRuntime.target m source) r () =
      some (required m f source h (project m f source h r))
  ownership : ∀ res ∈ (withdrawalData m f source h).retained,
    readEnv f.resourceOwner (PackageRuntime.target m source) h.resourceOwner res = m.runtimeSchema.target
  accountOwners : ∀ r accounts,
    ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) r →
    (RuntimeComponents.resources m.runtime).accounts.eval (PackageRuntime.target m source) r () = some accounts →
    ∀ res ∈ (withdrawalData m f source h).retained,
      (accounts res).owner = some (readEnv f.resourceOwner (PackageRuntime.target m source) h.resourceOwner res)
  action : ∀ r d act, ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
    (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) r → rawLegal m source r d act →
    readEnv f.actionOwner (PackageRuntime.target m source) h.actionOwner act = m.runtimeSchema.target

omit [DecidableEq Stage] in
theorem required_retained (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (hl : Lift m f source h) (r : Registers R RV)
    (hr : ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) r) :
    required m f source h (project m f source h r) ⊆ (withdrawalData m f source h).retained := by
  have hf := hl.resources r hr
  obtain ⟨accounts,req,w,_,he,hw,_,_,_,hs,_⟩ := hr
  have heq := Option.some.inj (he.symm.trans hf)
  have hwq := Option.some.inj (hw.symm.trans (withdrawal_fields m f source h).1)
  simpa only [← heq,← hwq] using hs

omit [DecidableEq Stage] in
theorem retained_actual_ownership (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (hl : Lift m f source h) (r : Registers R RV)
    (accounts : Resource → ResourceRuntime.Account)
    (hr : ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) r)
    (he : (RuntimeComponents.resources m.runtime).accounts.eval (PackageRuntime.target m source) r () = some accounts)
    (res : Resource) (retained : res ∈ (withdrawalData m f source h).retained) :
    (accounts res).owner = some m.runtimeSchema.target :=
  (hl.accountOwners r accounts hr he res retained).trans (congrArg some (hl.ownership res retained))

omit [DecidableEq Stage] in
theorem projection_laws (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (hl : Lift m f source h) :
    GameAutonomyTransport.ProjectionLaws (factor m f source h) (rawRows m source)
      (rawUpdate m f source h) (PackageRuntime.Withdrawal m source) (PackageRuntime.PackageAt m source)
      (ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
        (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source))
      (rawLegal m source) (rawLaw m f source h) (project m f source h) := by
  constructor
  all_goals try (intro _; exact (withdrawal_fields m f source h).2.1 _ (by decide))
  · intro _; exact h.carriers
  · intro _; exact ⟨h.disturbances,h.withdrawal.1.2.2.1⟩
  · intro r hr
    exact ⟨hr.1,by simpa only [hl.cells r hr] using hr.2.2⟩
  · intro r hr rid hm
    obtain ⟨res,hres,he⟩ := List.mem_map.mp hm
    exact List.mem_map.mpr ⟨res,required_retained m f source h hl r hr hres,he⟩
  · intro _ rid hm
    obtain ⟨res,hres,he⟩ := List.mem_map.mp hm
    change owner m f source h rid = m.runtimeSchema.target
    cases hf : (withdrawalData m f source h).retained.find? (fun r => f.resourceId r == rid) with
    | none =>
      have hs : ((withdrawalData m f source h).retained.find? (fun r => f.resourceId r == rid)).isSome = true :=
        List.find?_isSome.mpr ⟨res,hres,by change (f.resourceId res == rid) = true; exact beq_iff_eq.mpr he⟩
      rw [hf] at hs
      contradiction
    | some res' => simpa only [owner,hf] using hl.ownership res' (List.mem_of_find?_eq_some hf)
  · exact hl.action
  · intro r d act o hlegal hs
    exact ⟨r,o,rfl,hlegal,hs,rfl⟩
  · intro r d act o hs
    exact ⟨r,o,rfl,rfl,hs⟩
  · intro r d act o hs
    exact ⟨r,o,rfl,rfl,hs⟩

/-- Every activated realized entry, with the invariant constructed from the
causal game and EVERY actual support branch preserved before projection. -/
theorem each_entry_exact (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (hl : Lift m f source h)
    (ha : PackageRuntime.AcquisitionReady m source)
    (hg : PackageRuntime.FullGame m source ha h.ready) :
    ∃ cert : PackageRuntime.FullCertificate m source ha h.ready,
      ∀ entry, PackageRuntime.Entries m source ha entry →
        Nonempty (ExactAutonomyCertificate (GameAutonomyTransport.projectedData
          (factor m f source h) cert (project m f source h) entry)) :=
  GameAutonomyTransport.game_each_entry_exact (factor m f source h) (project m f source h)
    (projection_laws m f source h hl) hg

theorem each_entry_words (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (hl : Lift m f source h)
    (ha : PackageRuntime.AcquisitionReady m source)
    (hg : PackageRuntime.FullGame m source ha h.ready) :
    ∃ cert : PackageRuntime.FullCertificate m source ha h.ready,
      ∀ entry, PackageRuntime.Entries m source ha entry → ∀ word : List D,
        ∃ y, ControlledRun (GameAutonomyTransport.projectedData
          (factor m f source h) cert (project m f source h) entry)
          (project m f source h entry) word y ∧ FactorPackage m f source y :=
  GameAutonomyTransport.game_each_entry_finite_words (factor m f source h) (project m f source h)
    (projection_laws m f source h hl) hg

theorem all_support (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (hl : Lift m f source h)
    (ha : PackageRuntime.AcquisitionReady m source)
    (cert : PackageRuntime.FullCertificate m source ha h.ready)
    (r : Registers R RV) (hr : cert.inside r) (d : D) :
    ∃ act, (system m f source h).actionOwner act = m.runtimeSchema.target ∧
      StrategyGame.Normalized (rawRows m source) r d act ∧
      ∀ o, StrategyGame.PositiveSupport (rawRows m source) r d act o →
        cert.inside (rawUpdate m f source h r d act o) ∧
        (system m f source h).step (project m f source h r) d act
          (project m f source h (rawUpdate m f source h r d act o)) ∧
        advancement m f source h (project m f source h r) d act
          (project m f source h (rawUpdate m f source h r d act o)) ∧
        advancement m f source h (project m f source h r) d act
          (project m f source h (rawUpdate m f source h r d act o)) :=
  GameAutonomyTransport.projected_response_all_support (factor m f source h) cert
    (project m f source h) (projection_laws m f source h hl) r hr d

inductive InputField where | projection | maintenance | actionOwner | resourceOwner
  deriving DecidableEq

def dependencies (f : FactorFrame) : InputField → List TC
  | .projection => f.projection.dependencies
  | .maintenance => f.maintenance.dependencies
  | .actionOwner => f.actionOwner.dependencies
  | .resourceOwner => f.resourceOwner.dependencies

omit [DecidableEq Stage] in
theorem missing_field_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (field : InputField) (k : TC) (hk : k ∈ dependencies f field)
    (hm : PackageRuntime.target m source k = none) : ¬ Checked m f source := by
  intro h
  have present : Complete (dependencies f field) (PackageRuntime.target m source) := by
    cases field with
    | projection => exact h.projection
    | maintenance => exact h.maintenance
    | actionOwner => exact h.actionOwner
    | resourceOwner => exact h.resourceOwner
  have hp := present k hk
  rw [hm] at hp
  contradiction

omit [DecidableEq Stage] in
theorem aliased_resource_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (r s : Resource) (different : r ≠ s) (aliasing : f.resourceId r = f.resourceId s) :
    ¬ Checked m f source := fun h => different (h.identifiers aliasing)

omit [DecidableEq Stage] in
theorem empty_disturbance_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (hm : m.runtime.execution.disturbances = []) : ¬ Checked m f source :=
  fun h => h.withdrawal.1.2.2.1 hm

omit [DecidableEq Stage] in
theorem wrong_action_owner_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (r : Registers R RV) (d : D) (act : A)
    (hr : ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) r)
    (legal : rawLegal m source r d act)
    (wrong : readEnv f.actionOwner (PackageRuntime.target m source) h.actionOwner act ≠ m.runtimeSchema.target) :
    ¬ Lift m f source h := fun hl => wrong (hl.action r d act hr legal)

omit [DecidableEq Stage] in
theorem wrong_resource_owner_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (res : Resource) (retained : res ∈ (withdrawalData m f source h).retained)
    (wrong : readEnv f.resourceOwner (PackageRuntime.target m source) h.resourceOwner res ≠ m.runtimeSchema.target) :
    ¬ Lift m f source h := fun hl => wrong (hl.ownership res retained)

omit [DecidableEq Stage] in
theorem changed_account_owner_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (r : Registers R RV) (accounts : Resource → ResourceRuntime.Account)
    (hr : ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) r)
    (he : (RuntimeComponents.resources m.runtime).accounts.eval (PackageRuntime.target m source) r () = some accounts)
    (res : Resource) (retained : res ∈ (withdrawalData m f source h).retained)
    (bad : (accounts res).owner ≠ some (readEnv f.resourceOwner
      (PackageRuntime.target m source) h.resourceOwner res)) : ¬ Lift m f source h :=
  fun hl => bad (hl.accountOwners r accounts hr he res retained)

omit [DecidableEq Stage] in
theorem omitted_resource_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (r : Registers R RV)
    (hr : ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) r)
    (res : Resource) (used : res ∈ required m f source h (project m f source h r))
    (removed : res ∉ (withdrawalData m f source h).retained) : ¬ Lift m f source h :=
  fun hl => removed (required_retained m f source h hl r hr used)

omit [DecidableEq Stage] in
theorem changed_factor_cell_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (r : Registers R RV) (hp : PackageRuntime.PackageAt m source r)
    (k : TC) (bad : factorAssignment m f source (project m f source h r) k ≠
      PackageRuntime.runAssignment m source r k) : ¬ Lift m f source h :=
  fun hl => bad (congrFun (hl.cells r hp) k)

omit [DecidableEq Stage] in
theorem changed_resource_table_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (h : Checked m f source) (r : Registers R RV)
    (hr : ResourceRuntime.ResourceClosed (RuntimeComponents.resourceSchema m.runtimeSchema)
      (RuntimeComponents.resources m.runtime) (PackageRuntime.target m source) r)
    (bad : (RuntimeComponents.resources m.runtime).required.eval (PackageRuntime.target m source) r () ≠
      some (required m f source h (project m f source h r))) : ¬ Lift m f source h :=
  fun hl => bad (hl.resources r hr)

omit [DecidableEq Stage] in
/-- Reject the factor package itself; readiness is not assumed together with
the contradictory absence of a needed factor primitive. -/
theorem missing_factor_cell_guard (m : Model) (f : FactorFrame) (source : Assignment SC SV)
    (s : X) (clause : ClauseDispatcher.Kind) (k : TC)
    (hk : k ∈ (m.package.clauses.rule clause).scope)
    (hm : factorAssignment m f source s k = none) : ¬ FactorPackage m f source s :=
  fun hp => (m.package.clauses.rule clause).missing_rejected _ k hk hm (hp.2 clause)

end CSTTT.TargetTheory.GenericHandoff.RawFiniteAutonomy
