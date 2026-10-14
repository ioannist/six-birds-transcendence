import CSTTT.Targets.GenericHandoff.NominalProtocol

/-! Owning nominal-protocol binding, TTH-06 (b).
The specification and primitive reader are constructed from the owning frames.
Only the reference ledger/operator, required resource names and a raw static
source-presence recipe are additional data. Their resource interpretation and
closed C8 dispatcher binding are explicit laws. Nominal autonomy is a defined
protocol-qualified semantic readout, separate from the earlier bare game. -/
namespace CSTTT.TargetTheory.GenericHandoff.NominalHandoff
open RegisterInterpreter

structure Instructions (Cell : Type) (Value : Cell → Type) (S Resource : Type) where
  ledger : OperationalViability.Ledger
  canonicalP : S → S → Nat
  required : List Resource
  sourcePresent : StaticView Cell Value Bool

variable {SC Cell R SR TR S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type}
  {SourceValue : SC → Type} {Value : Cell → Type} {RV : R → Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => OwningHandoff.RawHandoff SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint
local notation "Recipe" => Instructions Cell Value S Resource
variable [DecidableEq S] [DecidableEq O] [DecidableEq Route] [DecidableEq Stage]
  [DecidableEq Id] [DecidableEq Owner] [DecidableEq Resource]

def specification (m : Model) (r : Recipe) : NominalProtocol.Specification S A O HF Route Stage Id Owner Resource :=
  ⟨m.frames.sourceSchema.base.destination,
    ⟨m.frames.targetSchema.base.states,m.frames.targetSchema.base.actions,
      m.frames.targetSchema.base.destination,m.frames.targetSchema.base.rowScale,
      m.frames.targetSchema.owner,r.ledger,r.canonicalP⟩,
    m.frames.targetSchema.base.outcomes,m.frames.targetSchema.routes,m.frames.targetSchema.stages,
    m.frames.entry,m.frames.exit,m.frames.exitEvent,
    m.frames.targetSchema.stageAdvance,m.frames.targetSchema.tickAdvance,r.required⟩

def metadata (m : Model) (r : Recipe) : StaticView Cell Value (NominalProtocol.Metadata Resource) :=
  ⟨.map (fun x => ⟨x.1.removedRoles,x.1.retained,x.2⟩)
    (.pair (StaticView.ofCell m.runtime.resource.withdrawal).instruction r.sourcePresent.instruction)⟩

def operationalBindings (m : Model) : OperationalViability.Bindings Cell Value S A O Owner :=
  ⟨m.frames.targetCells.rows,m.frames.targetCells.policy,m.frames.targetCells.resource,m.frames.targetCells.ledger⟩

/-- All-context raw recipe equations and closed dispatcher equality; no verdict. -/
def Laws (m : Model) (r : Recipe) (a : Assignment Cell Value) : Prop :=
  m.package.clauses.rule .c8 = ClauseDispatcher.Rule.c8 inferInstance inferInstance inferInstance
    (specification m r).viability (specification m r).outcomes (operationalBindings m) ∧
  (∀ run, m.runtime.resource.sourcePresent.eval a run () = r.sourcePresent.read a) ∧
  ∀ run, m.runtime.resource.required.eval a run () = some r.required

/-- Withdrawal metadata is decoded from the SAME owning resource instructions. -/
def Pass (m : Model) (r : Recipe) (a : Assignment Cell Value) : Prop :=
  ∃ wd, (metadata m r).read a = some wd ∧
    NominalProtocol.Pass (specification m r) wd (NominalProtocol.views m.frames) a

variable [DecidableEq Cell]
def FullAutonomy (m : Model) (r : Recipe) (a : Assignment SC SourceValue) : Prop :=
  Pass m r (OwningHandoff.target m a) ∧ OwningHandoff.PostWithdrawalFullAutonomy m a
def OperationalAutonomy (m : Model) (r : Recipe) (a : Assignment SC SourceValue) : Prop :=
  Pass m r (OwningHandoff.target m a) ∧ OwningHandoff.PostWithdrawalOperationalAutonomy m a

def FullSubcheck (m : Model) (r : Recipe) (a : Assignment SC SourceValue) : Prop :=
  Pass m r (OwningHandoff.target m a) ∧ OwningHandoff.FullSubcheck m a
def OperationalSubcheck (m : Model) (r : Recipe) (a : Assignment SC SourceValue) : Prop :=
  Pass m r (OwningHandoff.target m a) ∧ OwningHandoff.OperationalSubcheck m a

theorem full_subcheck_iff (m : Model) (r : Recipe) (a : Assignment SC SourceValue) :
    FullSubcheck m r a ↔ FullAutonomy m r a :=
  and_congr_right (fun _ => OwningHandoff.full_subcheck_iff m a)
theorem operational_subcheck_iff (m : Model) (r : Recipe) (a : Assignment SC SourceValue) :
    OperationalSubcheck m r a ↔ OperationalAutonomy m r a :=
  and_congr_right (fun _ => OwningHandoff.operational_subcheck_iff m a)

omit [DecidableEq Cell] in
theorem missing_primitive_no_pass (m : Model) (r : Recipe) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ (NominalProtocol.reader (NominalProtocol.views m.frames)).dependencies) (hm : a k = none) :
    ¬ Pass m r a := by
  rintro ⟨wd,_,h⟩
  exact NominalProtocol.missing_no_pass _ wd _ a k hk hm h

omit [DecidableEq Cell] in
theorem missing_metadata_no_pass (m : Model) (r : Recipe) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ (metadata m r).dependencies) (hm : a k = none) : ¬ Pass m r a := by
  rintro ⟨wd,hd,_⟩
  rw [(metadata m r).missing a k hk hm] at hd
  contradiction

omit [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route]
  [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner] [DecidableEq Resource] in
theorem shared_primitives (m : Model) : (NominalProtocol.views m.frames).rows = m.frames.targetCells.rows ∧
    (NominalProtocol.views m.frames).sourceRows = m.frames.sourceCells.rows ∧
    (NominalProtocol.views m.frames).receiver = m.frames.receiver := ⟨rfl,rfl,rfl⟩

omit [DecidableEq Cell] in
theorem source_present_no_pass (m : Model) (r : Recipe) (a : Assignment Cell Value)
    (present : r.sourcePresent.read a = some true) : ¬ Pass m r a := by
  rintro ⟨wd,hd,h⟩
  have present' := present
  change r.sourcePresent.instruction.eval a RegisterInitialization.noRegisters () = some true at present'
  simp only [metadata,StaticView.read,Expr.eval,present'] at hd
  cases hw : (StaticView.ofCell m.runtime.resource.withdrawal).instruction.eval a RegisterInitialization.noRegisters () with
  | none => simp [hw] at hd
  | some w =>
    simp only [hw] at hd
    have equal := Option.some.inj hd
    subst wd
    exact NominalProtocol.source_present_no_pass _ _ _ _ rfl h

variable [DecidableEq P] [DecidableEq Q]
def HandoffPass_F (m : Model) (r : Recipe) (a : Assignment SC SourceValue) : Prop :=
  Laws m r (OwningHandoff.target m a) ∧ Pass m r (OwningHandoff.target m a) ∧ OwningHandoff.HandoffPass_F m a
def HandoffPass_O (m : Model) (r : Recipe) (a : Assignment SC SourceValue) : Prop :=
  Laws m r (OwningHandoff.target m a) ∧ Pass m r (OwningHandoff.target m a) ∧ OwningHandoff.HandoffPass_O m a

theorem soundness_F (m : Model) (r : Recipe) (a : Assignment SC SourceValue) (h : HandoffPass_F m r a) :
    OwningHandoff.IntegratedTargetRealization m a ∧ OwningHandoff.StrictTemporalLineage m a ∧ FullAutonomy m r a := by
  have lanes := OwningHandoff.temporalFIACHCertificateSoundness_generic_F m a h.2.2
  exact ⟨lanes.1,lanes.2.1,h.2.1,lanes.2.2⟩

theorem soundness_O (m : Model) (r : Recipe) (a : Assignment SC SourceValue) (h : HandoffPass_O m r a) :
    OwningHandoff.IntegratedTargetRealization m a ∧ OwningHandoff.StrictTemporalLineage m a ∧ OperationalAutonomy m r a := by
  have lanes := OwningHandoff.temporalFIACHCertificateSoundness_generic_O m a h.2.2
  exact ⟨lanes.1,lanes.2.1,h.2.1,lanes.2.2⟩

end CSTTT.TargetTheory.GenericHandoff.NominalHandoff
