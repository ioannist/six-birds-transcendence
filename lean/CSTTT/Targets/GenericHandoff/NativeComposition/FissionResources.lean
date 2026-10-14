import CSTTT.Targets.GenericHandoff.NativeComposition.FissionFuture

/-! The target name is read on every actual semantic entry and every positive
play of the unchanged controller. C5 transports both raw owner and housing
coordinates; external Unit ownership remains external. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
open RegisterInterpreter PublicationReplay CSTTT.TransportTheory

def resourceOwnerExpr (branch : Bool) : Expr Owner MemoryValue Unit (fun _ => ModeExecution.State) Unit CarrierId :=
  .map (renameOwner branch) (PublicationPhysical.ownerExpr true)
theorem resource_owner_evaluation (branch : Bool) (a : Assignment Owner MemoryValue) (p : Input × Input)
    (hp : a true=some p) (x : ModeExecution.Registers) :
    (resourceOwnerExpr branch).eval a x ()=some (branchNames branch
      (if (x ()).2=true then p.1.temporal.resource.owner else p.2.temporal.resource.owner)) := by
  simp only [resourceOwnerExpr,Expr.eval,PublicationPhysical.owner_evaluation true a p hp,
    Option.map_some,branchNames]

theorem every_safe_play_owner (branch : Bool) (entry : ModeExecution.Registers)
    (he : PublicationResources.entries true entry) (x : ModeExecution.Registers) (past : List ModeExecution.Registers)
    (hp : StrategyGame.Play (ResourceRuntime.rows (PublicationResources.runtime true) PublicationResources.assignment)
      (ResourceRuntime.update (PublicationResources.runtime true) PublicationResources.assignment (PublicationResources.ready true))
      PublicationResources.safeController entry (x::past)) :
    (resourceOwnerExpr branch).eval PublicationResources.assignment x ()=some (⟨branchTarget branch⟩ : CarrierId) ∧
    (PublicationResources.runtime true).sourcePresent.eval PublicationResources.assignment x ()=some false := by
  constructor
  · obtain ⟨h,time,rfl⟩ := PublicationResources.every_safe_play_inside true entry he _ hp x past rfl
    rw [resource_owner_evaluation branch PublicationResources.assignment (PublicationExecution.episodePair 0)
      (PublicationExecution.assigned_pair true)]
    cases branch <;> rfl
  · exact PublicationResources.every_safe_play_source_absent true entry he x past hp

abbrev NamedCreditOwner := Sum CarrierId Unit
def namedCreditOwner (ns : Owner → CarrierId) : NativePackagePrimitives.CreditOwner → NamedCreditOwner
  | .inl o => .inl (ns o)
  | .inr u => .inr u
def namedCreditImage (branch : Bool) : NamedCreditOwner → NamedCreditOwner
  | .inl o => .inl (renameOwner branch (PublicationFuture.ownerImage true o))
  | .inr u => .inr u
def namedCreditTables (ns : Owner → CarrierId) (b : NativePackageBundle.Bundle) :=
  let t := (NativeCreditCells.data b).tables
  ProtocolCreditRules.Tables.mk t.edges
    (fun p => namedCreditOwner ns (t.owner p)) (fun p => namedCreditOwner ns (t.housing p))
theorem named_credit_owner_equation (branch : Bool) (o : NativePackagePrimitives.CreditOwner) :
    namedCreditOwner (branchNames branch) (NativePackagePrimitives.translateOwner o)=
      namedCreditImage branch (namedCreditOwner (names true) o) := by
  cases o with
  | inl o => cases branch <;> cases o <;> rfl
  | inr u => rfl

theorem named_raw_credit_transport (branch : Bool) (b : NativePackageBundle.Bundle) :
    ProtocolCreditRules.Transport (namedCreditTables (names true) b)
      (namedCreditTables (branchNames branch) (NativePackageBundle.publishBundle b))
      NativeCreditCells.protocols id id (namedCreditImage branch) := by
  intro p hp
  obtain ⟨he,ho,hh⟩ := PublicationMaps.raw_credit_transport b p hp
  simp only [id_eq] at ho hh
  refine ⟨he,?_,?_⟩
  · change namedCreditImage branch (namedCreditOwner (names true) ((NativeCreditCells.data b).tables.owner p))=
      namedCreditOwner (branchNames branch) ((NativeCreditCells.data (NativePackageBundle.publishBundle b)).tables.owner p)
    rw [←ho,named_credit_owner_equation]
  · change namedCreditImage branch (namedCreditOwner (names true) ((NativeCreditCells.data b).tables.housing p))=
      namedCreditOwner (branchNames branch) ((NativeCreditCells.data (NativePackageBundle.publishBundle b)).tables.housing p)
    rw [←hh,named_credit_owner_equation]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
