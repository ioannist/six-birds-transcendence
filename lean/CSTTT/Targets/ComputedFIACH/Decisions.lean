import CSTTT.POS04.Assigned.PackageControls
set_option synthInstance.maxSize 4096

/-! Executable finite decisions for the existing assigned clause semantics.
C1's universal fixed-distribution conclusion is DERIVED using `c1_accept_iff_gate`,
not enumerated or replaced by a flag. Enumeration is over the existing raw types.
-/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

class AuditEnum (α : Type) where
  values : List α
  complete : ∀ x, x ∈ values

instance finiteForall {α : Type} [AuditEnum α] (p : α → Prop) [DecidablePred p] :
    Decidable (∀ x, p x) :=
  decidable_of_iff (∀ x ∈ AuditEnum.values, p x)
    ⟨fun h x => h x (AuditEnum.complete x),fun h x _ => h x⟩
instance finiteExists {α : Type} [AuditEnum α] (p : α → Prop) [DecidablePred p] :
    Decidable (∃ x, p x) :=
  decidable_of_iff (∃ x ∈ AuditEnum.values, p x)
    ⟨fun ⟨x,_,h⟩ => ⟨x,h⟩,fun ⟨x,h⟩ => ⟨x,AuditEnum.complete x,h⟩⟩
instance finiteFunctionEq {α β : Type} [AuditEnum α] [DecidableEq β] :
    DecidableEq (α → β) := fun f g =>
  decidable_of_iff (∀ x, f x = g x) ⟨fun h => funext h,fun h x => congrFun h x⟩

instance : AuditEnum KState := ⟨kernel,by intro s; cases s <;> decide⟩
instance : AuditEnum Action := ⟨actions,by intro a; cases a <;> decide⟩
instance : AuditEnum Ambient := ⟨ambientStates,by
  intro s; cases s with
  | inK k => cases k <;> decide
  | p2w0 => decide
  | p5w1 => decide⟩
instance : AuditEnum Tag := ⟨tags,by intro t; cases t <;> decide⟩
instance : AuditEnum Clause := ⟨clauses,by intro c; cases c <;> decide⟩
instance : AuditEnum Cell := ⟨primitiveCells,primitive_cells_complete⟩
instance : AuditEnum RouteId := ⟨routeIds,by intro r; cases r <;> decide⟩
instance : AuditEnum HistoryId := ⟨historyIds,by intro h; cases h <;> decide⟩
instance : AuditEnum CurrentChannel := ⟨[.publicPosition,.deadlineAvailability,.canonicalM],by intro c; cases c <;> decide⟩
instance : AuditEnum AssemblageId := ⟨assemblageIds,by intro c; cases c <;> decide⟩
instance (n : Nat) : AuditEnum (Fin n) := ⟨List.finRange n,by simp⟩

instance (a : Assignment) (scope : List Cell) : Decidable (Complete scope a) := by
  unfold Complete; infer_instance
instance (d : ViabilityInputs) : Decidable (Ledger8 d) := by
  unfold Ledger8; infer_instance
instance (a : Assignment) (t : Tag) : Decidable (C1Gate a t) := by
  unfold C1Gate Ready Complete RowsValid T1Anchors TablesReconstructed
  infer_instance
instance (a : Assignment) (t : Tag) : Decidable (C1Accept a t) :=
  decidable_of_iff (C1Gate a t) (c1_accept_iff_gate a t).symm
instance (a : Assignment) (t : Tag) : Decidable (C2Accept a t) := by
  unfold C2Accept C2Gate Ready Complete RowsValid MLinked samePartition C2Rule; infer_instance
instance (a : Assignment) (t : Tag) : Decidable (C3Accept a t) := by
  unfold C3Accept C3Gate Ready Complete RowsValid MLinked C3Rule samePartition; infer_instance
instance (a : Assignment) (t : Tag) : Decidable (C4Accept a t) := by
  unfold C4Accept C4Gate Ready Complete RowsValid MLinked samePartition Collision4 Connector4 Exposed4
  infer_instance
instance (a : Assignment) (t : Tag) : Decidable (C5Accept a t) := by
  unfold C5Accept C5Gate Ready Complete RowsValid C5Rule Owner5 Anchors5; infer_instance
instance (a : Assignment) (t : Tag) : Decidable (C6Accept a t) := by
  unfold C6Accept C6Gate Ready Complete RowsValid Reference6 MLinked samePartition Trace6
    LedgerConservation6 UnitFunding6 FiniteBisim6 Coarser6
  infer_instance
instance (a : Assignment) (t : Tag) : Decidable (C7Accept a t) := by
  unfold C7Accept C7Gate Ready Complete RowsValid C7Rule Local7 Histories7 Strict7 Operational7
  infer_instance
instance (d : ViabilityInputs) : Decidable (PUnchanged8 d) := by
  unfold PUnchanged8; infer_instance
instance (a : Assignment) (t : Tag) : Decidable (C8Accept a t) := by
  unfold C8Accept C8Gate Ready Complete RowsValid Ledger8 PUnchanged8; infer_instance
instance (a : Assignment) (t : Tag) (c : Clause) : Decidable (clauseAccept a t c) := by
  cases c <;> unfold clauseAccept <;> infer_instance
instance (a : Assignment) (t : Tag) : Decidable (AssignedPackagePass a t) := by
  unfold AssignedPackagePass; infer_instance

def packageCheck (a : Assignment) (t : Tag) : Bool := decide (AssignedPackagePass a t)
theorem package_check_iff (a : Assignment) (t : Tag) :
    packageCheck a t = true ↔ AssignedPackagePass a t := by simp [packageCheck]
end CSTTT.TargetTheory.ComputedFIACH
