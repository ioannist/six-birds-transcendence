import CSTTT.Targets.GenericHandoff.NativeComposition.FissionRelation

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
open RegisterInterpreter PublicationReplay CSTTT.TransportTheory
open CSTTT.CorridorTheory.AtomicChain

def swapPlaced (p : PlacedBundle) : PlacedBundle := {p with names := swapOwner ∘ p.names}
theorem canonical_target_package_swap (branch : Bool) :
    targetPackage (!branch) (assignment canonicalRaw (!branch))=
      (targetPackage branch (assignment canonicalRaw branch)).map swapPlaced := by
  rw [canonical_assignment,canonical_assignment]
  have hn : branchNames (!branch)=swapOwner ∘ branchNames branch := funext (swapped_names branch)
  simp only [targetPackage,Option.map_map,swapPlaced,Function.comp_def]
  rw [hn]
  rfl
theorem canonical_source_package_swap :
    (sourcePackage (assignment canonicalRaw false)).map swapPlaced=sourcePackage (assignment canonicalRaw false) := by
  have hn : (fun o => swapOwner (names true o))=names true := by
    funext o; cases o <;> rfl
  simp only [sourcePackage,Option.map_map,swapPlaced,Function.comp_def,hn]

def swapLeg (l : FiniteAtomicLeg) : FiniteAtomicLeg :=
  {l with
    source := transpose 201 202 l.source
    target := transpose 201 202 l.target
    stages := l.stages.map (fun s => {s with support := s.support.map (transpose 201 202), frontier := {s.frontier with owner := transpose 201 202 s.frontier.owner}})
    events := l.events.map (fun e => {e with owner := transpose 201 202 e.owner})
    updates := l.updates.map (fun u => {u with nextOwner := transpose 201 202 u.nextOwner})}
theorem canonical_whole_leg_swap (branch : Bool) (h : Factor) :
    renameLeg (!branch) (PublicationCorridor.left h)=swapLeg (renameLeg branch (PublicationCorridor.left h)) := by
  cases branch
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> decide +kernel

theorem canonical_future_code_swap (branch : Bool) (x : Frame.Registers) :
    (targetFuture (!branch) NativePackageBundle.canonical PublicationComposition.canonical_ready).code x=
      OwnerRelabel.codeImage swapOwner ((targetFuture branch NativePackageBundle.canonical PublicationComposition.canonical_ready).code x) := by
  change bridgeCodeOfObservation ((targetFuture (!branch) NativePackageBundle.canonical PublicationComposition.canonical_ready).observe x)=_
  rw [canonical_swap_observation]
  rfl

theorem canonical_named_credit_owner_swap (branch : Bool) (b : NativePackageBundle.Bundle)
    (p : NativePackagePrimitives.Protocol) :
    (namedCreditTables (branchNames (!branch)) b).owner p=
      (match (namedCreditTables (branchNames branch) b).owner p with
        | .inl c => .inl (swapOwner c)
        | .inr u => .inr u) := by
  change namedCreditOwner (branchNames (!branch)) ((NativeCreditCells.data b).tables.owner p)=_
  cases ho : (NativeCreditCells.data b).tables.owner p with
  | inl o => simp only [namedCreditTables,namedCreditOwner,ho,swapped_names]
  | inr u => simp only [namedCreditTables,namedCreditOwner,ho]
theorem canonical_named_credit_housing_swap (branch : Bool) (b : NativePackageBundle.Bundle)
    (p : NativePackagePrimitives.Protocol) :
    (namedCreditTables (branchNames (!branch)) b).housing p=
      (match (namedCreditTables (branchNames branch) b).housing p with
        | .inl c => .inl (swapOwner c)
        | .inr u => .inr u) := by
  change namedCreditOwner (branchNames (!branch)) ((NativeCreditCells.data b).tables.housing p)=_
  cases ho : (NativeCreditCells.data b).tables.housing p with
  | inl o => simp only [namedCreditTables,namedCreditOwner,ho,swapped_names]
  | inr u => simp only [namedCreditTables,namedCreditOwner,ho]

theorem named_accounts_swap (branch : Bool) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers) :
    (namedRuntime (!branch)).accounts.eval a x ()=
      ((namedRuntime branch).accounts.eval a x ()).map
        (fun accounts res => {accounts res with owner := (accounts res).owner.map swapOwner}) := by
  cases hc : (ModeExecution.context true false).eval a x () with
  | none => simp [namedRuntime,ModeExecution.resources,Expr.eval,hc]
  | some p =>
    simp only [namedRuntime,ModeExecution.resources,Expr.eval,hc,Option.map_some]
    congr 1
    funext res
    cases res
    · rfl
    · simp only [ite_true,swapped_names,Option.map_some]
theorem named_charge_swap (branch : Bool) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers)
    (d : Unit) (act : Bool) :
    (namedRuntime (!branch)).charge.eval a x (d,act)=
      ((namedRuntime branch).charge.eval a x (d,act)).map (fun charge => {charge with owner := swapOwner charge.owner}) := by
  cases hc : (ModeExecution.context true false).eval a x () with
  | none => simp [namedRuntime,ModeExecution.resources,Expr.eval,Expr.reenv_eval,hc]
  | some p => simp only [namedRuntime,ModeExecution.resources,Expr.eval,Expr.reenv_eval,hc,Option.map_some,swapped_names]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
