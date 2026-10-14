import CSTTT.Targets.GenericHandoff.NativeComposition.OperationalCells

/-! Shared native and supplementary primitive cells for a full dispatcher
construction. Credit, quotient, distribution, viability and acceptance are
computed from these fields; none is stored here. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackagePrimitives
open RegisterInterpreter

abbrev Vertex := Fin 3
inductive Protocol where | selfCycle | externalCycle | null deriving DecidableEq, Repr
inductive Provenance where | local | external deriving DecidableEq, Repr
abbrev CreditOwner := Sum Owner Unit
abbrev Edge := Vertex × Vertex × Bool
structure CreditPrimitives where
  edges : Protocol → List Edge
  owner : Protocol → Provenance
  housing : Protocol → Provenance
structure Supplement where
  objecthood : NativeObjecthoodCells.Supplement
  credit : CreditPrimitives
  joint : JointRules.Tables Bool Factor Bool Bool Bool Unit

abbrev Cell := Sum Owner Owner
def Value : Cell → Type
  | .inl o => MemoryValue o
  | .inr _ => Supplement × Supplement
def selectSupplement (copy : Bool) (p : Supplement × Supplement) := if copy then p.2 else p.1
def nativeInputs (a : Assignment Cell Value) : Assignment Owner MemoryValue := fun o => a (.inl o)
def objecthoodInputs (a : Assignment Cell Value) : Assignment NativeObjecthoodCells.Cell NativeObjecthoodCells.Value
  | .inl o => a (.inl o)
  | .inr o => (a (.inr o)).map (fun p => (p.1.objecthood,p.2.objecthood))

def cycle (channel : Bool) : List Edge := [(0,1,channel),(1,2,channel),(2,0,channel)]
def creditPrimitives : CreditPrimitives :=
  ⟨(fun id => match id with | .selfCycle => cycle false | .externalCycle => cycle true | .null => []),
    (fun id => match id with | .selfCycle => .local | _ => .external),
    (fun id => match id with | .selfCycle => .local | _ => .external)⟩
def hiddenHistory (b : Bool) : Factor := (false,false,b)
def coupling (b : Bool) : List (Bool × Bool) :=
  if b then [(false,true),(true,false)] else [(false,false),(true,true)]
def jointPrimitives : JointRules.Tables Bool Factor Bool Bool Bool Unit :=
  ⟨(fun _ => hiddenHistory),(fun _ => hiddenHistory),coupling,id,[()]⟩
def supplement : Supplement := ⟨NativeObjecthoodCells.supplement,creditPrimitives,jointPrimitives⟩
def initial : Assignment Cell Value
  | .inl o => some (AvailabilityFactor.input o,AvailabilityFactor.input o)
  | .inr _ => some (supplement,supplement)

def image (a : Assignment Cell Value) : Assignment Cell Value
  | .inl o => memoryImage (nativeInputs a) o
  | .inr o => (a (.inr (swapOwner o))).map (fun p => (p.1,p.1))
def cellOwner : Cell → Owner | .inl o | .inr o => o
def staged (a : Assignment Cell Value) : Assignment Cell Value :=
  fun c => if cellOwner c then image a c else image (image a) c
def canonical := staged initial

theorem objecthood_image (a : Assignment Cell Value) :
    objecthoodInputs (image a)=NativeObjecthoodCells.image (objecthoodInputs a) := by
  funext c
  cases c with
  | inl o => rfl
  | inr o => simp [objecthoodInputs,image,NativeObjecthoodCells.image,Option.map_map,Function.comp_def]
theorem objecthood_staged (a : Assignment Cell Value) :
    objecthoodInputs (staged a)=NativeObjecthoodCells.staged (objecthoodInputs a) := by
  funext c
  cases c with
  | inl o => cases o <;> rfl
  | inr o =>
    cases o <;> simp [staged,cellOwner,objecthoodInputs,image,NativeObjecthoodCells.staged,
      NativeObjecthoodCells.cellOwner,NativeObjecthoodCells.image,swapOwner,Option.map_map,Function.comp_def]
theorem objecthood_initial : objecthoodInputs initial=AvailabilityPublication.initial := by
  funext c; cases c <;> rfl
theorem objecthood_canonical : objecthoodInputs canonical=AvailabilityPublication.stages := by
  rw [canonical,objecthood_staged,objecthood_initial]
  rfl
theorem native_canonical : nativeInputs canonical=AvailabilityPublication.native := by
  exact congrArg NativeObjecthoodCells.nativeInputs objecthood_canonical
theorem copied_native_source (a : Assignment Cell Value) (o : Owner) :
    sourceInputs (nativeInputs (image a)) (swapOwner o)=currentInputs (nativeInputs a) o :=
  published_source (nativeInputs a) o
theorem copied_supplement_source (a : Assignment Cell Value) (o : Owner) :
    (image a (.inr (swapOwner o))).map (selectSupplement true)=
      (a (.inr o)).map (selectSupplement false) := by
  cases o <;> simp [image,selectSupplement,swapOwner,Option.map_map,Function.comp_def] <;> rfl
theorem canonical_supplement (o : Owner) : canonical (.inr o)=some (supplement,supplement) := by
  cases o <;> rfl

def interpretOwner (i : Input) : Provenance → CreditOwner
  | .local => .inl i.temporal.resource.owner
  | .external => .inr ()
def creditTables (i : Input) (s : Supplement) : ProtocolCreditRules.Tables Protocol Edge CreditOwner :=
  ⟨s.credit.edges,(fun id => interpretOwner i (s.credit.owner id)),
    (fun id => interpretOwner i (s.credit.housing id))⟩
def translateOwner : CreditOwner → CreditOwner
  | .inl o => .inl (swapOwner o)
  | .inr _ => .inr ()
theorem interpret_published_owner (i : Input) (p : Provenance) :
    interpretOwner (publish i) p=translateOwner (interpretOwner i p) := by cases p <;> rfl
theorem credit_raw_transport (i : Input) (s : Supplement) :
    ProtocolCreditRules.Transport (creditTables i s) (creditTables (publish i) s)
      [.selfCycle,.externalCycle,.null] id id translateOwner := by
  intro p hp
  exact ⟨List.map_id _,(interpret_published_owner i (s.credit.owner p)).symm,
    (interpret_published_owner i (s.credit.housing p)).symm⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackagePrimitives
