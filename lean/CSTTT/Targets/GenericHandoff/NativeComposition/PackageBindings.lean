import CSTTT.Targets.GenericHandoff.NativeComposition.CreditCells
import CSTTT.Targets.GenericHandoff.NativeComposition.JointCells

/-! Exact clause bindings in one shared primitive bundle namespace.
All decoder and acceptance equivalences quantify over every partial assignment;
native/supplementary projections are actual raw views, with no default data. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackageBindings
open RegisterInterpreter NativePackageBundle

def nativeValue (_ : Owner) (p : Bundle × Bundle) : Input × Input := (p.1.native,p.2.native)
def nativeView {X : Type} (v : CellView Owner MemoryValue X) : CellView Owner NativePackageBundle.Value X :=
  CellReindex.cellView id nativeValue v
def objecthoodValue : (k : NativeObjecthoodCells.Cell) → NativePackageBundle.Value (NativeObjecthoodCells.cellOwner k) → NativeObjecthoodCells.Value k
  | .inl _,p => (p.1.native,p.2.native)
  | .inr _,p => (p.1.supplement.objecthood,p.2.supplement.objecthood)
def objecthoodView {X : Type} (v : CellView NativeObjecthoodCells.Cell NativeObjecthoodCells.Value X) :
    CellView Owner NativePackageBundle.Value X :=
  CellReindex.cellView NativeObjecthoodCells.cellOwner objecthoodValue v

theorem native_view_read {X : Type} (v : CellView Owner MemoryValue X) (a : Assignment Owner NativePackageBundle.Value) :
    (nativeView v).read a=v.read (NativePackageBundle.nativeInputs a) := by
  simp [nativeView,CellReindex.cellView,CellView.read,NativePackageBundle.nativeInputs,nativeValue,
    Option.map_map,Function.comp_def]
theorem objecthood_pullback (a : Assignment Owner NativePackageBundle.Value) :
    CellReindex.pullback NativeObjecthoodCells.cellOwner objecthoodValue a=NativePackageBundle.objecthoodInputs a := by
  funext k; cases k <;> rfl
theorem objecthood_view_read {X : Type} (v : CellView NativeObjecthoodCells.Cell NativeObjecthoodCells.Value X)
    (a : Assignment Owner NativePackageBundle.Value) :
    (objecthoodView v).read a=v.read (NativePackageBundle.objecthoodInputs a) := by
  rw [objecthoodView,CellReindex.cell_view_equation,objecthood_pullback]

def c1 (cell : Owner) (copy : Bool) : ObjecthoodCells.Bindings Owner NativePackageBundle.Value Factor Bool Factor :=
  let v := NativeObjecthoodCells.bindings cell copy
  ⟨objecthoodView v.rows,objecthoodView v.positions,objecthoodView v.hazards,objecthoodView v.policy,objecthoodView v.prototypes,objecthoodView v.parameters,objecthoodView v.publishedP,objecthoodView v.publishedC,objecthoodView v.publishedU⟩
def profile (cell : Owner) (copy : Bool) : ProfileRules.ClauseBindings Owner NativePackageBundle.Value Factor Bool Factor :=
  let v := ProfileCells.bindings cell copy
  ⟨⟨nativeView v.primitives.rows,nativeView v.primitives.positions,nativeView v.primitives.hazards,nativeView v.primitives.reveal⟩,nativeView v.classes⟩
def exposure (cell : Owner) (copy : Bool) : ExposureRules.Bindings Owner NativePackageBundle.Value Factor Bool Factor Unit :=
  let v := ExposureRepair.bindings cell copy
  ⟨nativeView v.rows,nativeView v.positions,nativeView v.hazards,nativeView v.channels,nativeView v.policy,nativeView v.histories,nativeView v.classes⟩
def factor (cell : Owner) (copy : Bool) :
    TemporalFactorCells.Bindings Owner NativePackageBundle.Value Factor Bool Factor History Route Stage Bool Owner :=
  let v := MemoryFrames.bindings cell copy
  ⟨nativeView v.rows,nativeView v.positions,nativeView v.hazards,nativeView v.policy,nativeView v.classes,nativeView v.publishedP,nativeView v.ticks,nativeView v.resource,nativeView v.ledger,nativeView v.interface,nativeView v.histories,nativeView v.events,nativeView v.realized,nativeView v.receiverFunded,nativeView v.routes,nativeView v.writers⟩
def operational (cell : Owner) (copy : Bool) : OperationalViability.Bindings Owner NativePackageBundle.Value Factor Bool Factor Owner :=
  let v := NativeOperationalCells.bindings cell copy
  ⟨nativeView v.rows,nativeView v.policy,nativeView v.resource,nativeView v.ledger⟩

theorem c1_decoded (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    ObjecthoodCells.decoded clauseSchema.toSchema (c1 cell copy) a=
      ObjecthoodCells.decoded clauseSchema.toSchema (NativeObjecthoodCells.bindings cell copy) (NativePackageBundle.objecthoodInputs a) := by
  simp only [ObjecthoodCells.decoded,c1,objecthood_view_read]
theorem profile_decoded (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    ProfileRules.decodedClause clauseSchema (profile cell copy) a=
      ProfileRules.decodedClause clauseSchema (ProfileCells.bindings cell copy) (NativePackageBundle.nativeInputs a) := by
  simp only [ProfileRules.decodedClause,ProfileRules.decoded,profile,native_view_read]
theorem exposure_decoded (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    ExposureRules.decoded (exposure cell copy) a=
      ExposureRules.decoded (ExposureRepair.bindings cell copy) (NativePackageBundle.nativeInputs a) := by
  simp only [ExposureRules.decoded,exposure,native_view_read]
theorem factor_decoded (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    TemporalFactorCells.decoded (factor cell copy) a=
      TemporalFactorCells.decoded (MemoryFrames.bindings cell copy) (NativePackageBundle.nativeInputs a) := by
  simp only [TemporalFactorCells.decoded,factor,native_view_read]
theorem operational_decoded (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    OperationalViability.decoded (operational cell copy) a=
      OperationalViability.decoded (NativeOperationalCells.bindings cell copy) (NativePackageBundle.nativeInputs a) := by
  simp only [OperationalViability.decoded,operational,native_view_read]

theorem c1_accept_iff (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    ObjecthoodProtocol.Accept clauseSchema.toSchema NativeObjecthoodCells.reference (c1 cell copy) a ↔
      ObjecthoodProtocol.Accept clauseSchema.toSchema NativeObjecthoodCells.reference (NativeObjecthoodCells.bindings cell copy) (NativePackageBundle.objecthoodInputs a) := by
  simp only [ObjecthoodProtocol.Accept,c1_decoded]
theorem c2_accept_iff (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    ProfileRules.C2Accept clauseSchema (profile cell copy) a ↔
      ProfileRules.C2Accept clauseSchema (ProfileCells.bindings cell copy) (NativePackageBundle.nativeInputs a) := by
  simp only [ProfileRules.C2Accept,profile_decoded]
theorem c3_accept_iff (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    (ClauseDispatcher.Rule.c3 inferInstance inferInstance clauseSchema (profile cell copy)).accept a ↔
      (ClauseDispatcher.Rule.c3 inferInstance inferInstance clauseSchema (ProfileCells.bindings cell copy)).accept (NativePackageBundle.nativeInputs a) := by
  simp only [ClauseDispatcher.Rule.accept,ProfileRules.C3Accept,profile_decoded]
theorem c4_accept_iff (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    ExposureRules.AssignedAccept ExposureRepair.schema (exposure cell copy) a ↔
      ExposureRules.AssignedAccept ExposureRepair.schema (ExposureRepair.bindings cell copy) (NativePackageBundle.nativeInputs a) := by
  simp only [ExposureRules.AssignedAccept,exposure_decoded]
theorem c6_accept_iff (owner cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    TemporalFactorCells.Accept (factorSchema owner) (factor cell copy) a ↔
      TemporalFactorCells.Accept (factorSchema owner) (MemoryFrames.bindings cell copy) (NativePackageBundle.nativeInputs a) := by
  simp only [TemporalFactorCells.Accept,factor_decoded]
theorem c8_accept_iff (owner cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    OperationalCells.Accept (NativeOperationalCells.schema owner) factors (operational cell copy) a ↔
      OperationalCells.Accept (NativeOperationalCells.schema owner) factors (NativeOperationalCells.bindings cell copy) (NativePackageBundle.nativeInputs a) := by
  simp only [OperationalCells.Accept,operational_decoded]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePackageBindings

