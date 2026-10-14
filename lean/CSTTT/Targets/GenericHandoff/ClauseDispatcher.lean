import CSTTT.Targets.GenericHandoff.ObjecthoodProtocol
import CSTTT.Targets.GenericHandoff.ExposureRules
import CSTTT.Targets.GenericHandoff.ProtocolCreditRules
import CSTTT.Targets.GenericHandoff.JointRules
import CSTTT.Targets.GenericHandoff.TemporalFactorCells
import CSTTT.Targets.GenericHandoff.OperationalCells

/-! Closed raw package dispatcher: no acceptance function is a raw field.
The eight constructors select fixed algorithms on typed primitive bindings.
C4–C7 retain their surrogate grades. Finite C6 audits and C3 completion must
be linked to actual runtime semantics before this dispatcher can be used for
TTH-06 promotion. Different clauses may use different finite interface types.
-/
namespace CSTTT.TargetTheory.GenericHandoff.ClauseDispatcher

inductive Kind where | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8
  deriving DecidableEq

def kinds : List Kind := [.c1,.c2,.c3,.c4,.c5,.c6,.c7,.c8]

/-- Decidable equality instances are presentation data, not property flags.
No type or cardinality of a carrier/action/owner is fixed by the dispatcher. -/
inductive Rule (Cell : Type) (Value : Cell → Type) : Kind → Type 1 where
  | c1 {S A O : Type} (eqS : DecidableEq S)
      (cfg : ProfileRules.Schema S A O) (ref : ObjecthoodProtocol.Reference S)
      (v : ObjecthoodCells.Bindings Cell Value S A O) : Rule Cell Value .c1
  | c2 {S A O : Type} (eqS : DecidableEq S) (eqO : DecidableEq O)
      (cfg : ProfileRules.ClauseSchema S A O) (v : ProfileRules.ClauseBindings Cell Value S A O) : Rule Cell Value .c2
  | c3 {S A O : Type} (eqS : DecidableEq S) (eqO : DecidableEq O)
      (cfg : ProfileRules.ClauseSchema S A O) (v : ProfileRules.ClauseBindings Cell Value S A O) : Rule Cell Value .c3
  | c4 {S A O H : Type} (eqS : DecidableEq S) (eqO : DecidableEq O)
      (cfg : ExposureRules.Schema S A O H) (v : ExposureRules.Bindings Cell Value S A O H) : Rule Cell Value .c4
  | c5 {S A O V Ch Id H Owner Edge : Type}
      (eqS : DecidableEq S) (eqO : DecidableEq O) (eqV : DecidableEq V) (eqCh : DecidableEq Ch)
      (cfg : ProtocolCreditRules.Schema S A O V Ch Id H Owner Edge)
      (v : ProtocolCreditRules.Bindings Cell Value S A O Id H Owner Edge) : Rule Cell Value .c5
  | c6 {S A O H RouteId Stage Id Owner : Type}
      (eqS : DecidableEq S) (eqO : DecidableEq O) (eqR : DecidableEq RouteId)
      (eqStage : DecidableEq Stage) (eqId : DecidableEq Id)
      (cfg : TemporalFactorRules.Schema S A O H RouteId Stage Id Owner)
      (v : TemporalFactorCells.Bindings Cell Value S A O H RouteId Stage Id Owner) : Rule Cell Value .c6
  | c7 {S A O D H L R Assembly Observable Stage Id : Type}
      (eqS : DecidableEq S) (eqO : DecidableEq O) (eqObs : DecidableEq Observable)
      (eqStage : DecidableEq Stage) (eqId : DecidableEq Id)
      (cfg : JointRules.Schema S A O D H L R Assembly Observable Stage Id)
      (v : JointRules.Bindings Cell Value S A O D H L R Assembly Observable Stage Id) : Rule Cell Value .c7
  | c8 {S A O Owner : Type} (eqS : DecidableEq S) (eqO : DecidableEq O) (eqOwner : DecidableEq Owner)
      (cfg : OperationalViability.Schema S A O Owner) (outcomes : List O)
      (v : OperationalViability.Bindings Cell Value S A O Owner) : Rule Cell Value .c8

variable {Cell : Type} {Value : Cell → Type} {k : Kind}

def Rule.scope : Rule Cell Value k → List Cell
  | .c1 _ _ _ v => v.scope
  | .c2 _ _ _ v | .c3 _ _ _ v => v.scope
  | .c4 _ _ _ v => v.scope
  | .c5 _ _ _ _ _ v => v.scope
  | .c6 _ _ _ _ _ _ v => v.scope
  | .c7 _ _ _ _ _ _ v => v.scope
  | .c8 _ _ _ _ _ v => v.scope

/-- C3 includes a genuine fixed-point/block-coverage check, not only adjacent
partition agreement. This is an explicit enclosing completion gate. -/
def Rule.accept (r : Rule Cell Value k) (a : Assignment Cell Value) : Prop := match r with
  | .c1 eqS cfg ref v => letI := eqS; ObjecthoodProtocol.Accept cfg ref v a
  | .c2 eqS eqO cfg v => letI := eqS; letI := eqO; ProfileRules.C2Accept cfg v a
  | .c3 eqS eqO cfg v => letI := eqS; letI := eqO;
      ProfileRules.C3Accept cfg v a ∧ ∃ d labels,
        ProfileRules.decodedClause cfg v a = some (d,labels) ∧ ProfileRules.StableProfile d
  | .c4 eqS eqO cfg v => letI := eqS; letI := eqO; ExposureRules.AssignedAccept cfg v a
  | .c5 eqS eqO eqV eqCh cfg v => letI := eqS; letI := eqO; letI := eqV; letI := eqCh;
      ProtocolCreditRules.AssignedAccept cfg v a
  | .c6 eqS eqO eqR eqStage eqId cfg v => letI := eqS; letI := eqO; letI := eqR;
      letI := eqStage; letI := eqId; TemporalFactorCells.Accept cfg v a
  | .c7 eqS eqO eqObs eqStage eqId cfg v => letI := eqS; letI := eqO; letI := eqObs;
      letI := eqStage; letI := eqId; JointRules.AssignedAccept cfg v a
  | .c8 eqS eqO eqOwner cfg outcomes v => letI := eqS; letI := eqO; letI := eqOwner; OperationalCells.Accept cfg outcomes v a

theorem Rule.locality (r : Rule Cell Value k) {a b : Assignment Cell Value}
    (h : Agrees r.scope a b) : r.accept a ↔ r.accept b := by
  cases r with
  | c1 eqS cfg ref v =>
    letI := eqS
    exact ObjecthoodProtocol.acceptance_locality cfg ref v h
  | c2 eqS eqO cfg v =>
    letI := eqS
    letI := eqO
    exact ProfileRules.c2_locality cfg v h
  | c3 eqS eqO cfg v =>
    letI := eqS
    letI := eqO
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [ProfileRules.c3_locality cfg v h,ProfileRules.clause_decoder_locality cfg v h]
  | c4 eqS eqO cfg v =>
    letI := eqS
    letI := eqO
    exact ExposureRules.acceptance_locality cfg v h
  | c5 eqS eqO eqV eqCh cfg v =>
    letI := eqS
    letI := eqO
    letI := eqV
    letI := eqCh
    exact ProtocolCreditRules.acceptance_locality cfg v h
  | c6 eqS eqO eqR eqStage eqId cfg v =>
    letI := eqS
    letI := eqO
    letI := eqR
    letI := eqStage
    letI := eqId
    exact TemporalFactorCells.acceptance_locality cfg v h
  | c7 eqS eqO eqObs eqStage eqId cfg v =>
    letI := eqS
    letI := eqO
    letI := eqObs
    letI := eqStage
    letI := eqId
    exact JointRules.acceptance_locality cfg v h
  | c8 eqS eqO eqOwner cfg outcomes v =>
    letI := eqS
    letI := eqO
    letI := eqOwner
    exact OperationalCells.locality cfg outcomes v h

theorem Rule.missing_rejected (r : Rule Cell Value k) (a : Assignment Cell Value)
    (cell : Cell) (hk : cell ∈ r.scope) (hm : a cell = none) : ¬ r.accept a := by
  cases r with
  | c1 eqS cfg ref v =>
    letI := eqS
    exact ObjecthoodProtocol.missing_rejected cfg ref v a cell hk hm
  | c2 eqS eqO cfg v =>
    letI := eqS
    letI := eqO
    exact (ProfileRules.missing_cell_rejected cfg v a cell hk hm).2.1
  | c3 eqS eqO cfg v =>
    letI := eqS
    letI := eqO
    exact fun h => (ProfileRules.missing_cell_rejected cfg v a cell hk hm).2.2 h.1
  | c4 eqS eqO cfg v =>
    letI := eqS
    letI := eqO
    exact (ExposureRules.missing_rejected cfg v a cell hk hm).2
  | c5 eqS eqO eqV eqCh cfg v =>
    letI := eqS
    letI := eqO
    letI := eqV
    letI := eqCh
    exact (ProtocolCreditRules.missing_rejected cfg v a cell hk hm).2
  | c6 eqS eqO eqR eqStage eqId cfg v =>
    letI := eqS
    letI := eqO
    letI := eqR
    letI := eqStage
    letI := eqId
    exact TemporalFactorCells.missing_rejected cfg v a cell hk hm
  | c7 eqS eqO eqObs eqStage eqId cfg v =>
    letI := eqS
    letI := eqO
    letI := eqObs
    letI := eqStage
    letI := eqId
    exact (JointRules.missing_rejected cfg v a cell hk hm).2
  | c8 eqS eqO eqOwner cfg outcomes v =>
    letI := eqS
    letI := eqO
    letI := eqOwner
    exact OperationalCells.missing_rejected cfg outcomes v a cell hk hm

structure Package (Cell : Type) (Value : Cell → Type) where
  rule : (k : Kind) → Rule Cell Value k

def Package.accept (p : Package Cell Value) (a : Assignment Cell Value) : Prop := ∀ k, (p.rule k).accept a

theorem Package.locality (p : Package Cell Value) {a b : Assignment Cell Value}
    (h : ∀ k, Agrees (p.rule k).scope a b) : p.accept a ↔ p.accept b := by
  constructor <;> intro hp k
  · exact ((p.rule k).locality (h k)).mp (hp k)
  · exact ((p.rule k).locality (h k)).mpr (hp k)

theorem Package.missing_rejected (p : Package Cell Value) (a : Assignment Cell Value)
    (k : Kind) (cell : Cell) (hk : cell ∈ (p.rule k).scope) (hm : a cell = none) : ¬ p.accept a :=
  fun h => (p.rule k).missing_rejected a cell hk hm (h k)

end CSTTT.TargetTheory.GenericHandoff.ClauseDispatcher

