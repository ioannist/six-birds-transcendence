import CSTTT.Targets.GenericHandoff.NativeComposition.ModeExecution

/-! Reception changes the actual retained tuple by an injective raw operation.
It need not satisfy the old endpoint's literal tuple-identity requirement. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ReceptionMemory
open RegisterInterpreter ModeExecution

def encode (past : Frame.Residue) : Frame.Residue := (past.1++past.1,past.2)
def decode (past : Frame.Residue) : Frame.Residue :=
  (past.1.take (past.1.length/2),past.2)

theorem decode_encode (past : Frame.Residue) : decode (encode past)=past := by
  rcases past with ⟨hist,ids⟩
  simp only [encode,decode,half_double]

theorem injective : Function.Injective encode := by
  intro x y h
  have he := congrArg decode h
  simpa only [decode_encode] using he

theorem actual_reception (cell sourceOwner : Owner) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell=some p) (x : ModeExecution.Registers) (h : History) (r : Route) :
    ((receiveExpr cell sourceOwner).eval a x (h,r)).map (fun y => y.1.residue)=
      some (encode (x ()).1.residue) := by
  rw [actual_receive cell sourceOwner a p hp x h r]
  rfl

theorem actual_recovery (cell sourceOwner : Owner) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell=some p) (x : ModeExecution.Registers) (h : History) (r : Route) :
    ((receiveExpr cell sourceOwner).eval a x (h,r)).map (fun y => decode y.1.residue)=
      some (x ()).1.residue := by
  have he := congrArg (Option.map decode) (actual_reception cell sourceOwner a p hp x h r)
  simpa only [Option.map_map,Function.comp_def,Option.map_some,decode_encode] using he

theorem publication_tuple (i : Input) (h : History) (ids : List Bool) :
    ((publish i).temporal.histories h,ids)=encode (i.temporal.histories h,ids) := rfl

theorem missing_reception (cell sourceOwner : Owner) (a : Assignment Owner MemoryValue)
    (hm : a cell=none) (x : ModeExecution.Registers) (h : History) (r : Route) :
    (receiveExpr cell sourceOwner).eval a x (h,r)=none := by
  simp [receiveExpr,targetData,Expr.eval,Expr.reenv_eval,hm]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ReceptionMemory
