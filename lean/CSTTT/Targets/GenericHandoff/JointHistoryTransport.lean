import CSTTT.Targets.GenericHandoff.JointRules

/-! Stronger raw joint transport permits an explicit history encoding, while
retaining complete branch records, primitive coupling and exact distributions.
The older pointwise-state transport embeds without changing its statement. -/
namespace CSTTT.TargetTheory.GenericHandoff.JointHistoryTransport

def Transport {S T AS AT OS OT D H L R Assembly Observable Stage Id : Type}
    [DecidableEq S] [DecidableEq T]
    (sc : JointRules.Schema S AS OS D H L R Assembly Observable Stage Id)
    (tc : JointRules.Schema T AT OT D H L R Assembly Observable Stage Id)
    (s : JointRules.Raw S AS OS D H L R Assembly Observable Stage Id)
    (t : JointRules.Raw T AT OT D H L R Assembly Observable Stage Id) (historyMap : List S → List T) : Prop :=
  s.joint.observables=t.joint.observables ∧
  ∀ id ∈ sc.assemblages,
    ((JointRules.branchwise sc s id).1.map historyMap,(JointRules.branchwise sc s id).2.map historyMap)=
      JointRules.branchwise tc t id ∧
    s.joint.coupling id=t.joint.coupling id ∧ JointRules.distribution sc s id=JointRules.distribution tc t id

theorem of_state_transport {S T AS AT OS OT D H L R Assembly Observable Stage Id : Type}
    [DecidableEq S] [DecidableEq T]
    (sc : JointRules.Schema S AS OS D H L R Assembly Observable Stage Id)
    (tc : JointRules.Schema T AT OT D H L R Assembly Observable Stage Id)
    (s : JointRules.Raw S AS OS D H L R Assembly Observable Stage Id)
    (t : JointRules.Raw T AT OT D H L R Assembly Observable Stage Id) (stateMap : S → T)
    (h : JointRules.Transport sc tc s t stateMap) : Transport sc tc s t (List.map stateMap) := h

end CSTTT.TargetTheory.GenericHandoff.JointHistoryTransport
