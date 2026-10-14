import CSTTT.FullNative02.Ancestry

namespace CSTTT.FullNative02
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem fusion_birth_from_execution (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (pair : Pair) (probability : Rat) :
    (settle supply w q p pair probability).kind=.created (.birth (w.events.length+2)) := by
  simp [settle,paidParents,advance]

theorem fusion_preserves_old_ancestry (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (pair : Pair) (probability : Rat) (x y : Node) (h : ancestry w x y) :
    ancestry (settle supply w q p pair probability).world x y := by
  apply path_mono (es := ledgerEdges w) (x := x) (y := y) ?_ h
  intro e he
  simp only [ledgerEdges,settle,paidParents,advance,List.length_append,List.length_singleton,
    List.append_assoc,ledger_append,Nat.zero_add]
  exact List.mem_append_left _ he

theorem both_actual_parent_paths (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (pair : Pair) (probability : Rat) :
    ancestry (settle supply w q p pair probability).world p.left.version (.birth (w.events.length+2)) ∧
    ancestry (settle supply w q p pair probability).world p.right.version (.birth (w.events.length+2)) := by
  let next := (settle supply w q p pair probability).world
  have left : (p.left.version,.event w.events.length)∈ledgerEdges next := by
    simp [next,ledgerEdges,settle,paidParents,advance,ledger_append,ledgerEdgesFrom,eventEdges]
  have leftAfter : (.event w.events.length,.version w.events.length)∈ledgerEdges next := by
    simp [next,ledgerEdges,settle,paidParents,advance,ledger_append,ledgerEdgesFrom,eventEdges]
  have right : (p.right.version,.event (w.events.length+1))∈ledgerEdges next := by
    simp [next,ledgerEdges,settle,paidParents,advance,ledger_append,ledgerEdgesFrom,eventEdges]
  have rightAfter : (.event (w.events.length+1),.version (w.events.length+1))∈ledgerEdges next := by
    simp [next,ledgerEdges,settle,paidParents,advance,ledger_append,ledgerEdgesFrom,eventEdges]
  have leftFuse : (.version w.events.length,.event (w.events.length+2))∈ledgerEdges next := by
    simp [next,ledgerEdges,settle,paidParents,advance,ledger_append,ledgerEdgesFrom,eventEdges,Nat.add_assoc]
  have rightFuse : (.version (w.events.length+1),.event (w.events.length+2))∈ledgerEdges next := by
    simp [next,ledgerEdges,settle,paidParents,advance,ledger_append,ledgerEdgesFrom,eventEdges,Nat.add_assoc]
  have born : (.event (w.events.length+2),.birth (w.events.length+2))∈ledgerEdges next := by
    simp [next,ledgerEdges,settle,paidParents,advance,ledger_append,ledgerEdgesFrom,eventEdges,Nat.add_assoc]
  exact ⟨.extend (.extend (.extend (.one left) leftAfter) leftFuse) born,
    .extend (.extend (.extend (.one right) rightAfter) rightFuse) born⟩

/-- Original relation-valued schema, using the ACTUAL parent versions in the
same least relation. No historical-source role is assigned to a live target. -/
theorem original_positive_fusion (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (pair : Pair) (probability : Rat) (source : Node)
    (left : ancestry w source p.left.version) (right : ancestry w source p.right.version) :
    Prospects.FallbackFissionFusionEmpty Node
      (ancestry (settle supply w q p pair probability).world) source
      p.left.version p.right.version (.birth (w.events.length+2))
      (EmptyTarget supply w q) := by
  exact ⟨fusion_preserves_old_ancestry supply w q p pair probability _ _ left,
    fusion_preserves_old_ancestry supply w q p pair probability _ _ right,
    .inl (both_actual_parent_paths supply w q p pair probability)⟩

theorem original_empty_fusion (supply : Supply) (w : World) (q : FusionRequest) (p : Parents)
    (view : parentView w q=some p)
    (zero : meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction=0)
    (source : Node) (left : ancestry w source p.left.version) (right : ancestry w source p.right.version) :
    Prospects.FallbackFissionFusionEmpty Node (ancestry w) source
      p.left.version p.right.version (prospective q) (EmptyTarget supply w q) := by
  exact ⟨left,right,.inr ⟨p,view,zero,rfl,empty_same_world supply w q p view zero⟩⟩

end CSTTT.FullNative02
