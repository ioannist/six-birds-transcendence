import CSTTT.FullNative02.Fusion
import CSTTT.Prospects.Statements

namespace CSTTT.FullNative02
set_option autoImplicit false

/-- Interpreter event kinds determine their edges. No raw adjacency list,
relation, ancestry boolean or supplied lineage constructor is accepted. -/
def eventEdges (ordinal : Nat) : Event → List (Node × Node)
  | .boot address _ _ _ => [(.hardware address,.birth ordinal)]
  | .native before _ _ => [(before,.event ordinal),(.event ordinal,.version ordinal)]
  | .snapshot source _ _ _ _ => [(source,.event ordinal)]
  | .activation snapshot _ _ _ _ _ => [(snapshot,.birth ordinal)]
  | .partition parent _ _ _ _ => [(parent,.birth ordinal)]
  | .fusion left right _ _ _ _ _ _ _ =>
      [(left,.event ordinal),(right,.event ordinal),(.event ordinal,.birth ordinal)]

def ledgerEdgesFrom : Nat → List Event → List (Node × Node)
  | _,[] => []
  | n,e::rest => eventEdges n e ++ ledgerEdgesFrom (n+1) rest
def ledgerEdges (w : World) : List (Node × Node) := ledgerEdgesFrom 0 w.events

inductive Path (edges : List (Node × Node)) : Node → Node → Prop where
  | one {x y} : (x,y)∈edges → Path edges x y
  | extend {x y z} : Path edges x y → (y,z)∈edges → Path edges x z

def ancestry (w : World) : Node → Node → Prop := Path (ledgerEdges w)

theorem path_trans {es : List (Node × Node)} {x y z : Node}
    (first : Path es x y) (second : Path es y z) : Path es x z := by
  induction second with
  | one h => exact .extend first h
  | extend _ h ih => exact .extend ih h

theorem ancestry_least (w : World) (r : Node → Node → Prop)
    (contains : ∀ x y, (x,y)∈ledgerEdges w → r x y)
    (transitive : ∀ x y z, r x y → r y z → r x z)
    (x y : Node) (h : ancestry w x y) : r x y := by
  induction h with
  | one edge => exact contains _ _ edge
  | extend _ edge ih => exact transitive _ _ _ ih (contains _ _ edge)

theorem no_ex_nihilo (w : World) (x y : Node) (h : ancestry w x y) :
    (x,y)∈ledgerEdges w ∨ ∃ p, ancestry w x p ∧ (p,y)∈ledgerEdges w := by
  cases h with
  | one edge => exact .inl edge
  | extend before edge => exact .inr ⟨_,before,edge⟩

theorem ledger_append (history suffix : List Event) (start : Nat) :
    ledgerEdgesFrom start (history++suffix)=
      ledgerEdgesFrom start history ++ ledgerEdgesFrom (start+history.length) suffix := by
  induction history generalizing start with
  | nil => simp [ledgerEdgesFrom]
  | cons e rest ih =>
    simp [ledgerEdgesFrom,ih,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem path_mono {es fs : List (Node × Node)} (included : ∀ e∈es, e∈fs)
    (x y : Node) (h : Path es x y) : Path fs x y := by
  induction h with
  | one edge => exact .one (included _ edge)
  | extend _ edge ih => exact .extend ih (included _ edge)

theorem appended_history_preserves_ancestry (w : World) (suffix : List Event)
    (x y : Node) (h : ancestry w x y) : ancestry {w with events := w.events++suffix} x y := by
  apply path_mono (es := ledgerEdges w) (x := x) (y := y) ?_ h
  intro e he
  simp only [ledgerEdges,ledger_append,Nat.zero_add]
  exact List.mem_append_left _ he

theorem first_edge {es : List (Node × Node)} {x y : Node} (h : Path es x y) :
    ∃ z, (x,z)∈es := by
  induction h with
  | one edge => exact ⟨_,edge⟩
  | extend _ _ ih => exact ih

def nodeRank : Node → Nat
  | .hardware _ => 0
  | .birth n => 4*n+3
  | .event n => 4*n+2
  | .version n => 4*n+3
  | .prospective _ _ _ _ _ => 0

theorem ordered_ledger_acyclic (w : World)
    (ordered : ∀ x y, (x,y)∈ledgerEdges w → nodeRank x<nodeRank y)
    (x y : Node) (h : ancestry w x y) : nodeRank x<nodeRank y := by
  induction h with
  | one edge => exact ordered _ _ edge
  | extend _ edge ih => exact Nat.lt_trans ih (ordered _ _ edge)

/-- EmptyTarget classifies the reference in this computed diagnostic, never a
later live birth or an arbitrary vacant address. -/
def EmptyTarget (supply : Supply) (w : World) (q : FusionRequest) (node : Node) : Prop :=
  ∃ p, parentView w q=some p ∧
    meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction=0 ∧
    node=prospective q ∧ fusionRows supply w q=[(⟨w,.empty node⟩,1)]

theorem empty_settlement_has_no_new_edges (supply : Supply) (w : World) (q : FusionRequest)
    (node : Node) (h : EmptyTarget supply w q node) :
    ∀ outcome probability, (outcome,probability)∈fusionRows supply w q → ledgerEdges outcome.world=ledgerEdges w := by
  obtain ⟨_,_,_,_,rows⟩ := h
  intro outcome probability member
  rw [rows] at member
  have eq := List.mem_singleton.mp member
  cases eq
  rfl

theorem prospective_is_not_birth (left right : Node) (a b : Bool) (out n : Nat) :
    Node.prospective left right a b out≠Node.birth n := by intro h; cases h

end CSTTT.FullNative02
