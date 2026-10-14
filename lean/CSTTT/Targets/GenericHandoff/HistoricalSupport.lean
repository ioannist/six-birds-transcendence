import CSTTT.Targets.GenericHandoff.StrategyGame

/-! Recorded acquisition support, separate from funded source run execution.
An edge reads the raw action table and its actual destination. Folding a
recorded history keeps its actual terminal coordinate, never a predictive
representative. Funding belongs to the activated target response; a stronger
lineage interpretation must additionally validate actual source execution.
These are polymorphic table/fold helpers, not supplied handoff verdicts. -/
namespace CSTTT.TargetTheory.GenericHandoff.HistoricalSupport

def fold {State Action : Type} : State → List (Action × State) → State
  | x,[] => x
  | _,(_,y)::rest => fold y rest

def word {State Action : Type} (policy : State → Action) (history : List State) : List (Action × State) :=
  (history.zip (history.drop 1)).map fun e => (policy e.1,e.2)

def rawSupport {State Action : Type} (row : State → Action → List (State × Rat))
    (policy : State → Action) (history : List State) : Prop :=
  history ≠ [] ∧ ∀ edge ∈ history.zip (history.drop 1),
    ∃ weight, (edge.2,weight) ∈ row edge.1 (policy edge.1) ∧ 0 < weight

/-- Empty recorded histories cannot be treated as an arbitrary initialized
endpoint. Singleton histories are allowed but have no fabricated edge. -/
theorem missing_history_rejected {State Action : Type}
    (row : State → Action → List (State × Rat)) (policy : State → Action) :
    ¬ rawSupport row policy [] := fun h => h.1 rfl

theorem fold_word_terminal {State Action : Type} (policy : State → Action)
    (first : State) (rest : List State) (default : State) :
    fold first (word policy (first::rest)) = (first::rest).getLastD default := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    simpa [word,fold,List.zip_cons_cons] using ih next

end CSTTT.TargetTheory.GenericHandoff.HistoricalSupport
