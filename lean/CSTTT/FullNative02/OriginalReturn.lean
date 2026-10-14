import CSTTT.FullNative02.Controls
import CSTTT.FullNative02.GuardFacts

namespace CSTTT.FullNative02
set_option autoImplicit false

/-- An actual-row return, not a constructor over independently supplied
ancestry/ownership/probability witnesses. The supported pair is recovered from
the computed row; all clauses use the same frozen branchesWorld/request. -/
theorem full_actual_positive_return (outcome : Settlement) (probability : Rat)
    (member : (outcome,probability)∈fusionRows renewable branchesWorld mainRequest) :
    ∃ pair, pair∈meeting mainParents.rom mainParents.left.current mainParents.right.current false false ∧
      probability=pairProbability mainParents.rom mainParents.left.current mainParents.right.current false false pair ∧
      0<probability ∧
      outcome.kind=.created (.birth (branchesWorld.events.length+2)) ∧
      outcome.world.residents mainRequest.left=none ∧ outcome.world.residents mainRequest.right=none ∧
      (outcome.world.residents mainRequest.output).map Resident.installed=some (some mainParents.rom) ∧
      (outcome.world.residents mainRequest.output).map Resident.receipts=some [] ∧
      outcome.world.fresh mainRequest.output=false ∧
      (∀ t, branchesWorld.accounts.custody t=.local mainRequest.left ∨
        branchesWorld.accounts.custody t=.local mainRequest.right →
          outcome.world.accounts.custody t=.local mainRequest.output) ∧
      outcome.world.accounts.charge=(paidParents renewable branchesWorld mainRequest mainParents pair probability).accounts.charge ∧
      outcome.world.accounts.cursor=(paidParents renewable branchesWorld mainRequest mainParents pair probability).accounts.cursor ∧
      Prospects.FallbackFissionFusionEmpty Node (ancestry outcome.world) (.birth 0)
        mainParents.left.version mainParents.right.version (.birth (branchesWorld.events.length+2))
        (EmptyTarget renewable branchesWorld mainRequest) := by
  rw [main_positive_rows] at member
  obtain ⟨pair,support,eq⟩ := List.mem_map.mp member
  cases eq
  let computed := pairProbability mainParents.rom mainParents.left.current mainParents.right.current false false pair
  have retired := guarded_parents_retired renewable branchesWorld mainRequest mainParents main_view pair computed
  have stock := all_stock_transferred_unchanged renewable branchesWorld mainRequest mainParents pair computed
  refine ⟨pair,support,rfl,supported_probability_positive _ _ _ _ _ pair support main_meeting_present,
    fusion_birth_from_execution renewable branchesWorld mainRequest mainParents pair computed,retired.1,retired.2,
    output_installed renewable branchesWorld mainRequest mainParents pair computed,
    output_cold renewable branchesWorld mainRequest mainParents pair computed,
    output_cap_consumed renewable branchesWorld mainRequest mainParents pair computed,
    ?_,stock.1,stock.2,?_⟩
  · intro t owned
    exact every_parent_token_transferred renewable branchesWorld mainRequest mainParents pair computed t owned
  · exact original_positive_fusion renewable branchesWorld mainRequest mainParents pair computed (.birth 0)
      branches_source_ancestry.1 branches_source_ancestry.2

/-- The positive row is nonempty and normalized; the existential old formula
is not discharged by its empty disjunct. -/
theorem positive_fusion_exists :
    ∃ outcome probability, (outcome,probability)∈fusionRows renewable branchesWorld mainRequest ∧
      0<probability ∧
      Prospects.FallbackFissionFusionEmpty Node (ancestry outcome.world) (.birth 0)
        mainParents.left.version mainParents.right.version (.birth 24)
        (EmptyTarget renewable branchesWorld mainRequest) := by
  let outcome := settle renewable branchesWorld mainRequest mainParents firstPair firstProbability
  have result := full_actual_positive_return outcome firstProbability first_output_is_actual
  obtain ⟨_,_,_,positive,_,_,_,_,_,_,_,_,_,original⟩ := result
  refine ⟨outcome,firstProbability,first_output_is_actual,positive,?_⟩
  have length : branchesWorld.events.length=22 := by decide +kernel
  simpa only [length] using original

end CSTTT.FullNative02
