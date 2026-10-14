import CSTTT.FullNative02.History
import CSTTT.FullNative02.Diagnostic
import CSTTT.FullNative02.Transport

namespace CSTTT.FullNative02
set_option autoImplicit false

/-- A supported positive readout, recovered from execution, rather than raw
input fields containing a program, pair, probability or ancestry witness. -/
def OwnedFusion (supply : Supply) (w : World) (q : FusionRequest)
    (outcome : Settlement) (probability : Rat) : Prop :=
  ∃ p pair, parentView w q=some p ∧
    pair∈meeting p.rom p.left.current p.right.current q.leftAction q.rightAction ∧
    0<meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction ∧
    probability=pairProbability p.rom p.left.current p.right.current q.leftAction q.rightAction pair ∧
    outcome=settle supply w q p pair probability

theorem every_supported_fusion (supply : Supply) (w : World) (q : FusionRequest)
    (outcome : Settlement) (probability : Rat)
    (member : (outcome,probability)∈fusionRows supply w q) :
    OwnedFusion supply w q outcome probability ∨
      (outcome.world=w ∧ probability=1 ∧ EmptyTarget supply w q (prospective q)) := by
  cases view : parentView w q with
  | none => simp [fusionRows,view] at member
  | some p =>
    by_cases zero : meetingMass p.rom p.left.current p.right.current q.leftAction q.rightAction=0
    · rw [empty_same_world supply w q p view zero] at member
      cases List.mem_singleton.mp member
      exact .inr ⟨rfl,rfl,p,view,zero,rfl,empty_same_world supply w q p view zero⟩
    · simp only [fusionRows,view,if_neg zero] at member
      obtain ⟨pair,support,eq⟩ := List.mem_map.mp member
      cases eq
      exact .inl ⟨p,pair,view,support,by omega,rfl,rfl⟩

theorem owned_fusion_original_return (supply : Supply) (w : World) (q : FusionRequest)
    (outcome : Settlement) (probability : Rat) (h : OwnedFusion supply w q outcome probability) :
    0<probability ∧ outcome.world.residents q.left=none ∧ outcome.world.residents q.right=none ∧
    outcome.world.fresh q.output=false ∧
    ∃ p pair, parentView w q=some p ∧
      (outcome.world.residents q.output).map Resident.installed=some (some p.rom) ∧
      (outcome.world.residents q.output).map Resident.receipts=some [] ∧
      (∀ t, w.accounts.custody t=.local q.left ∨ w.accounts.custody t=.local q.right →
        outcome.world.accounts.custody t=.local q.output) ∧
      outcome.world.accounts.charge=(paidParents supply w q p pair probability).accounts.charge ∧
      outcome.world.accounts.cursor=(paidParents supply w q p pair probability).accounts.cursor ∧
      (∀ source, ancestry w source p.left.version → ancestry w source p.right.version →
        Prospects.FallbackFissionFusionEmpty Node (ancestry outcome.world) source
          p.left.version p.right.version (.birth (w.events.length+2)) (EmptyTarget supply w q)) := by
  obtain ⟨p,pair,view,support,mass,probabilityEq,rfl⟩ := h
  have positive := supported_probability_positive p.rom p.left.current p.right.current
    q.leftAction q.rightAction pair support mass
  rw [← probabilityEq] at positive
  have retired := guarded_parents_retired supply w q p view pair probability
  exact ⟨positive,retired.1,retired.2,output_cap_consumed _ _ _ _ _ _,p,pair,view,
    output_installed _ _ _ _ _ _,output_cold _ _ _ _ _ _,
    every_parent_token_transferred _ _ _ _ _ _,rfl,rfl,
    fun source left right => original_positive_fusion _ _ _ _ _ _ source left right⟩

theorem main_all_support_owned (outcome : Settlement) (probability : Rat)
    (member : (outcome,probability)∈fusionRows renewable branchesWorld mainRequest) :
    OwnedFusion renewable branchesWorld mainRequest outcome probability := by
  rw [main_positive_rows] at member
  obtain ⟨pair,support,eq⟩ := List.mem_map.mp member
  cases eq
  exact ⟨mainParents,pair,main_view,support,main_meeting_present,rfl,rfl⟩

end CSTTT.FullNative02
