import CSTTT.POS04.Assigned.C6DynamicsLinks

/-! Single-field proposal guards on the entire defined closure. Proposals are
not inputs to dynamics6/future6; equality with the defined readout is required.
This is the ReadoutGuards method, not a stored clause acceptance predicate. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

inductive Field6 where
  | factor | predictive | counter | tickCounter | tickPhase | progress | writer
  | record | residue | maintenance | owner | budget | enabled
  deriving DecidableEq, Repr

abbrev ReadoutValue6 : Field6 → Type
  | .factor => Ambient
  | .predictive => PredictiveNow
  | .counter | .tickCounter | .tickPhase | .progress | .record | .budget => Nat
  | .writer | .maintenance | .enabled => Bool
  | .residue => List KState × List EventId
  | .owner => Tag

def readout6 (a : Assignment) (tag : Tag) (f : Field6) (x : Run6) : ReadoutValue6 f :=
  let d := runInputs6 a tag
  match f with
  | .factor => x.factor
  | .predictive => (observation6 d tag x).predictive
  | .counter => x.counter
  | .tickCounter => x.ticks
  | .tickPhase => (observation6 d tag x).tickPhase
  | .progress => (observation6 d tag x).cumulativeProgress
  | .writer => writer6 d tag x.residue
  | .record => (observation6 d tag x).endogenousRecordCount
  | .residue => (observation6 d tag x).routeResidue
  | .maintenance => (observation6 d tag x).maintenanceState
  | .owner => (observation6 d tag x).owner
  | .budget => budget6 d
  | .enabled => enabled6 d x

def ProposedReadoutAgrees6 (a : Assignment) (tag : Tag) (f : Field6)
    (proposal : Run6 → ReadoutValue6 f) : Prop :=
  ∀ x, Closure6 a tag x → proposal x = readout6 a tag f x

theorem defined_readout6_agrees (a : Assignment) (tag : Tag) (f : Field6) :
    ProposedReadoutAgrees6 a tag f (readout6 a tag f) := fun _ _ => rfl

theorem readout6_guard (a : Assignment) (tag : Tag) (f : Field6)
    (proposal : Run6 → ReadoutValue6 f) (x : Run6) (hx : Closure6 a tag x)
    (hbad : proposal x ≠ readout6 a tag f x) : ¬ ProposedReadoutAgrees6 a tag f proposal :=
  fun h => hbad (h x hx)

/-- Constants/caps chosen by the field rule: the cap two is the audited
endpoint counter from G1c; three real supported steps reach beyond that cap.
They are method proposals, not scientific model mutations. -/
def cappedReadout6 (a : Assignment) (tag : Tag) (f : Field6) (x : Run6) : ReadoutValue6 f :=
  match f with
  | .factor => .p2w0
  | .predictive => .exit2
  | .counter => min x.counter 2
  | .tickCounter => min x.ticks 2
  | .tickPhase => (min x.ticks 2) % 2
  | .progress => min x.counter 2
  | .writer => false
  | .record => min (observation6 (runInputs6 a tag) tag x).endogenousRecordCount 2
  | .residue => ([],[])
  | .maintenance => false
  | .owner => if tag = .source then .target else .source
  | .budget => 0
  | .enabled => false

theorem canonical_each_readout6_guard (tag : Tag) (f : Field6) :
    ¬ ProposedReadoutAgrees6 canonical tag f (cappedReadout6 canonical tag f) := by
  apply readout6_guard _ _ f _ (thirdStep6 tag) (canonical_three_step_closure6 tag)
  cases f <;> cases tag <;> simp only [cappedReadout6,readout6,ReadoutValue6] <;> decide

theorem canonical_budget6_closure (tag : Tag) (x : Run6) (hx : Closure6 canonical tag x) :
    x.funded = true ∧ budget6 (runInputs6 canonical tag) = 1 ∧
      budgetAfter6 (runInputs6 canonical tag) = budget6 (runInputs6 canonical tag) := by
  refine ⟨?_,by cases tag <;> rfl,canonical_ledger_conservation6 tag⟩
  induction hx with
  | root x hm =>
    have hr : ∀ y ∈ roots6 canonical tag, y.funded = true := by cases tag <;> decide
    exact hr x hm
  | step hx act o ho ih =>
    change (update6 (runInputs6 canonical tag) _ act o).funded = true
    simp only [update6,ih]
    cases tag <;> rfl

theorem assigned_ledger6_guard (tag : Tag) :
    ¬ LedgerConservation6 (zeroReturn8 canonical) tag := by
  unfold LedgerConservation6
  cases tag <;> decide

end CSTTT.POS04.Assigned
