import CSTTT.POS04.C2C3

/-! C7 follows the frozen `audit/M3_model_spec.md:23,31,34-35`.
The two distributions below are computed from the declared two-edge couplings;
the variants are the raw interventions in the frozen POS-04 JSON. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

inductive C7Variant where
  | positive | negAggregate | negTransport | negUncoupled
  | missingMixedEvent | sourceAbsent
  deriving DecidableEq, Repr

def c7Coupling (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    List (Fin 2 × Fin 2) :=
  if id = .crossed && (v = .negUncoupled ||
      (v = .negTransport && tag = .target)) then coupling .diagonal
  else coupling id

def c7Reassembly (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    AssemblageId :=
  if id = .crossed && (v = .negUncoupled ||
      (v = .negTransport && tag = .target)) then .diagonal
  else reassembly tag id

def c7Observables (v : C7Variant) (tag : Tag) : List JointObservable :=
  if v = .negAggregate then [] else jointObservables tag

def c7Realized (v : C7Variant) : List Stage :=
  if v = .missingMixedEvent then [.sourceLive,.targetExit] else realizedStages

def c7SourcePresent (v : C7Variant) : Bool :=
  if v = .sourceAbsent then false else receiver.sourcePresent

def c7PairCount (v : C7Variant) (tag : Tag) (id : AssemblageId)
    (left right : HistoryId) : Nat :=
  ((c7Coupling v tag id).filter fun pair =>
    leftBranch pair.1 == left && rightBranch pair.2 == right).length

/-- Exact `jointPairing` probability, with its denominator from the raw
coupling length. -/
def jointPairing (v : C7Variant) (tag : Tag) (id : AssemblageId)
    (left right : HistoryId) : Rat :=
  (c7PairCount v tag id left right : Rat) / (c7Coupling v tag id).length

def c7Branchwise (_v : C7Variant) (_tag : Tag) (_id : AssemblageId) :
    List HistoryId × List HistoryId :=
  ([leftBranch 0,leftBranch 1], [rightBranch 0,rightBranch 1])

def c7JointDistribution (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    List (Nat × Nat) :=
  (historyIds.flatMap fun l => historyIds.map fun r =>
    (c7PairCount v tag id l r, (c7Coupling v tag id).length))

def c7Recombination (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    (List HistoryId × List HistoryId) × List (Nat × Nat) :=
  (c7Branchwise v tag id,
    if .jointPairing ∈ c7Observables v tag then c7JointDistribution v tag id else [])

def C7Strict (v : C7Variant) (tag : Tag) : Prop :=
  AssemblageId.diagonal ≠ .crossed ∧
  c7Branchwise v tag .diagonal = c7Branchwise v tag .crossed ∧
  c7Recombination v tag .diagonal ≠ c7Recombination v tag .crossed

/-- The indexed reassembly row is checked against that assemblage's raw
coupling, even when two assemblages happen to have equal couplings. -/
def C7LocallyConsistent (v : C7Variant) (tag : Tag) : Prop :=
  ∀ id ∈ assemblageIds,
    c7Coupling v tag id = coupling (c7Reassembly v tag id) ∧
    (c7Coupling v tag id).length = 2 ∧
    (c7Coupling v tag id).Nodup

def C7HistoriesAdmissible (tag : Tag) : Prop :=
  ∀ id ∈ historyIds, supportedHistory tag id = true

def c7MixedRealized (v : C7Variant) : Bool :=
  events.any fun e => e.id != .exit && e.atomic && e.sourceSupport &&
    e.targetSupport && decide (e.fromStage ∈ c7Realized v) &&
    decide (e.toStage ∈ c7Realized v)

def c7ReceiverActive (v : C7Variant) : Bool :=
  c7SourcePresent v && receiver.targetReceiverFunded && receiver.funded &&
    (!receiver.mixedEventRequired || c7MixedRealized v)

def c7Display (v : C7Variant) (tag : Tag) (id : AssemblageId) :
    List (Nat × Nat) :=
  if .jointPairing ∈ c7Observables v tag then c7JointDistribution v tag id else []

def C7OperationalUse (v : C7Variant) (tag : Tag) : Prop :=
  c7MixedRealized v = true ∧ c7ReceiverActive v = true ∧
  c7Display v tag .diagonal ≠ c7Display v tag .crossed ∧
  (∀ s ∈ kernel, ∀ t ∈ kernel,
    rowWeight (actionRow tag s (canonicalAction s)) t = taggedPNum tag s t)

def C7Pass (v : C7Variant) (tag : Tag) : Prop :=
  C7LocallyConsistent v tag ∧ C7HistoriesAdmissible tag ∧
    C7Strict v tag ∧ C7OperationalUse v tag

def C7Transport (v : C7Variant) : Prop :=
  c7Observables v .source = c7Observables v .target ∧
  ∀ id ∈ assemblageIds,
    c7Branchwise v .source id = c7Branchwise v .target id ∧
    c7Coupling v .source id = c7Coupling v .target id ∧
    c7JointDistribution v .source id = c7JointDistribution v .target id

theorem c7_exact_distributions (tag : Tag) :
    jointPairing .positive tag .diagonal .repA .classB = 1/2 ∧
    jointPairing .positive tag .crossed .repA .split = 1/2 := by
  cases tag <;> simp [jointPairing, c7PairCount, c7Coupling, coupling,
    leftBranch, rightBranch]

/-- Every raw coupling has two edges; the distribution entries are exact
numerator/denominator pairs and `jointPairing` is their rational value. -/
theorem c7_joint_denominator_two (v : C7Variant) (tag : Tag)
    (id : AssemblageId) : (c7Coupling v tag id).length = 2 := by
  cases v <;> cases tag <;> cases id <;> decide

theorem c7_joint_distribution_probability (v : C7Variant) (tag : Tag)
    (id : AssemblageId) :
    ((c7JointDistribution v tag id).map Prod.fst).sum = 2 ∧
    (∀ entry ∈ c7JointDistribution v tag id, entry.2 = 2) := by
  cases v <;> cases tag <;> cases id <;> decide

theorem c7_each_tag (tag : Tag) : C7Pass .positive tag := by
  cases tag <;> (simp only [C7Pass, C7Strict, C7LocallyConsistent,
    C7HistoriesAdmissible, C7OperationalUse] <;> decide)

theorem c7_staged_transport : C7Transport .positive := by
  simp only [C7Transport]
  decide

theorem neg_c7_aggregate_loses_refinement (tag : Tag) :
    ¬ C7Strict .negAggregate tag := by
  cases tag <;> simp only [C7Strict] <;> decide

theorem neg_c7_uncoupled_consistent (tag : Tag) :
    C7LocallyConsistent .negUncoupled tag := by
  cases tag <;> simp only [C7LocallyConsistent] <;> decide

theorem neg_c7_uncoupled_loses_refinement (tag : Tag) :
    ¬ C7Strict .negUncoupled tag := by
  cases tag <;> simp only [C7Strict] <;> decide

theorem neg_c7_transport_locally_consistent :
    C7LocallyConsistent .negTransport .target := by
  simp only [C7LocallyConsistent]
  decide

theorem neg_c7_transport_loses_target_refinement :
    ¬ C7Strict .negTransport .target := by
  simp only [C7Strict]
  decide

theorem neg_c7_transport_breaks_staged_equation :
    ¬ C7Transport .negTransport := by
  simp only [C7Transport]
  decide

theorem c7_missing_mixed_event_fails (tag : Tag) :
    ¬ C7OperationalUse .missingMixedEvent tag := by
  cases tag <;> simp only [C7OperationalUse] <;> decide

theorem c7_source_absent_fails (tag : Tag) :
    ¬ C7OperationalUse .sourceAbsent tag := by
  cases tag <;> simp only [C7OperationalUse] <;> decide

end CSTTT.POS04
