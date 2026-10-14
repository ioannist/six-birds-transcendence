import CSTTT.POS04.Transfer

/-! POS-04 route memory, frozen `audit/M3_model_spec.md:31,46`.
The register stores the raw history/event tuple, never the route name. We
execute a funded canonical target action and read the register from each
resulting state. The first-source-phase readout is deliberately designed, so
the output distinction is near-automatic once persistence is established.
Local route memory checks raw path composition and the receiver's content
map; corridor realization is checked by `RouteMemoryWithCorridor`. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

inductive RouteVariant where
  | positive | negMemory | missingWriter | underfund
  deriving DecidableEq, Repr

def routeWriter (v : RouteVariant) (id : RouteId) : Bool :=
  if v = .missingWriter && id = .b then false
  else recordWriterAvailable .target id

def routeFunding (v : RouteVariant) : C8Variant :=
  if v = .underfund then .negUnderfund else .funded

def routeRegisterWrite (v : RouteVariant) (id : RouteId) :
    Option (List KState × List EventId) :=
  if v = .negMemory then none
  else if receiver.registerRule = .copyRawRouteTuple then some (routeRegister id)
  else none

structure FundedTargetStep where
  factor : KState
  massNum : Nat
  budget : Nat
  register : Option (List KState × List EventId)
  deriving DecidableEq, Repr

def routeStepFrom (v : RouteVariant) (id : RouteId)
    (endpoint : KState) : List FundedTargetStep :=
  (actionRow .target endpoint (canonicalAction endpoint)).filterMap fun entry =>
    match entry.1 with
    | .inK successor =>
        if entry.2 > 0 && successor ∈ c8Greatest (routeFunding v) .target then
          some ⟨successor,entry.2,
            ledger.initialBudget - ledger.actionCost + ledger.rechargePerAction,
            routeRegisterWrite v id⟩
        else none
    | .p2w0 | .p5w1 => none

def routeFundedStep (v : RouteVariant) (id : RouteId) : List FundedTargetStep :=
  let history := (routeOf id).sourceHistory
  if routeReferencesResolve id && routeEventsCompose id &&
      decide (history ∈ bridgeFrontier) &&
      supportedHistory .source history && routeWriter v id &&
      c8Available (routeFunding v) .target then
    match receiverFactor .positive history with
    | some endpoint =>
        if endpoint ∈ c8Greatest (routeFunding v) .target then
          routeStepFrom v id endpoint
        else []
    | none => []
  else []

def routeReadFromState (step : FundedTargetStep) : Option Nat :=
  step.register.bind fun tuple =>
    tuple.1.head?.map fun first => ambientPhase (.inK first)

def routeFutureOutput (v : RouteVariant) (id : RouteId) : Option Nat :=
  let reads := (routeFundedStep v id).map routeReadFromState
  if reads.isEmpty then none
  else if reads.all (fun read => some read == reads.head?) then reads.head?.join
  else none

def RouteMemoryPass (v : RouteVariant) : Prop :=
  (∀ id ∈ routeIds, routeReferencesResolve id = true ∧
    routeEventsCompose id = true) ∧
  routeRegister .a ≠ routeRegister .b ∧
  resourceOwner .target = .target ∧ routeReadoutOwner = .target ∧
  routeWriter v .a = true ∧ routeWriter v .b = true ∧
  c8Available (routeFunding v) .target = true ∧
  routeFundedStep v .a ≠ [] ∧ routeFundedStep v .b ≠ [] ∧
  (∀ step ∈ routeFundedStep v .a,
    step.register = some (routeRegister .a) ∧ step.budget = 1 ∧
      routeReadFromState step = some 0) ∧
  (∀ step ∈ routeFundedStep v .b,
    step.register = some (routeRegister .b) ∧ step.budget = 1 ∧
      routeReadFromState step = some 1) ∧
  routeFutureOutput v .a = some 0 ∧
  routeFutureOutput v .b = some 1

/-- Combined certification records corridor realization separately from the
local retained-route-memory check. -/
def RouteMemoryWithCorridor (v : RouteVariant) (cv : CorridorVariant) : Prop :=
  RouteMemoryPass v ∧ CorridorPass cv

theorem route_step_uses_t1_canonical_P (s t : KState) :
    rowWeight (actionRow .target s (canonicalAction s)) t =
      taggedPNum .target s t :=
  canonical_action_row_agrees_with_tagged_P .target s t

theorem route_positive_steps :
    routeFundedStep .positive .a =
      [⟨.p2w1,4,1,some (routeRegister .a)⟩] ∧
    routeFundedStep .positive .b =
      [⟨.p2w1,4,1,some (routeRegister .b)⟩] := by decide

theorem route_positive_future_outputs :
    routeFutureOutput .positive .a = some 0 ∧
    routeFutureOutput .positive .b = some 1 := by decide

theorem route_memory_positive : RouteMemoryPass .positive := by
  simp only [RouteMemoryPass]
  decide

theorem route_with_corridor_positive :
    RouteMemoryWithCorridor .positive .positive :=
  ⟨route_memory_positive, corridor_positive⟩

theorem neg_route_memory_no_register :
    routeFutureOutput .negMemory .a = none ∧
    routeFutureOutput .negMemory .b = none := by decide

theorem neg_route_memory_fails : ¬ RouteMemoryPass .negMemory := by
  intro h
  have hout := neg_route_memory_no_register
  rcases h with ⟨_,_,_,_,_,_,_,_,_,_,_,hclaimed,_⟩
  rw [hout.1] at hclaimed
  contradiction

theorem route_missing_writer_fails : ¬ RouteMemoryPass .missingWriter := by
  intro h
  have hw : routeWriter .missingWriter .b = false := by decide
  rcases h with ⟨_,_,_,_,_,hclaimed,_⟩
  rw [hw] at hclaimed
  contradiction

theorem route_gap_preserves_local_memory : RouteMemoryPass .positive :=
  route_memory_positive

theorem route_gap_breaks_combined :
    ¬ RouteMemoryWithCorridor .positive .gap := by
  intro h
  exact neg_corridor_gap_fails h.2

theorem route_underfunded_step_absent :
    routeFundedStep .underfund .a = [] ∧
    routeFundedStep .underfund .b = [] := by decide

theorem route_underfund_fails : ¬ RouteMemoryPass .underfund := by
  intro h
  have ha : c8Available (routeFunding .underfund) .target = false := by decide
  rcases h with ⟨_,_,_,_,_,_,havailable,_⟩
  rw [ha] at havailable
  contradiction

end CSTTT.POS04
