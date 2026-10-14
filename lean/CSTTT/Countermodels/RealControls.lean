import CSTTT.POS04.Countermodels
import CSTTT.Temporal.Closure
import CSTTT.Corridor.FiniteTemporalCorridor
import CSTTT.Corridor.Fission
import CSTTT.Transport.RecordArrow
import CSTTT.Package.FiniteGluing
import CSTTT.Robustness.DefectVector
import CSTTT.Autonomy.UnboundedInvariant

/-!
Finite real-predicate controls for TTN-01, 03, 05, 07, 08, 10, 11, 12.
Raw rules and their relationship to frozen CM-02/03/05/07/08/10/11/13 are
recorded in `audit/N1_countermodel_plan.md`. No stored verdict flags are used.
-/

namespace CSTTT.RealControls

open CSTTT.Objecthood.T1Audit
open CSTTT.POS04

/-! TTN-01. CM-02's two stages have source-only then target-only support.
The target factor is initialized by copying the raw endpoint coordinate;
this operation does not edit the stage list or its support. Fields irrelevant
to `HasMixedSupport` are generated from each tag's position in `tags`. -/
/-- CM-02's one declared copy edge: the target receives the source's raw T1
coordinate at the endpoint. It is outside the temporal support graph. -/
def detachedCopy (x : TaggedState) : TaggedState := (.target,x.2)

def detachedStage (tag : Tag) : CSTTT.CorridorTheory.FiniteTemporalStage :=
  let i := tags.idxOf tag
  { index := i, support := [tagCarrierId tag], realized := true,
    predictiveRank := i, orderRank := i, tickIndex := i,
    progressRank := i, recordValue := i, routeResidue := [],
    maintenanceOwner := tagCarrierId tag }

def detachedStages : List CSTTT.CorridorTheory.FiniteTemporalStage :=
  [detachedStage .source,detachedStage .target]

def DetachedEndpointMatch : Prop :=
  detachedCopy (.source,.p1w0) = (.target,.p1w0) ∧
  rawM .source .p1w0 = rawM (detachedCopy (.source,.p1w0)).1
    (detachedCopy (.source,.p1w0)).2

def DetachedCopyControl : Prop :=
  tagCarrierId .source ≠ tagCarrierId .target ∧
  DetachedEndpointMatch ∧
  PackagePass .funded .target ∧
  TargetAutonomy .funded c8WithdrawnReceiver ∧
  CSTTT.CorridorTheory.NoRealizedGap detachedStages ∧
  ¬ CSTTT.CorridorTheory.HasMixedSupport
    (tagCarrierId .source) (tagCarrierId .target) detachedStages

theorem ttn01_detached_copy : DetachedCopyControl := by
  refine ⟨pos04_carriers_distinct, ?_, package_funded_each_tag .target,
    target_only_autonomy_positive, ?_, ?_⟩
  · simp [DetachedEndpointMatch, detachedCopy, rawM,
      rawContinuation, actionRow]
  · simp [CSTTT.CorridorTheory.NoRealizedGap, detachedStages,
      detachedStage]
  · simp [CSTTT.CorridorTheory.HasMixedSupport, detachedStages,
      detachedStage, tagCarrierId, tags]
    decide

theorem ttn01_no_atomic_corridor
    (d : CSTTT.CorridorTheory.AtomicTemporalCorridorData)
    (hs : d.source = tagCarrierId .source)
    (ht : d.target = tagCarrierId .target)
    (hstages : d.stages = detachedStages) :
    ¬ Nonempty (CSTTT.CorridorTheory.AtomicTemporalCorridorCertificate d) := by
  apply CSTTT.CorridorTheory.noMixedStageExcludesAtomicCorridor d
  rw [hs,ht,hstages]
  exact ttn01_detached_copy.2.2.2.2.2

/-- The model data itself is existential: an endpoint copy and a stage list
with package and autonomy but no mixed-support corridor. -/
theorem ttn01_exists :
    ∃ copy : TaggedState → TaggedState,
    ∃ stages : List CSTTT.CorridorTheory.FiniteTemporalStage,
      copy (.source,.p1w0) = (.target,.p1w0) ∧
      rawM .source .p1w0 = rawM (copy (.source,.p1w0)).1
        (copy (.source,.p1w0)).2 ∧
      PackagePass .funded .target ∧
      TargetAutonomy .funded c8WithdrawnReceiver ∧
      ¬ CSTTT.CorridorTheory.HasMixedSupport
        (tagCarrierId .source) (tagCarrierId .target) stages := by
  exact ⟨detachedCopy,detachedStages,ttn01_detached_copy.2.1.1,
    ttn01_detached_copy.2.1.2,
    ttn01_detached_copy.2.2.1,ttn01_detached_copy.2.2.2.1,
    ttn01_detached_copy.2.2.2.2.2⟩

/-! TTN-03. CM-03's published permutations, in source order 0,1,2.
The raw record rule `constant` means that each successor records zero.
Strict arrow uses the actual `RecordTheory.StrictlyMonotoneOn` interface,
with the finite state order and natural-number record order. -/
abbrev RoutePoint := Fin 3

def routeA : RoutePoint → RoutePoint
  | 0 => 0 | 1 => 2 | 2 => 1
def routeB : RoutePoint → RoutePoint
  | 0 => 1 | 1 => 0 | 2 => 2
def constantRecord (_ : RoutePoint) : Nat := 0
def routeEnum : CSTTT.FiniteEnum RoutePoint :=
  ⟨[0,1,2], by
    intro x
    have h : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
    rcases h with h | h | h
    · have hx : x = 0 := Fin.ext h; simp [hx]
    · have hx : x = 1 := Fin.ext h; simp [hx]
    · have hx : x = 2 := Fin.ext h; simp [hx]⟩
def routeCarrier : CSTTT.Carrier :=
  { id := ⟨0⟩, State := RoutePoint, stateEnum := routeEnum }
def routeAlphabet : CSTTT.TemporalAlphabet :=
  { predictiveType := RoutePoint, orderType := RoutePoint,
    tickType := RoutePoint, progressType := RoutePoint,
    recordType := RoutePoint, routeType := RoutePoint,
    maintenanceType := RoutePoint, predictiveEnum := routeEnum,
    orderEnum := routeEnum, tickEnum := routeEnum,
    progressEnum := routeEnum, recordEnum := routeEnum,
    routeEnum := routeEnum, maintenanceEnum := routeEnum }
def routeSuccessor (s t : RoutePoint) : Prop :=
  t = routeA s ∨ t = routeB s
def routeSpec : CSTTT.TemporalClosureSpec routeCarrier routeAlphabet :=
  { signature := fun s =>
      { predictiveNow :=
          { predictiveClass := s, routeResidue := s,
            futureSufficient := ∀ x y : RoutePoint,
              routeA x = routeA y → routeB x = routeB y },
        orderState := s, tickPhase := s, progressState := s,
        arrowRecord := s, maintenanceState := s, owner := routeCarrier.id },
    successor := routeSuccessor,
    viableTick := fun s => ∃ t, routeSuccessor s t,
    tickProgress := fun s t => s ≠ t,
    recordPreorder := fun a b : RoutePoint => a.val ≤ b.val,
    endogenousRecordUpdate := fun s t =>
      routeSuccessor s t ∧ constantRecord s < constantRecord t,
    maintenanceResources := fun _ => [] }
def strictRecordEdge (step : RoutePoint → RoutePoint) : Prop :=
  ∃ s : RoutePoint, constantRecord s < constantRecord (step s)

def RouteHolonomyWithoutArrow : Prop :=
  (∀ s : RoutePoint, routeA (routeA s) = s) ∧
  (∀ s : RoutePoint, routeB (routeB s) = s) ∧
  routeA (routeB 0) ≠ routeB (routeA 0) ∧
  ¬ strictRecordEdge routeA ∧ ¬ strictRecordEdge routeB ∧
  (¬ ∃ s t : RoutePoint, routeSpec.endogenousRecordUpdate s t) ∧
  ¬ CSTTT.RecordTheory.StrictlyMonotoneOn
    (fun a b : RoutePoint => a < b) (· < ·) constantRecord

theorem ttn03_holonomy_without_arrow : RouteHolonomyWithoutArrow := by
  unfold RouteHolonomyWithoutArrow strictRecordEdge
    CSTTT.RecordTheory.StrictlyMonotoneOn
  simp [routeSpec,constantRecord]
  decide

structure RouteControl where
  first : RoutePoint → RoutePoint
  second : RoutePoint → RoutePoint
  record : RoutePoint → Nat

def RouteControlPass (m : RouteControl) : Prop :=
  (∀ s, m.first (m.first s) = s) ∧
  (∀ s, m.second (m.second s) = s) ∧
  m.first (m.second 0) ≠ m.second (m.first 0) ∧
  (¬ ∃ s, m.record s < m.record (m.first s)) ∧
  (¬ ∃ s, m.record s < m.record (m.second s)) ∧
  (¬ ∃ s t : RoutePoint,
    (t = m.first s ∨ t = m.second s) ∧ m.record s < m.record t) ∧
  ¬ CSTTT.RecordTheory.StrictlyMonotoneOn
    (fun a b : RoutePoint => a < b) (· < ·) m.record

theorem ttn03_exists : ∃ m : RouteControl, RouteControlPass m := by
  refine ⟨⟨routeA,routeB,constantRecord⟩,?_⟩
  exact ttn03_holonomy_without_arrow

/-! TTN-05. CM-07 has one boundary node, a phase group mod 2, and a
loop translation by 1. Identity and loop are the two paths at that node;
their present phases are computed by composing the declared translation. -/
inductive ClockPath where | identity | loop deriving DecidableEq, Repr
def clockTranslate (phase : Fin 2) : Fin 2 := ⟨(phase.val + 1) % 2, by omega⟩
def clockBoundary (_ : ClockPath) : Fin 1 := 0
def clockLocalNow : ClockPath → Fin 2
  | .identity => 0
  | .loop => clockTranslate 0
def clockHolonomy : Prop := clockTranslate 0 ≠ (0 : Fin 2)

theorem ttn05_clock_loop :
    clockHolonomy ∧ clockBoundary .identity = clockBoundary .loop ∧
    clockLocalNow .identity ≠ clockLocalNow .loop ∧
    ¬ CSTTT.RouteTheory.CanonicalGlobalNow clockBoundary clockLocalNow := by
  have hbound : clockBoundary .identity = clockBoundary .loop := rfl
  have hnow : clockLocalNow .identity ≠ clockLocalNow .loop := by decide
  exact ⟨by simp [clockHolonomy,clockTranslate],hbound,hnow,
    CSTTT.RouteTheory.noCanonicalGlobalNowOfTranslationHolonomy
      clockBoundary clockLocalNow .identity .loop hbound hnow⟩

structure ClockLoopControl where
  translation : Fin 2 → Fin 2

def loopNow (m : ClockLoopControl) : ClockPath → Fin 2
  | .identity => 0
  | .loop => m.translation 0

theorem ttn05_exists :
    ∃ m : ClockLoopControl,
      m.translation 0 ≠ (0 : Fin 2) ∧
      ¬ CSTTT.RouteTheory.CanonicalGlobalNow clockBoundary (loopNow m) := by
  refine ⟨⟨clockTranslate⟩,ttn05_clock_loop.1,?_⟩
  exact ttn05_clock_loop.2.2.2

/-! TTN-07. CM-05 is a singleton state with a self transition and phase
zero. A declared tick is viable when the transition is defined and preserves
the clock phase; genuine progress is the `TemporalClosureSpec` successor
plus strict progress relation, here derived from the successor's rank. -/
inductive StoppedState where | stop deriving DecidableEq, Repr

def stoppedCarrier : CSTTT.Carrier :=
  { id := ⟨0⟩, State := StoppedState,
    stateEnum := ⟨[.stop], by intro x; cases x; simp⟩ }

def oneEnum : CSTTT.FiniteEnum (Fin 1) :=
  ⟨[0], by
    intro x
    have h : x = 0 := by apply Fin.ext; omega
    simp [h]⟩

def stoppedAlphabet : CSTTT.TemporalAlphabet :=
  { predictiveType := Fin 1, orderType := Fin 1, tickType := Fin 1,
    progressType := Fin 1, recordType := Fin 1, routeType := Fin 1,
    maintenanceType := Fin 1, predictiveEnum := oneEnum,
    orderEnum := oneEnum, tickEnum := oneEnum, progressEnum := oneEnum,
    recordEnum := oneEnum, routeEnum := oneEnum,
    maintenanceEnum := oneEnum }

def stoppedStep (_ : StoppedState) : StoppedState := .stop
def stoppedPhase (_ : stoppedCarrier.State) : Fin 1 := 0

def stoppedSpec : CSTTT.TemporalClosureSpec stoppedCarrier stoppedAlphabet :=
  { signature := fun _ =>
      { predictiveNow := { predictiveClass := (0 : Fin 1),
                           routeResidue := (0 : Fin 1),
                           futureSufficient := ∀ x y : stoppedCarrier.State,
                             stoppedStep x = stoppedStep y },
        orderState := (0 : Fin 1), tickPhase := (0 : Fin 1),
        progressState := (0 : Fin 1), arrowRecord := (0 : Fin 1),
        maintenanceState := (0 : Fin 1), owner := stoppedCarrier.id },
    successor := fun s t => stoppedStep s = t,
    viableTick := fun s => stoppedPhase (stoppedStep s) = stoppedPhase s,
    tickProgress := fun s t => s ≠ t,
    recordPreorder := fun a b => a = b,
    endogenousRecordUpdate := fun s t => s ≠ t,
    maintenanceResources := fun _ => [] }

theorem ttn07_stable_tick_no_progress :
    stoppedSpec.viableTick .stop ∧
    stoppedSpec.successor .stop (stoppedStep .stop) ∧
    ¬ ∃ next : stoppedCarrier.State,
      stoppedSpec.successor .stop next ∧ stoppedSpec.tickProgress .stop next := by
  simp [stoppedSpec, stoppedStep, stoppedPhase]

theorem ttn07_exists :
    ∃ spec : CSTTT.TemporalClosureSpec stoppedCarrier stoppedAlphabet,
      spec.viableTick .stop ∧ spec.successor .stop (stoppedStep .stop) ∧
      ¬ ∃ next : stoppedCarrier.State,
        spec.successor .stop next ∧ spec.tickProgress .stop next :=
  ⟨stoppedSpec,ttn07_stable_tick_no_progress⟩

/-! TTN-08. CM-08 declares two clauses over one shared coordinate with
local values 0 and 1. Here `Bool` is the same two-value encoding. A clause
accepts exactly its declared local value, and its hard gate checks that same
coordinate. These rules are fixed before evaluating either assignment;
the opposite value fails each local rule. The two scope occurrences make a
global restriction equation inconsistent. -/
def oneCoordEnum : CSTTT.FiniteEnum (Fin 1) := oneEnum
def boolEnum : CSTTT.FiniteEnum Bool :=
  ⟨[false,true], by intro x; cases x <;> simp⟩
def conflictAlphabet : CSTTT.PackageAlphabet :=
  { Coord := Fin 1, Value := Bool,
    coordEnum := oneCoordEnum, valueEnum := boolEnum }

def conflictClause (i : Bool) :
    CSTTT.ClauseSpec .c1Objecthood conflictAlphabet :=
  { scope := [(0 : Fin 1)],
    accepts := fun assignment => assignment (0 : Fin 1) = some i,
    hardGate := fun assignment => assignment (0 : Fin 1) = some i,
    essentialResources := [] }

def conflictAssignment (i : Bool) :
    CSTTT.GlobalAssignment conflictAlphabet := fun _ => some i

def conflictWitness (i : Bool) :
    CSTTT.ClauseWitness .c1Objecthood conflictAlphabet
      (conflictClause i) :=
  ⟨conflictAssignment i, rfl, rfl⟩

def conflictTree : CSTTT.PackageTheory.RootedJoinTree Bool (Fin 1) :=
  { root := false,
    parent := fun i => if i then some false else none,
    rootHasNoParent := rfl,
    everyNonrootHasParent := by
      intro i hi; cases i
      · exact False.elim (hi rfl)
      · exact ⟨false,rfl⟩,
    rank := fun i => if i then 1 else 0,
    parentDecreases := by
      intro i p h; cases i <;> cases p <;> simp at h ⊢,
    scope := fun _ _ => True,
    covers := by intro _; exact ⟨false,True.intro⟩,
    runningIntersection := by
      intro i j c _ _
      cases i <;> cases j
      · exact .refl false True.intro
      · exact .step True.intro True.intro (Or.inr rfl)
          (.refl true True.intro)
      · exact .step True.intro True.intro (Or.inl rfl)
          (.refl false True.intro)
      · exact .refl true True.intro }

def conflictLocal (i : Bool) (_ : Fin 1) : Bool := i
def conflictAccepted (i : Bool) : Prop :=
  (conflictClause i).accepts (conflictWitness i).assignment
def conflictGate (i : Bool) : Prop :=
  (conflictClause i).hardGate (conflictWitness i).assignment

theorem conflict_opposite_rejected (i : Bool) :
    ¬ (conflictClause i).accepts (conflictAssignment (!i)) := by
  cases i <;> simp [conflictClause,conflictAssignment]

theorem ttn08_local_global_obstruction :
    (∀ i : Bool, conflictAccepted i ∧ conflictGate i) ∧
    ¬ Nonempty (CSTTT.PackageTheory.IntegratedPackageWitness
      conflictTree conflictLocal conflictAccepted conflictGate) := by
  constructor
  · intro i; cases i <;> exact ⟨rfl,rfl⟩
  · rintro ⟨w⟩
    have hfalse := w.restricts false 0 True.intro
    have htrue := w.restricts true 0 True.intro
    simp [conflictLocal] at hfalse htrue
    exact Bool.false_ne_true (hfalse.symm.trans htrue)

theorem ttn08_exists :
    ∃ assignment : Bool → Fin 1 → Bool,
      (∀ i : Bool,
        (conflictWitness i).assignment (0 : Fin 1) =
          some (assignment i 0) ∧ conflictAccepted i ∧ conflictGate i) ∧
      ¬ Nonempty (CSTTT.PackageTheory.IntegratedPackageWitness
        conflictTree assignment conflictAccepted conflictGate) := by
  refine ⟨conflictLocal,?_,ttn08_local_global_obstruction.2⟩
  intro i
  exact ⟨rfl,(ttn08_local_global_obstruction.1 i).1,
    (ttn08_local_global_obstruction.1 i).2⟩

/-! TTN-11. CM-11 declares two distinct target branches swapped by an
involution. Each branch is a relabeled POS-04 T1 factor. The relabeling
transports target ownership, while the canonical transition and C1-C7
coordinates are invariant under that relabeling. The same C8 deletion and
withdrawal rules are rerun with the branch-owned resource. The raw fork
edges are two source-to-branch endpoint copies, and relatedness also checks
the POS-04 receiver output. This is a post-corridor structural fork, not a
claim of numerical identity or of two independent pre-branch corridors. -/
structure ForkTarget where
  branch : Bool
  endpoint : KState
  deriving DecidableEq, Repr

def forkLeft : ForkTarget := ⟨false,.p1w0⟩
def forkRight : ForkTarget := ⟨true,.p1w0⟩
def forkCopy (branch : Bool) (source : KState) : ForkTarget :=
  ⟨branch,source⟩
def forkEdges : List (KState × ForkTarget) :=
  [false,true].map fun branch => (.p1w0,forkCopy branch .p1w0)
def forkCarrierId (branch : Bool) : CarrierId :=
  ⟨(tagCarrierId .target).code + if branch then 1 else 0⟩
/-- Relabel the target carrier in the two-carrier POS-04 domain. Source
identity is preserved; branch identity is generated from the target index. -/
def forkRelabel (branch : Bool) (id : CarrierId) : CarrierId :=
  if id = tagCarrierId .target then forkCarrierId branch else id
def forkResourceOwner (branch : Bool) : CarrierId :=
  forkRelabel branch (tagCarrierId (resourceOwner .target))

theorem fork_relabel_source (branch : Bool) :
    forkRelabel branch (tagCarrierId .source) = tagCarrierId .source := by
  cases branch <;> decide
theorem fork_relabel_target (branch : Bool) :
    forkRelabel branch (tagCarrierId .target) = forkCarrierId branch := by
  cases branch <;> decide
theorem fork_resource_owned (branch : Bool) :
    forkResourceOwner branch = forkCarrierId branch := by
  cases branch <;> decide
theorem fork_relabel_distinct (branch : Bool) :
    forkRelabel branch (tagCarrierId .source) ≠
      forkRelabel branch (tagCarrierId .target) := by
  cases branch <;> decide

/-- C5, C6 and route ownership are relative target labels in POS-04. The
same carrier relabeling interprets each target-owned primitive on its branch.
External provenance remains outside the two-carrier domain. -/
def forkProtocolOwner (branch : Bool) (id : ProtocolId) :
    Option CarrierId :=
  match c5Owner .positive .target id with
  | .source => some (forkRelabel branch (tagCarrierId .source))
  | .target => some (forkRelabel branch (tagCarrierId .target))
  | .external | .none => none
def forkC6Owner (branch : Bool) : CarrierId :=
  forkRelabel branch (tagCarrierId (resourceOwner .target))
def forkRouteOwner (branch : Bool) : CarrierId :=
  forkRelabel branch (tagCarrierId routeReadoutOwner)
theorem fork_clause_owners_transport (branch : Bool) :
    forkProtocolOwner branch .clockwise = some (forkCarrierId branch) ∧
    forkC6Owner branch = forkCarrierId branch ∧
    forkRouteOwner branch = forkCarrierId branch := by
  cases branch <;> decide

def forkActionRow (_branch : Bool) (s : KState) (a : Action) :
    List (Ambient × Nat) := actionRow .target s a
theorem fork_action_row_transport (branch : Bool) (s : KState)
    (a : Action) :
    forkActionRow branch s a = actionRow .target s a := rfl

/-- Branch-owned availability applies the same funded ledger rule after
relabeling the resource owner. No stored validity bit is consulted. -/
def forkAvailable (branch : Bool) : Bool :=
  c8Recharge .funded .target &&
    decide (ledger.initialBudget ≥ ledger.actionCost) &&
    decide (ledger.initialBudget - ledger.actionCost +
      ledger.rechargePerAction > 0) &&
    decide (forkResourceOwner branch = forkCarrierId branch)
theorem fork_available_transport (branch : Bool) :
    forkAvailable branch = c8Available .funded .target := by
  cases branch <;> decide

def forkRetain (branch : Bool) (candidate : List KState)
    (s : KState) : Bool :=
  forkAvailable branch &&
    actions.any (fun a => c8RowClosed .target s a candidate)
def forkPrune (branch : Bool) (candidate : List KState) : List KState :=
  candidate.filter (forkRetain branch candidate)
def forkIterate (branch : Bool) : Nat → List KState
  | 0 => kernel
  | n+1 => forkPrune branch (forkIterate branch n)
def forkGreatest (branch : Bool) : List KState :=
  forkIterate branch kernel.length

theorem fork_retain_transport (branch : Bool)
    (candidate : List KState) (s : KState) :
    forkRetain branch candidate s = c8Retain .funded .target candidate s := by
  simp [forkRetain,c8Retain,fork_available_transport]
theorem fork_iterate_transport (branch : Bool) (n : Nat) :
    forkIterate branch n = c8Iterate .funded .target n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [forkIterate,c8Iterate,forkPrune,c8Prune,ih]
      congr 1
      funext s
      exact fork_retain_transport branch _ s
theorem fork_greatest_transport (branch : Bool) :
    forkGreatest branch = c8Greatest .funded .target :=
  fork_iterate_transport branch kernel.length

/-- With source absent, the branch remains available because its relabeled
resource belongs to that branch, and the branch is distinct from the source. -/
def forkAvailableAfterWithdrawal (branch : Bool) : Bool :=
  forkAvailable branch &&
    (if forkCarrierId branch = tagCarrierId .source then
      c8WithdrawnReceiver.sourcePresent else true)
theorem fork_available_after_withdrawal_transport (branch : Bool) :
    forkAvailableAfterWithdrawal branch =
      c8AvailableWithReceiver c8WithdrawnReceiver .funded .target := by
  cases branch <;> decide
def forkReceiverRetain (branch : Bool) (candidate : List KState)
    (s : KState) : Bool :=
  forkAvailableAfterWithdrawal branch &&
    actions.any (fun a => c8RowClosed .target s a candidate)
def forkReceiverPrune (branch : Bool) (candidate : List KState) :
    List KState :=
  candidate.filter (forkReceiverRetain branch candidate)
def forkReceiverIterate (branch : Bool) : Nat → List KState
  | 0 => kernel
  | n+1 => forkReceiverPrune branch (forkReceiverIterate branch n)
def forkReceiverGreatest (branch : Bool) : List KState :=
  forkReceiverIterate branch kernel.length
theorem fork_receiver_retain_transport (branch : Bool)
    (candidate : List KState) (s : KState) :
    forkReceiverRetain branch candidate s =
      c8ReceiverRetain c8WithdrawnReceiver .funded .target candidate s := by
  simp [forkReceiverRetain,c8ReceiverRetain,
    fork_available_after_withdrawal_transport]
theorem fork_receiver_iterate_transport (branch : Bool) (n : Nat) :
    forkReceiverIterate branch n =
      c8ReceiverIterate c8WithdrawnReceiver .funded .target n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [forkReceiverIterate,c8ReceiverIterate,forkReceiverPrune,
        c8ReceiverPrune,ih]
      congr 1
      funext s
      exact fork_receiver_retain_transport branch _ s
theorem fork_receiver_greatest_transport (branch : Bool) :
    forkReceiverGreatest branch =
      c8ReceiverGreatest c8WithdrawnReceiver .funded .target :=
  fork_receiver_iterate_transport branch kernel.length

def ForkAutonomyPass (branch : Bool) : Prop :=
  c8WithdrawnReceiver.sourcePresent = false ∧
  forkResourceOwner branch = forkCarrierId branch ∧
  forkAvailableAfterWithdrawal branch = true ∧
  forkReceiverGreatest branch ≠ []

theorem fork_autonomy_transport (branch : Bool) :
    ForkAutonomyPass branch := by
  refine ⟨target_only_autonomy_positive.1,
    fork_resource_owned branch, ?_, ?_⟩
  · rw [fork_available_after_withdrawal_transport]
    exact target_only_autonomy_positive.2.1.2.1
  · rw [fork_receiver_greatest_transport]
    exact target_only_autonomy_positive.2.2

/-- C1-C7 and all 160 coordinates are invariant under carrier-ID relabeling.
C8 is rerun from branch-owned resources and the same canonical action rows. -/
def ForkPackagePass (branch : Bool) : Prop :=
  CoordinatesComplete ∧ C1FactorPass .target ∧
  C2Pass .position .target ∧ C3Pass .positive .position .target ∧
  C4Surrogate .positive .target ∧ C5Surrogate .positive .target ∧
  C6Pass .positive .target ∧ C7Pass .positive .target ∧
  forkProtocolOwner branch .clockwise = some (forkCarrierId branch) ∧
  forkC6Owner branch = forkCarrierId branch ∧
  forkRouteOwner branch = forkCarrierId branch ∧
  forkResourceOwner branch = forkCarrierId branch ∧
  forkAvailable branch = true ∧ forkGreatest branch ≠ [] ∧
  C8LedgerHolds .funded .target ∧
  ∀ s t : KState,
    rowWeight (forkActionRow branch s (canonicalAction s)) t =
      taggedPNum .target s t

theorem fork_package_each_branch (branch : Bool) :
    ForkPackagePass branch := by
  have hp := package_funded_each_tag .target
  rcases hp with ⟨hcoords,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8⟩
  have howners := fork_clause_owners_transport branch
  refine ⟨hcoords,hc1,hc2,hc3,hc4,hc5,hc6,hc7,
    howners.1,howners.2.1,howners.2.2,
    fork_resource_owned branch, ?_, ?_, hc8.2.2.1, ?_⟩
  · rw [fork_available_transport]
    exact hc8.2.1
  · rw [fork_greatest_transport]
    exact hc8.1
  · intro s t
    rw [fork_action_row_transport]
    exact canonical_action_row_agrees_with_tagged_P .target s t
def forkRelated (source : KState) (target : ForkTarget) : Prop :=
  receiverOutput .positive .positive .repA = some source ∧
    (source,target) ∈ forkEdges
def forkValid (target : ForkTarget) : Prop :=
  ForkPackagePass target.branch ∧
  ForkAutonomyPass target.branch ∧
  target.endpoint ∈ forkGreatest target.branch ∧
  CorridorPass .positive ∧
  BridgePass .positive .positive ∧
  forkCarrierId target.branch ≠ tagCarrierId .source ∧
  target.endpoint = .p1w0
def forkSwap (target : ForkTarget) : ForkTarget :=
  { target with branch := !target.branch }

def realFission : CSTTT.CorridorTheory.TemporalFissionData
    KState ForkTarget :=
  { source := .p1w0, left := forkLeft, right := forkRight,
    related := forkRelated, valid := forkValid, swap := forkSwap }

theorem ttn11_symmetric_fork_certificate :
    CSTTT.CorridorTheory.TemporalFissionCertificate realFission := by
  refine ⟨by decide,
    by
      simp [realFission,forkRelated,forkEdges,forkLeft,forkCopy]
      decide,
    by
      simp [realFission,forkRelated,forkEdges,forkRight,forkCopy]
      decide,
    ?_, ?_, by decide, by decide⟩
  · exact ⟨fork_package_each_branch false,
      fork_autonomy_transport false,
      by change KState.p1w0 ∈ forkGreatest false
         simp [fork_greatest_transport,c8_funded_greatest_is_kernel,kernel],
      corridor_positive,bridge_positive,by decide,rfl⟩
  · exact ⟨fork_package_each_branch true,
      fork_autonomy_transport true,
      by change KState.p1w0 ∈ forkGreatest true
         simp [fork_greatest_transport,c8_funded_greatest_is_kernel,kernel],
      corridor_positive,bridge_positive,by decide,rfl⟩

theorem fork_target_carriers_distinct :
    forkCarrierId false ≠ forkCarrierId true := by decide

theorem ttn11_no_invariant_unique_selector :
    (∀ t : ForkTarget, forkRelated .p1w0 t →
      forkValid t → forkValid (forkSwap t)) ∧
    ¬ ∃ selected : ForkTarget,
      forkRelated .p1w0 selected ∧ forkValid selected ∧
      forkSwap selected = selected := by
  constructor
  · intro t hrelated hvalid
    simp [forkRelated,forkEdges] at hrelated
    rcases hrelated.2 with hleft | hright
    · subst t; simpa [forkSwap,forkLeft,forkRight] using
        ttn11_symmetric_fork_certificate.rightValid
    · subst t; simpa [forkSwap,forkLeft,forkRight] using
        ttn11_symmetric_fork_certificate.leftValid
  · rintro ⟨selected,_,_,hfixed⟩
    have hb := congrArg ForkTarget.branch hfixed
    cases selected.branch <;> simp [forkSwap] at hb

theorem ttn11_exists :
    ∃ d : CSTTT.CorridorTheory.TemporalFissionData KState ForkTarget,
      CSTTT.CorridorTheory.TemporalFissionCertificate d ∧
      forkCarrierId false ≠ forkCarrierId true ∧
      (∀ t : ForkTarget, d.related d.source t →
        d.valid t → d.valid (d.swap t)) ∧
      ¬ ∃ selected : ForkTarget,
        d.related d.source selected ∧ d.valid selected ∧
        d.swap selected = selected := by
  exact ⟨realFission,ttn11_symmetric_fork_certificate,
    fork_target_carriers_distinct,ttn11_no_invariant_unique_selector.1,
    ttn11_no_invariant_unique_selector.2⟩

/-! TTN-10. CM-10's rejected vector has nine zero defects followed by one
unit defect at its declared hard gate, index nine. The accepted comparator
keeps the same ten gate types and tolerances and moves that one unit of
defect to the first soft component. Its tolerance is the declared one-unit
soft allowance, matching the single defect unit in CM-10; this rule is fixed
before computing either verdict. No stored acceptance bit is read. The
scalar test is CM-10's exact `10 * sum ≤ count` one-tenth threshold. -/
def softZero : CSTTT.DefectTheory.DefectComponent := ⟨false,0,0⟩
def allowedSoftZero : CSTTT.DefectTheory.DefectComponent := ⟨false,0,1⟩
def allowedSoftOne : CSTTT.DefectTheory.DefectComponent := ⟨false,1,1⟩
def hardZero : CSTTT.DefectTheory.DefectComponent := ⟨true,0,0⟩
def hardOne : CSTTT.DefectTheory.DefectComponent := ⟨true,1,0⟩
def scalarHardVector : CSTTT.DefectTheory.DefectVector :=
  [allowedSoftZero] ++ List.replicate 8 softZero ++ [hardOne]
/-- Move the one defect unit from the declared failed hard gate (index 9)
to the least-index soft gate with one-unit allowance (index 0). The gate
schema and total defect are untouched. -/
def scalarAcceptedVector : CSTTT.DefectTheory.DefectVector :=
  (scalarHardVector.set 0 allowedSoftOne).set 9 hardZero
theorem scalar_accepted_shape :
    scalarAcceptedVector =
      [allowedSoftOne] ++ List.replicate 8 softZero ++ [hardZero] := by
  decide
def scalarSmall (v : CSTTT.DefectTheory.DefectVector) : Prop :=
  10 * (v.map (·.defect)).sum ≤ v.length

theorem ttn10_small_scalar_hard_failure :
    scalarHardVector.length = 10 ∧
    (scalarHardVector.map (·.defect)).sum = 1 ∧
    scalarSmall scalarHardVector ∧
    ¬ CSTTT.DefectTheory.VectorAccepts scalarHardVector := by
  refine ⟨by decide,by decide,by simp [scalarSmall,scalarHardVector,
    allowedSoftZero,softZero,hardOne],?_⟩
  intro h
  have hc := h hardOne (by decide)
  simp [CSTTT.DefectTheory.ComponentAccepts,hardOne] at hc

/-- The gate schema is identical in both profiles. Scalar equality therefore
cannot determine the componentwise acceptance result. -/
theorem ttn10_equal_scalar_different_acceptance :
    scalarAcceptedVector.length = scalarHardVector.length ∧
    (scalarAcceptedVector.map (·.defect)).sum =
      (scalarHardVector.map (·.defect)).sum ∧
    scalarSmall scalarAcceptedVector ∧
    (scalarAcceptedVector.map (fun c => (c.hard,c.tolerance))) =
      (scalarHardVector.map (fun c => (c.hard,c.tolerance))) ∧
    CSTTT.DefectTheory.VectorAccepts scalarAcceptedVector ∧
    ¬ CSTTT.DefectTheory.VectorAccepts scalarHardVector := by
  rw [scalar_accepted_shape]
  refine ⟨by decide,by decide,
    by simp [scalarSmall,allowedSoftOne,softZero,hardZero],
    by decide,?_,
    ttn10_small_scalar_hard_failure.2.2.2⟩
  intro c hc
  simp [allowedSoftOne,softZero,hardZero] at hc
  rcases hc with rfl | rfl | rfl
  all_goals simp [CSTTT.DefectTheory.ComponentAccepts]

theorem ttn10_exists :
    ∃ v : CSTTT.DefectTheory.DefectVector,
      v.length = 10 ∧ (v.map (·.defect)).sum = 1 ∧
      scalarSmall v ∧ ¬ CSTTT.DefectTheory.VectorAccepts v :=
  ⟨scalarHardVector,ttn10_small_scalar_hard_failure⟩

theorem ttn10_equal_scalar_exists :
    ∃ accepted rejected : CSTTT.DefectTheory.DefectVector,
      accepted.length = rejected.length ∧
      (accepted.map (·.defect)).sum = (rejected.map (·.defect)).sum ∧
      scalarSmall accepted ∧ scalarSmall rejected ∧
      (accepted.map (fun c => (c.hard,c.tolerance))) =
        (rejected.map (fun c => (c.hard,c.tolerance))) ∧
      CSTTT.DefectTheory.VectorAccepts accepted ∧
      ¬ CSTTT.DefectTheory.VectorAccepts rejected := by
  exact ⟨scalarAcceptedVector,scalarHardVector,
    ttn10_equal_scalar_different_acceptance.1,
    ttn10_equal_scalar_different_acceptance.2.1,
    ttn10_equal_scalar_different_acceptance.2.2.1,
    ttn10_small_scalar_hard_failure.2.2.1,
    ttn10_equal_scalar_different_acceptance.2.2.2.1,
    ttn10_equal_scalar_different_acceptance.2.2.2.2.1,
    ttn10_equal_scalar_different_acceptance.2.2.2.2.2⟩

/-! TTN-12. CM-13's budget trace 2,1,0 is the h=1 member of this
arbitrary-horizon finite family. State space is `Fin (h+2)`, the raw
transition decrements positive budget and fixes zero, and liveness means
positive budget. No stored finite-success or liveness verdict is used. -/
def countdownStep (h : Nat) (b : Fin (h+2)) : Fin (h+2) :=
  ⟨b.val - 1, by omega⟩
def countdownAt (h t : Nat) : Fin (h+2) :=
  ⟨h+1-t, by omega⟩
def countdownLive (h : Nat) (b : Fin (h+2)) : Prop := 0 < b.val

theorem countdown_follows_step (h t : Nat) :
    countdownStep h (countdownAt h t) = countdownAt h (t+1) := by
  apply Fin.ext
  simp [countdownStep,countdownAt]
  omega

theorem ttn12_arbitrary_finite_prefix (h : Nat) :
    (∀ t, t ≤ h → countdownLive h (countdownAt h t)) ∧
    (∀ t, t ≤ h → countdownStep h (countdownAt h t) =
      countdownAt h (t+1)) ∧
    ¬ countdownLive h (countdownAt h (h+1)) := by
  refine ⟨?_,?_,?_⟩
  · intro t ht; simp [countdownLive,countdownAt]; omega
  · intro t _; exact countdown_follows_step h t
  · simp [countdownLive,countdownAt]

theorem ttn12_exists_for_every_horizon (h : Nat) :
    ∃ step : Fin (h+2) → Fin (h+2),
      (∀ t, t ≤ h → countdownLive h (countdownAt h t)) ∧
      (∀ t, t ≤ h → step (countdownAt h t) =
        countdownAt h (t+1)) ∧
      ¬ countdownLive h (countdownAt h (h+1)) :=
  ⟨countdownStep h,ttn12_arbitrary_finite_prefix h⟩

end CSTTT.RealControls
