import CSTTT.Fallback.ReceiptAncestry
import CSTTT.Prospects.Statements

namespace CSTTT.FallbackTheory.BranchSymmetryPrototype
open CSTTT.TransportTheory
open CSTTT.FallbackTheory.OperationalTrace
variable {Source Target : Type}
-- Class (b): exchange the two declared branch addresses, without choosing an identity.
def swapPair [DecidableEq Target] (left right : Target) (target : Target) : Target :=
  if target=left then right else if target=right then left else target
def PairInvariant (identity : Source → Target → Prop) (source : Source) (left right : Target) : Prop :=
  identity source left ↔ identity source right
def AtMostOne (identity : Source → Target → Prop) (source : Source) : Prop :=
  ∀ left right,identity source left → identity source right → left=right
-- Direct refutation of the original arbitrary-identity schema, not a failed sufficient check.
theorem total_identity_refutes_original (ancestry : Source → Target → Prop) (swap : Target → Target) :
    ¬ CSTTT.Prospects.AncestryNoUniqueIdentity Source Target ancestry (fun _ _ => True) swap := by
  rintro ⟨_,_,_,_,_,negative⟩
  exact negative True.intro
theorem swap_left [DecidableEq Target] (left right : Target) : swapPair left right left=right := by
  simp [swapPair]
theorem swap_right [DecidableEq Target] (left right : Target) (distinct : left≠right) :
    swapPair left right right=left := by
  simp [swapPair,Ne.symm distinct]
theorem swap_involution [DecidableEq Target] (left right target : Target) (distinct : left≠right) :
    swapPair left right (swapPair left right target)=target := by
  by_cases hl : target=left
  · subst target; simp [swapPair,Ne.symm distinct]
  · by_cases hr : target=right
    · subst target; simp [swapPair,Ne.symm distinct]
    · simp [swapPair,hl,hr]
theorem invariant_at_most_one_excludes_both (identity : Source → Target → Prop)
    (source : Source) (left right : Target) (distinct : left≠right)
    (invariant : PairInvariant identity source left right) (unique : AtMostOne identity source) :
    ¬identity source left ∧ ¬identity source right := by
  constructor
  · intro h; exact distinct (unique left right h (invariant.mp h))
  · intro h; exact distinct (unique left right (invariant.mpr h) h)
-- Return to the unchanged schema with the additional identity premises visible.
theorem original_schema_from_invariant_pair [DecidableEq Target] (ancestry identity : Source → Target → Prop)
    (source : Source) (left right : Target) (leftRelated : ancestry source left)
    (rightRelated : ancestry source right) (distinct : left≠right)
    (invariant : PairInvariant identity source left right) (unique : AtMostOne identity source) :
    CSTTT.Prospects.AncestryNoUniqueIdentity Source Target ancestry identity (swapPair left right) := by
  refine ⟨source,left,leftRelated,?_,?_,(invariant_at_most_one_excludes_both identity source left right distinct invariant unique).1⟩
  · simpa only [swap_left] using rightRelated
  · rw [swap_left]; exact Ne.symm distinct
-- An address-dependent choice remains possible when invariance is not required.
theorem address_choice_unique (left right : Target) (distinct : left≠right) :
    (∃ selected, (selected=left ∨ selected=right) ∧
      (∀ other, (other=left ∨ other=right) → other=left → other=selected)) ∧
    ¬ ((left=left) ↔ (right=left)) := by
  refine ⟨⟨left,Or.inl rfl,fun _ _ h => h⟩,?_⟩
  intro invariant; exact distinct (invariant.mp rfl).symm
-- Obstruct every invariant unique branch, rather than excluding only one proposed identity.
theorem no_invariant_unique_branch (identity : Source → Target → Prop)
    (source : Source) (left right : Target) (distinct : left≠right)
    (invariant : PairInvariant identity source left right) (unique : AtMostOne identity source) :
    ¬ ∃ selected, (selected=left ∨ selected=right) ∧ identity source selected := by
  obtain ⟨nl,nr⟩ := invariant_at_most_one_excludes_both identity source left right distinct invariant unique
  rintro ⟨selected,branches,chosen⟩
  rcases branches with rfl|rfl
  · exact nl chosen
  · exact nr chosen
-- Identity descent is a declared admissibility law, not a derived identity verdict.
def ObservationDescent {Obs : Type} (observe : Source → Target → Obs) (identity : Source → Target → Prop) : Prop :=
  ∀ source left right,observe source left=observe source right → (identity source left ↔ identity source right)
-- Compute the actual local branch observation from scientific ancestry and actual typed/active readouts.
def receiptObservation {N H S T E R SC TC RR M : Type} [DecidableEq N] [DecidableEq S] [DecidableEq T]
    (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : SharedOperationalSeed.RawInputs S T) (receipts : List (ReceiptAncestry.Receipt S T))
    (receipt : ReceiptAncestry.Receipt S T) (source target : N) : Bool × Option (Content S T) × Bool :=
  (ReceiptAncestry.ancestryBit nodes address b inputs receipts (source,target),
    receipt.after.read (address target),receipt.after.active (address target))
-- Checked fission derives distinct actual addresses and equal local scientific observations.
theorem actual_fission_equal_observations {N H S T E R SC TC RR M : Type} [DecidableEq N] [DecidableEq S] [DecidableEq T]
    (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : SharedOperationalSeed.RawInputs S T) (commands : List (NativeDescendant.Command T))
    (store finished : Store S T) (receipts : List (ReceiptAncestry.Receipt S T)) (receipt : ReceiptAncestry.Receipt S T)
    (source parent left right : N) (executed : ReceiptAncestry.recordedRun b store commands=some (finished,receipts))
    (member : receipt∈receipts) (command : receipt.command=.fission (address parent) (address left) (address right))
    (previous : ReceiptAncestry.ancestryBit nodes address b inputs receipts (source,parent)=true) :
    left≠right ∧ ReceiptAncestry.ancestryBit nodes address b inputs receipts (source,left)=true ∧
      ReceiptAncestry.ancestryBit nodes address b inputs receipts (source,right)=true ∧
      receiptObservation nodes address b inputs receipts receipt source left=
        receiptObservation nodes address b inputs receipts receipt source right := by
  have checked := ReceiptAncestry.every_receipt_checked b commands store finished receipts executed receipt member
  have shape := ReceiptAncestry.checked_receipt_shape b receipt checked
  rw [command] at shape
  obtain ⟨_,_,_,_,_,addressesDistinct,_⟩ := shape
  have distinct : left≠right := fun h => addressesDistinct (congrArg address h)
  obtain ⟨hl,hr,contents,al,ar⟩ := ReceiptAncestry.actual_receipt_fission nodes address b inputs commands store finished receipts receipt
    source parent left right executed member command previous
  refine ⟨distinct,hl,hr,?_⟩
  simp only [receiptObservation,hl,hr,contents,al,ar]
-- No unique observation-derived identity can hold at either actual fission branch.
theorem actual_fission_no_observation_identity {N H S T E R SC TC RR M : Type} [DecidableEq N] [DecidableEq S] [DecidableEq T]
    (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : SharedOperationalSeed.RawInputs S T) (commands : List (NativeDescendant.Command T))
    (store finished : Store S T) (receipts : List (ReceiptAncestry.Receipt S T)) (receipt : ReceiptAncestry.Receipt S T)
    (source parent left right : N) (executed : ReceiptAncestry.recordedRun b store commands=some (finished,receipts))
    (member : receipt∈receipts) (command : receipt.command=.fission (address parent) (address left) (address right))
    (previous : ReceiptAncestry.ancestryBit nodes address b inputs receipts (source,parent)=true)
    (identity : N → N → Prop)
    (descends : ObservationDescent (receiptObservation nodes address b inputs receipts receipt) identity)
    (unique : AtMostOne identity source) :
    ¬identity source left ∧ ¬identity source right ∧
      ¬ ∃ selected,(selected=left ∨ selected=right) ∧ identity source selected := by
  obtain ⟨distinct,_,_,observations⟩ := actual_fission_equal_observations nodes address b inputs commands store finished receipts receipt
    source parent left right executed member command previous
  have invariant := descends source left right observations
  obtain ⟨nl,nr⟩ := invariant_at_most_one_excludes_both identity source left right distinct invariant unique
  exact ⟨nl,nr,no_invariant_unique_branch identity source left right distinct invariant unique⟩
-- Original identity schema returns on the actual executable scientific relation.
theorem actual_fission_original_identity_return {N H S T E R SC TC RR M : Type} [DecidableEq N] [DecidableEq S] [DecidableEq T]
    (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : SharedOperationalSeed.RawInputs S T) (commands : List (NativeDescendant.Command T))
    (store finished : Store S T) (receipts : List (ReceiptAncestry.Receipt S T)) (receipt : ReceiptAncestry.Receipt S T)
    (source parent left right : N) (executed : ReceiptAncestry.recordedRun b store commands=some (finished,receipts))
    (member : receipt∈receipts) (command : receipt.command=.fission (address parent) (address left) (address right))
    (previous : ReceiptAncestry.ancestryBit nodes address b inputs receipts (source,parent)=true)
    (identity : N → N → Prop)
    (descends : ObservationDescent (receiptObservation nodes address b inputs receipts receipt) identity)
    (unique : AtMostOne identity source) :
    CSTTT.Prospects.AncestryNoUniqueIdentity N N
      (fun root target => ReceiptAncestry.ancestryBit nodes address b inputs receipts (root,target)=true)
      identity (swapPair left right) := by
  obtain ⟨distinct,hl,hr,observations⟩ := actual_fission_equal_observations nodes address b inputs commands store finished receipts receipt
    source parent left right executed member command previous
  exact original_schema_from_invariant_pair _ identity source left right hl hr distinct
    (descends source left right observations) unique

-- Class (b): the campaign observation is optional and constructed only from actual recording.
def actualObservation {H S T E R SC TC RR M : Type} [DecidableEq S]
    (b : RawBridge H S T E R SC TC RR M) (inputs : SharedOperationalSeed.RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat) :
    Option (Bool × Option (Content S T) × Bool) :=
  (ReceiptAncestry.actualRecorded b inputs commands).map (fun result =>
    (ReceiptAncestry.finishedBit b inputs result source target,
      result.1.read target,result.1.active target))
-- Class (b): every partial assignment rejects the observation exactly when execution is unavailable.
theorem actual_observation_none_iff {H S T E R SC TC RR M : Type} [DecidableEq S]
    (b : RawBridge H S T E R SC TC RR M) (inputs : SharedOperationalSeed.RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat) :
    actualObservation b inputs commands source target=none ↔
      ReceiptAncestry.actualRecorded b inputs commands=none := by
  simp [actualObservation]
-- Class (b): recover the unique actual before/after receipt from a successful one-command campaign.
theorem single_recorded_shape {H S T E R SC TC RR M : Type} [DecidableEq S]
    (b : RawBridge H S T E R SC TC RR M) (inputs : SharedOperationalSeed.RawInputs S T)
    (command : NativeDescendant.Command T) (finished : Store S T) (receipts : List (ReceiptAncestry.Receipt S T))
    (available : ReceiptAncestry.actualRecorded b inputs [command]=some (finished,receipts)) :
    ∃ origin,SharedOperationalSeed.computedStore inputs=some origin ∧
      NativeDescendant.step b origin command=some finished ∧
      receipts=[⟨origin,command,finished⟩] := by
  cases computed : SharedOperationalSeed.computedStore inputs with
  | none => simp [ReceiptAncestry.actualRecorded,computed] at available
  | some origin =>
    have executed : ReceiptAncestry.recordedRun b origin [command]=some (finished,receipts) := by
      simpa [ReceiptAncestry.actualRecorded,computed] using available
    cases first : NativeDescendant.step b origin command with
    | none => simp [ReceiptAncestry.recordedRun,first] at executed
    | some next =>
      have equal : (next,[⟨origin,command,next⟩])=(finished,receipts) := by
        simpa [ReceiptAncestry.recordedRun,first] using executed
      cases equal
      exact ⟨origin,rfl,first,rfl⟩
-- Class (b): the actual source-coupled single fission propagates a real Seed to both branches.
theorem single_fission_actual_branches {H S T E R SC TC RR M : Type} [DecidableEq S]
    (b : RawBridge H S T E R SC TC RR M) (inputs : SharedOperationalSeed.RawInputs S T)
    (source parent left right : Nat) (finished : Store S T) (receipts : List (ReceiptAncestry.Receipt S T))
    (available : ReceiptAncestry.actualRecorded b inputs [.fission parent left right]=some (finished,receipts))
    (seed : SharedOperationalSeed.Seed b inputs source parent) :
    left≠right ∧ ReceiptAncestry.actualAncestry b inputs [.fission parent left right] source left=some true ∧
      ReceiptAncestry.actualAncestry b inputs [.fission parent left right] source right=some true ∧
      finished.read left=finished.read right ∧ finished.active left=true ∧ finished.active right=true := by
  obtain ⟨origin,computed,checked,ledger⟩ := single_recorded_shape b inputs (.fission parent left right) finished receipts available
  have shape := ReceiptAncestry.checked_receipt_shape b (⟨origin,.fission parent left right,finished⟩ : ReceiptAncestry.Receipt S T) checked
  obtain ⟨payload,_,_,_,_,distinct,after⟩ := shape
  change finished=NativeDescendant.split origin parent left right payload at after
  have executed : ReceiptAncestry.recordedRun b origin [.fission parent left right]=some (finished,receipts) := by
    simpa [ReceiptAncestry.actualRecorded,computed] using available
  have ancestry (target : Nat) (member : (parent,target)∈ReceiptAncestry.ledgerEdges receipts) :
      ReceiptAncestry.actualAncestry b inputs [.fission parent left right] source target=some true := by
    apply (ReceiptAncestry.actual_ancestry_exact b inputs [.fission parent left right] source target).mpr
    exact ⟨origin,finished,receipts,computed,executed,parent,seed,Or.inr (.one member)⟩
  have hl := ancestry left (by simp [ledger,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges])
  have hr := ancestry right (by simp [ledger,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges])
  have contents := NativeDescendant.fission_equal_readouts origin parent left right payload distinct
  refine ⟨distinct,hl,hr,?_,?_,?_⟩
  · rw [after]; exact contents.1.trans contents.2.1.symm
  · rw [after]; exact contents.2.2.1
  · rw [after]; exact contents.2.2.2.1
-- Class (b): equality of actual optional campaign observations is derived from the accepted source-coupled run.
theorem single_fission_actual_observation_equal {H S T E R SC TC RR M : Type} [DecidableEq S]
    (b : RawBridge H S T E R SC TC RR M) (inputs : SharedOperationalSeed.RawInputs S T)
    (source parent left right : Nat) (finished : Store S T) (receipts : List (ReceiptAncestry.Receipt S T))
    (available : ReceiptAncestry.actualRecorded b inputs [.fission parent left right]=some (finished,receipts))
    (seed : SharedOperationalSeed.Seed b inputs source parent) :
    actualObservation b inputs [.fission parent left right] source left=
      actualObservation b inputs [.fission parent left right] source right := by
  obtain ⟨_,hl,hr,reads,al,ar⟩ := single_fission_actual_branches b inputs source parent left right finished receipts available seed
  have bl : ReceiptAncestry.finishedBit b inputs (finished,receipts) source left=true := by
    simpa [ReceiptAncestry.actualAncestry,available] using hl
  have br : ReceiptAncestry.finishedBit b inputs (finished,receipts) source right=true := by
    simpa [ReceiptAncestry.actualAncestry,available] using hr
  simp only [actualObservation,available,Option.map_some,bl,br,reads,al,ar]
-- Class (b): no unique observation-derived identity on actual campaign fission, with exact original-schema return.
theorem single_fission_actual_identity_return {H S T E R SC TC RR M : Type} [DecidableEq S]
    (b : RawBridge H S T E R SC TC RR M) (inputs : SharedOperationalSeed.RawInputs S T)
    (source parent left right : Nat) (finished : Store S T) (receipts : List (ReceiptAncestry.Receipt S T))
    (available : ReceiptAncestry.actualRecorded b inputs [.fission parent left right]=some (finished,receipts))
    (seed : SharedOperationalSeed.Seed b inputs source parent) (identity : Nat → Nat → Prop)
    (descends : ObservationDescent (actualObservation b inputs [.fission parent left right]) identity)
    (unique : AtMostOne identity source) :
    (¬identity source left ∧ ¬identity source right) ∧
      (¬ ∃ selected,(selected=left ∨ selected=right) ∧ identity source selected) ∧
      CSTTT.Prospects.AncestryNoUniqueIdentity Nat Nat
        (fun root target => ReceiptAncestry.actualAncestry b inputs [.fission parent left right] root target=some true)
        identity (swapPair left right) := by
  obtain ⟨distinct,hl,hr,_,_,_⟩ := single_fission_actual_branches b inputs source parent left right finished receipts available seed
  have invariant := descends source left right
    (single_fission_actual_observation_equal b inputs source parent left right finished receipts available seed)
  exact ⟨invariant_at_most_one_excludes_both identity source left right distinct invariant unique,
    no_invariant_unique_branch identity source left right distinct invariant unique,
    original_schema_from_invariant_pair _ identity source left right hl hr distinct invariant unique⟩

-- Class (b): complete positive observation iff on every partial assignment.
theorem actual_observation_some_iff {H S T E R SC TC RR M : Type} [DecidableEq S]
    (b : RawBridge H S T E R SC TC RR M) (inputs : SharedOperationalSeed.RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat)
    (observation : Bool × Option (Content S T) × Bool) :
    actualObservation b inputs commands source target=some observation ↔
      ∃ result,ReceiptAncestry.actualRecorded b inputs commands=some result ∧
        (ReceiptAncestry.finishedBit b inputs result source target,result.1.read target,result.1.active target)=observation := by
  cases read : ReceiptAncestry.actualRecorded b inputs commands with
  | none => simp [actualObservation,read]
  | some result => simp [actualObservation,read]
-- Class (b): an observed ancestry truth is exactly the scientific ancestry truth, including missing cases.
theorem actual_observation_true_iff {H S T E R SC TC RR M : Type} [DecidableEq S]
    (b : RawBridge H S T E R SC TC RR M) (inputs : SharedOperationalSeed.RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat) :
    (∃ contents active,actualObservation b inputs commands source target=some (true,contents,active)) ↔
      ReceiptAncestry.actualAncestry b inputs commands source target=some true := by
  cases read : ReceiptAncestry.actualRecorded b inputs commands with
  | none => simp [actualObservation,ReceiptAncestry.actualAncestry,read]
  | some result => simp [actualObservation,ReceiptAncestry.actualAncestry,read]
-- Class (b): observed negative ancestry is an available false, never a missing-input default.
theorem actual_observation_false_iff {H S T E R SC TC RR M : Type} [DecidableEq S]
    (b : RawBridge H S T E R SC TC RR M) (inputs : SharedOperationalSeed.RawInputs S T)
    (commands : List (NativeDescendant.Command T)) (source target : Nat) :
    (∃ contents active,actualObservation b inputs commands source target=some (false,contents,active)) ↔
      ReceiptAncestry.actualAncestry b inputs commands source target=some false := by
  cases read : ReceiptAncestry.actualRecorded b inputs commands with
  | none => simp [actualObservation,ReceiptAncestry.actualAncestry,read]
  | some result => simp [actualObservation,ReceiptAncestry.actualAncestry,read]
end CSTTT.FallbackTheory.BranchSymmetryPrototype
