import CSTTT.POS04.Corridor

/-! POS-04 receiver and content tests, frozen `audit/M3_model_spec.md:31,44`.
The positive operation copies terminal raw position and phase. Consequently
class preservation is close to automatic once T1 tag isomorphism is checked;
the fixed-activation preloaded-copy control is the substantive separator.
No intended endpoint class is stored or read by this operation. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

inductive ReceiverVariant where
  | positive | sourceAbsent | preloadedCopy | bridgeRep
  deriving DecidableEq, Repr

inductive PositionRule where | copySourceTerminal | constantOne
  deriving DecidableEq, Repr
inductive PhaseRule where | copySourceTerminal | constantZero
  deriving DecidableEq, Repr

def receiverFor (v : ReceiverVariant) : Receiver :=
  if v = .sourceAbsent then { receiver with sourcePresent := false }
  else receiver

def receiverPositionRule (v : ReceiverVariant) : PositionRule :=
  if v = .preloadedCopy then .constantOne else .copySourceTerminal

def receiverPhaseRule (v : ReceiverVariant) : PhaseRule :=
  if v = .preloadedCopy then .constantZero else .copySourceTerminal

def receiverOverride (v : ReceiverVariant) (id : HistoryId) :
    Option (Nat × Nat) :=
  if v = .bridgeRep && id = .repB then some (1,1) else none

def sourceTerminalRaw (id : HistoryId) : Option (Nat × Nat) :=
  (sourceHistory id).getLast?.map fun s =>
    (ambientPosition (.inK s), ambientPhase (.inK s))

def sourceTerminalM (id : HistoryId) :
    Option (Nat × List (List Bool)) :=
  (sourceHistory id).getLast?.map (rawM .source)

def receiverRaw (v : ReceiverVariant) (id : HistoryId) :
    Option (Nat × Nat) := do
  let (p,w) ← sourceTerminalRaw id
  if let some override := receiverOverride v id then return override
  let targetP := match receiverPositionRule v with
    | .copySourceTerminal => p | .constantOne => 1
  let targetW := match receiverPhaseRule v with
    | .copySourceTerminal => w | .constantZero => 0
  return (targetP,targetW)

/-- Partial decoder: missing T1 factor coordinates never acquire a default
target state. -/
def stateFromRaw : Nat × Nat → Option KState
  | (0,0) => some .p0w0 | (0,1) => some .p0w1
  | (1,0) => some .p1w0 | (1,1) => some .p1w1
  | (2,1) => some .p2w1
  | (3,0) => some .p3w0 | (3,1) => some .p3w1
  | (4,0) => some .p4w0 | (4,1) => some .p4w1
  | (5,0) => some .p5w0
  | _ => none

def receiverFactor (v : ReceiverVariant) (id : HistoryId) : Option KState :=
  (receiverRaw v id).bind stateFromRaw

def receiverActive (v : ReceiverVariant) (cv : CorridorVariant) : Bool :=
  let r := receiverFor v
  r.sourcePresent && r.targetReceiverFunded && r.funded &&
    (!r.mixedEventRequired || corridorMixedCount cv > 0)

def receiverOutput (v : ReceiverVariant) (cv : CorridorVariant)
    (id : HistoryId) : Option KState :=
  if receiverActive v cv &&
      decide (id ∈ bridgeFrontier) && supportedHistory .source id then
    receiverFactor v id
  else none

def ContentSensitivity (v : ReceiverVariant) (cv : CorridorVariant) : Prop :=
  contentCounterfactuals = [.repA,.classB] ∧
  (receiverFor v).latentFactor = receiver.latentFactor ∧
  receiverActive v cv = true ∧
  sourceTerminalM .repA ≠ sourceTerminalM .classB ∧
  ∃ targetA targetB : KState,
    receiverOutput v cv .repA = some targetA ∧
    receiverOutput v cv .classB = some targetB ∧
    rawM .target targetA ≠ rawM .target targetB ∧
    sourceTerminalM .repA = some (rawM .target targetA) ∧
    sourceTerminalM .classB = some (rawM .target targetB)

def RepresentativeIndependence (v : ReceiverVariant) : Prop :=
  sourceHistory .repA ≠ sourceHistory .repB ∧
  (sourceHistory .repA).getLast? = (sourceHistory .repB).getLast? ∧
  (sourceHistory .repA).take 2 ≠ (sourceHistory .repB).take 2 ∧
  supportedHistory .source .repA = true ∧
  supportedHistory .source .repB = true ∧
  sourceTerminalM .repA = sourceTerminalM .repB ∧
  ∃ targetA targetB : KState,
    receiverFactor v .repA = some targetA ∧
    receiverFactor v .repB = some targetB ∧
    rawM .target targetA = rawM .target targetB

theorem receiver_predictive_M_link (tag : Tag) (s t : KState) :
    (rawM tag s = rawM tag t) ↔
      (taggedMClass tag s = taggedMClass tag t) :=
  rawM_iff_imported_M tag s t

theorem receiver_positive_raw_outputs :
    receiverRaw .positive .repA = some (1,0) ∧
    receiverRaw .positive .classB = some (1,1) ∧
    receiverFactor .positive .repA = some .p1w0 ∧
    receiverFactor .positive .classB = some .p1w1 := by decide

theorem receiver_positive_active :
    receiverActive .positive .positive = true := by decide

theorem content_sensitive_positive :
    ContentSensitivity .positive .positive := by
  simp only [ContentSensitivity]
  refine ⟨by decide, by decide, by decide, by decide,
    .p1w0, .p1w1, ?_⟩
  decide

theorem representative_independence_positive :
    RepresentativeIndependence .positive := by
  simp only [RepresentativeIndependence]
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    by decide,
    .p1w0, .p1w0, ?_⟩
  decide

theorem neg_activation_source_absent :
    receiverActive .sourceAbsent .positive = false := by decide

theorem activation_source_presence_sensitivity :
    receiverActive .positive .positive = true ∧
    receiverActive .sourceAbsent .positive = false :=
  ⟨receiver_positive_active, neg_activation_source_absent⟩

theorem source_absent_content_fails :
    ¬ ContentSensitivity .sourceAbsent .positive := by
  intro h
  have ha := h.2.2.1
  rw [neg_activation_source_absent] at ha
  contradiction

theorem neg_preloaded_copy_activation_unchanged :
    receiverFor .preloadedCopy = receiver ∧
    receiverActive .preloadedCopy .positive = true := by decide

theorem neg_preloaded_copy_same_target_class :
    receiverOutput .preloadedCopy .positive .repA = some .p1w0 ∧
    receiverOutput .preloadedCopy .positive .classB = some .p1w0 := by decide

theorem neg_preloaded_copy_content_fails :
    ¬ ContentSensitivity .preloadedCopy .positive := by
  intro h
  rcases h with ⟨_,_,_,_,a,b,ha,hb,hd,_,_⟩
  have hout := neg_preloaded_copy_same_target_class
  rw [hout.1] at ha
  rw [hout.2] at hb
  cases ha
  cases hb
  exact hd rfl

theorem neg_bridge_rep_target_classes_differ :
    receiverFactor .bridgeRep .repA = some .p1w0 ∧
    receiverFactor .bridgeRep .repB = some .p1w1 ∧
    rawM .target .p1w0 ≠ rawM .target .p1w1 := by decide

theorem neg_bridge_rep_independence_fails :
    ¬ RepresentativeIndependence .bridgeRep := by
  intro h
  rcases h with ⟨_,_,_,_,_,_,a,b,ha,hb,heq⟩
  have hout := neg_bridge_rep_target_classes_differ
  rw [hout.1] at ha
  rw [hout.2.1] at hb
  cases ha
  cases hb
  exact hout.2.2 heq

theorem receiver_missing_realized_mixed_event_fails :
    ¬ ContentSensitivity .positive .gap := by
  intro h
  have ha := h.2.2.1
  have hn : receiverActive .positive .gap = false := by decide
  rw [hn] at ha
  contradiction

end CSTTT.POS04
