import CSTTT.POS04.WellFormed

/-! C2 and C3 follow the frozen `audit/M3_model_spec.md:18-19,30-31`.
Readouts and profiles are computed from POS-04's raw action supports. The one
profile intervention is exactly `NEG-C3-PROFILE` in the frozen JSON. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

def rawContinuation (tag : Tag) (s : KState) : List (List Bool) :=
  actions.map fun a => (actionRow tag s a).map fun entry =>
    isLethalHazard entry.1

def rawM (tag : Tag) (s : KState) : Nat × List (List Bool) :=
  (publicPosition s, rawContinuation tag s)

/-- The raw `(f,L)` readout has precisely T1's imported M fibers. -/
theorem rawM_iff_imported_M (tag : Tag) (s t : KState) :
    (rawM tag s = rawM tag t) ↔
      (taggedMClass tag s = taggedMClass tag t) := by
  cases tag <;> cases s <;> cases t <;> decide

inductive LowerRule where | position | stateLabel deriving DecidableEq, BEq, Repr

def lowerReadout (rule : LowerRule) (s : KState) : Nat × Option KState :=
  match rule with
  | .position => (publicPosition s, none)
  | .stateLabel => (publicPosition s, some s)

def positiveLowerRule (tag : Tag) : LowerRule :=
  match publicChannelRule tag with
  | .position => .position

def C2Defect (rule : LowerRule) (tag : Tag) (s t : KState) : Prop :=
  lowerReadout rule s = lowerReadout rule t ∧ rawM tag s ≠ rawM tag t

def C2Pass (rule : LowerRule) (tag : Tag) : Prop :=
  C2Defect rule tag .p1w0 .p1w1

theorem c2_split_each_tag (tag : Tag) :
    C2Pass (positiveLowerRule tag) tag := by
  cases tag <;> unfold C2Pass C2Defect <;> decide

theorem c2_defect_nonempty_each_tag (tag : Tag) :
    ∃ s t : KState, C2Defect (positiveLowerRule tag) tag s t := by
  exact ⟨.p1w0,.p1w1,c2_split_each_tag tag⟩

theorem c2_tag_map_preserves_readouts (s : KState) :
    lowerReadout (positiveLowerRule .source) s =
      lowerReadout (positiveLowerRule .target) s ∧
    rawM .source s = rawM .target s := by
  cases s <;> decide

/-- `NEG-C2-SPLIT` replaces the lower public channel by the full state on
both tags; it removes every factorization defect, including the pinned pair. -/
theorem neg_c2_split_no_defect (tag : Tag) :
    ¬ ∃ s t : KState, C2Defect .stateLabel tag s t := by
  intro h
  rcases h with ⟨s,t,hLower,hDifferent⟩
  have hSame : s = t := by
    simpa [lowerReadout] using congrArg Prod.snd hLower
  subst t
  exact hDifferent rfl

inductive ProfileVariant where | positive | negC3Profile
  deriving DecidableEq, BEq, Repr

def profileRow (variant : ProfileVariant) (tag : Tag) (s : KState)
    (a : Action) : List (Ambient × Nat) :=
  if variant = .negC3Profile ∧ tag = .target ∧ s = .p1w0 ∧ a = .cw then
    [(.inK .p5w0,4)]
  else actionRow tag s a

def rawContinuationFor (variant : ProfileVariant) (tag : Tag)
    (s : KState) : List (List Bool) :=
  actions.map fun a => (profileRow variant tag s a).map fun entry =>
    isLethalHazard entry.1

def rawMFor (variant : ProfileVariant) (tag : Tag) (s : KState) :
    Nat × List (List Bool) :=
  (publicPosition s, rawContinuationFor variant tag s)

theorem rawMFor_positive (tag : Tag) (s : KState) :
    rawMFor .positive tag s = rawM tag s := by rfl

/-- The altered target successor remains safe, so the raw M partition
persists under the failed-prediction C3 intervention. -/
theorem neg_c3_rawM_iff_imported (tag : Tag) (s t : KState) :
    (rawMFor .negC3Profile tag s = rawMFor .negC3Profile tag t) ↔
      (taggedMClass tag s = taggedMClass tag t) := by
  cases tag <;> cases s <;> cases t <;> decide

def blockOf (classes : KState → Nat) : Ambient → Nat
  | .inK s => classes s
  | .p2w0 => 10
  | .p5w1 => 11

def profileMass (variant : ProfileVariant) (tag : Tag)
    (classes : KState → Nat) (s : KState) (a : Action) (block : Nat) : Nat :=
  (profileRow variant tag s a).foldl (fun total entry =>
    if blockOf classes entry.1 = block then total + entry.2 else total) 0

def profileSignature (variant : ProfileVariant) (tag : Tag)
    (classes : KState → Nat) (s : KState) : Nat × List (List Nat) :=
  (classes s, actions.map fun a =>
    (List.range 12).map fun block => profileMass variant tag classes s a block)

def profileStep (variant : ProfileVariant) (tag : Tag)
    (classes : KState → Nat) (s : KState) : Nat :=
  ((kernel.map (profileSignature variant tag classes)).eraseDups).idxOf
    (profileSignature variant tag classes s)

def profile0 (rule : LowerRule) (s : KState) : Nat :=
  match rule with
  | .position => publicPosition s
  | .stateLabel => (index s).val
def profile1 (variant : ProfileVariant) (rule : LowerRule) (tag : Tag) :
    KState → Nat := profileStep variant tag (profile0 rule)
def profile2 (variant : ProfileVariant) (rule : LowerRule) (tag : Tag) :
    KState → Nat := profileStep variant tag (profile1 variant rule tag)

def classCount (classes : KState → Nat) : Nat :=
  ((kernel.map classes).eraseDups).length

def samePartition {α β : Type} (a : KState → α) (b : KState → β) : Prop :=
  ∀ s t : KState, (a s = a t) ↔ (b s = b t)

def C3Pass (variant : ProfileVariant) (rule : LowerRule) (tag : Tag) : Prop :=
  classCount (profile0 rule) = 6 ∧
  classCount (profile1 variant rule tag) = 7 ∧
  classCount (profile2 variant rule tag) = 7 ∧
  samePartition (profile1 variant rule tag) (profile2 variant rule tag) ∧
  samePartition (profile2 variant rule tag) (rawMFor variant tag)

theorem c3_trajectory_each_tag (tag : Tag) :
    [classCount (profile0 (positiveLowerRule tag)),
     classCount (profile1 .positive (positiveLowerRule tag) tag),
     classCount (profile2 .positive (positiveLowerRule tag) tag)] = [6,7,7] := by
  cases tag <;> decide

theorem c3_stable_each_tag (tag : Tag) :
    samePartition (profile1 .positive (positiveLowerRule tag) tag)
      (profile2 .positive (positiveLowerRule tag) tag) := by
  cases tag <;> intro s t <;> cases s <;> cases t <;> decide

theorem c3_profile_fixed_each_tag (tag : Tag) (s : KState) :
    profile2 .positive (positiveLowerRule tag) tag s =
      profile1 .positive (positiveLowerRule tag) tag s := by
  cases tag <;> cases s <;> decide

theorem c3_terminal_is_M_each_tag (tag : Tag) :
    samePartition (profile2 .positive (positiveLowerRule tag) tag)
      (rawM tag) := by
  cases tag <;> intro s t <;> cases s <;> cases t <;> decide

theorem c3_terminal_iff_imported_M (tag : Tag) (s t : KState) :
    (profile2 .positive (positiveLowerRule tag) tag s =
      profile2 .positive (positiveLowerRule tag) tag t) ↔
    taggedMClass tag s = taggedMClass tag t := by
  exact (c3_terminal_is_M_each_tag tag s t).trans
    (rawM_iff_imported_M tag s t)

theorem c3_each_tag (tag : Tag) :
    C3Pass .positive (positiveLowerRule tag) tag := by
  cases tag <;> unfold C3Pass samePartition <;>
    refine ⟨by decide, by decide, by decide, ?_, ?_⟩ <;>
    intro s t <;> cases s <;> cases t <;> decide

theorem c3_tag_map_preserves_terminal (s : KState) :
    profile2 .positive (positiveLowerRule .source) .source s =
      profile2 .positive (positiveLowerRule .target) .target s := by
  cases s <;> decide

/-- M3b reported `NEG-C3-PROFILE` as a failed prediction: this intervention
does change a raw target row, but its C3 trajectory and M agreement remain. -/
theorem neg_c3_profile_still_holds :
    C3Pass .negC3Profile (positiveLowerRule .target) .target := by
  unfold C3Pass samePartition
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩ <;>
    intro s t <;> cases s <;> cases t <;> decide

theorem neg_c3_profile_fixed (s : KState) :
    profile2 .negC3Profile (positiveLowerRule .target) .target s =
      profile1 .negC3Profile (positiveLowerRule .target) .target s := by
  cases s <;> decide

theorem neg_c3_terminal_iff_imported_M (s t : KState) :
    (profile2 .negC3Profile (positiveLowerRule .target) .target s =
      profile2 .negC3Profile (positiveLowerRule .target) .target t) ↔
    taggedMClass .target s = taggedMClass .target t := by
  exact (neg_c3_profile_still_holds.2.2.2.2 s t).trans
    (neg_c3_rawM_iff_imported .target s t)

/-- Sensitivity guard: a full-state lower readout violates C3's required
six-class public starting partition. -/
theorem c3_state_label_lower_fails (tag : Tag) :
    ¬ C3Pass .positive .stateLabel tag := by
  intro h
  have hTen : classCount (profile0 .stateLabel) = 10 := by decide
  exact (by decide : (10 : Nat) ≠ 6) (hTen.symm.trans h.1)

end CSTTT.POS04
