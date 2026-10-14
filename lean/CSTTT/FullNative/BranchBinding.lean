import CSTTT.FullNative.EmittedFuture

/-! Derived all-word and actual-execution obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Binding
set_option autoImplicit false
set_option maxHeartbeats 8000000

def branch (right : Bool) (s : State) : Nat :=
  if s.outside then 0 else bit (if right then s.v else s.u)

def joint (s : State) : Nat := 2*branch false s+branch true s

theorem emission_domain (right : Bool) (s : State) : branch right s=0 ∨ branch right s=1 := by
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases right <;> decide +kernel

def marginalR (a : Bool) (o : Nat) : Rat :=
  if a then (if o=0 then 1 else 0) else (if o=0 ∨ o=1 then 1/2 else 0)

def referenceR : List Bool → List Nat → Rat
  | [],[] => 1
  | [],_::_ => 0
  | _::_,[] => 0
  | a::as,o::os => marginalR a o*referenceR as os

theorem marginalR_equation (right : Bool) (s : State) (a : Bool) (o : Nat) :
    (rationalRows model s a).foldr (fun e acc => (if branch right e.1=o then e.2 else 0)+acc) 0=marginalR a o := by
  by_cases h0 : o=0
  · subst o
    cases s with
    | mk p u v r phase =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases right <;> cases a <;> decide +kernel
  · by_cases h1 : o=1
    · subst o
      cases s with
      | mk p u v r phase =>
        cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases right <;> cases a <;> decide +kernel
    · have no : ∀ s, branch right s≠o := by
        intro s eq
        rcases emission_domain right s with hs | hs <;> omega
      simp only [no,if_false,marginalR,h0,h1,or_self]
      cases a <;> simpa using (no_emissionsR (rationalRows model s _))

theorem branch_all_wordsR (right : Bool) (s : State) (word : List Bool) (outputs : List Nat) :
    emittedLaw (rationalRows model) (branch right) s word outputs=referenceR word outputs := by
  induction word generalizing s outputs with
  | nil => cases outputs <;> rfl
  | cons a rest ih =>
    cases outputs with
    | nil => rfl
    | cons o os =>
      simp only [emittedLaw,ih,filtered_scaleR,marginalR_equation]
      rfl

theorem joint_gapR :
    emittedLaw (rationalRows model) joint FullInterface.replicaLeft [false] [0]=1/8 ∧
    emittedLaw (rationalRows model) joint (⟨false,false,true,false,true⟩:State) [false] [0]=3/8 := by
  decide +kernel

theorem joint_coherence (s t : State) (same : classes model s=classes model t)
    (word : List Bool) (outputs : List Nat) :
    emittedLaw (rationalRows model) joint s word outputs=
    emittedLaw (rationalRows model) joint t word outputs := by
  have hs := classes_shape_exact s t |>.mp same
  change emittedLaw (rationalRows model) (fun s => joint (representative (eraseReplica s))) s word outputs=
    emittedLaw (rationalRows model) (fun s => joint (representative (eraseReplica s))) t word outputs
  rw [projected_emitted_law (rationalRows model) (fun q => joint (representative q))
        eraseReplica representative projected_rows s word outputs,
      projected_emitted_law (rationalRows model) (fun q => joint (representative q))
        eraseReplica representative projected_rows t word outputs,hs]

def BindingEquivalent (s t : State) : Prop :=
  ∀ word outputs, emittedLaw (rationalRows model) joint s word outputs=
    emittedLaw (rationalRows model) joint t word outputs

def BranchwiseEquivalent (s t : State) : Prop :=
  ∀ right word outputs, emittedLaw (rationalRows model) (branch right) s word outputs=
    emittedLaw (rationalRows model) (branch right) t word outputs

theorem branchwise_universal (s t : State) : BranchwiseEquivalent s t := by
  intro right word outputs
  rw [branch_all_wordsR,branch_all_wordsR]

theorem strict_recombination :
    (∀ s t, BindingEquivalent s t → BranchwiseEquivalent s t) ∧
    BranchwiseEquivalent FullInterface.replicaLeft (⟨false,false,true,false,true⟩:State) ∧
    ¬ BindingEquivalent FullInterface.replicaLeft (⟨false,false,true,false,true⟩:State) := by
  refine ⟨fun s t _ => branchwise_universal s t,branchwise_universal _ _,?_⟩
  intro h
  have gap := h [false] [0]
  rw [joint_gapR.1,joint_gapR.2] at gap
  exact (by decide +kernel : (1:Rat)/8≠3/8) gap

def jointMarginal (a : Bool) (o : Nat) : Rat :=
  if a then (if o=0 then 1 else 0) else (if o<4 then 1/4 else 0)

theorem joint_range (s : State) : joint s<4 := by
  have l:=emission_domain false s
  have r:=emission_domain true s
  unfold joint
  omega

theorem flat_joint_margin (s : State) (a : Bool) (o : Nat) :
    (rationalRows (flatten model) s a).foldr (fun e acc => (if joint e.1=o then e.2 else 0)+acc) 0=jointMarginal a o := by
  by_cases h : o<4
  · have cases_o : o=0 ∨ o=1 ∨ o=2 ∨ o=3 := by omega
    rcases cases_o with rfl|rfl|rfl|rfl
    all_goals cases s with
      | mk p u v r phase =>
        cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases a <;> decide +kernel
  · have no : ∀ s, joint s≠o := by intro s eq;have range:=joint_range s;omega
    have h0 : o≠0 := by omega
    simp only [no,if_false,jointMarginal,h,h0]
    cases a <;> simpa using (no_emissionsR (rationalRows (flatten model) s _))

theorem flat_joint_all_words (s : State) (word : List Bool) (outputs : List Nat) :
    emittedLaw (rationalRows (flatten model)) joint s word outputs=independentLaw jointMarginal word outputs :=
  constant_emitted_law _ _ _ flat_joint_margin s word outputs

theorem flattening_destroys_joint_gap (s t : State) (word : List Bool) (outputs : List Nat) :
    emittedLaw (rationalRows (flatten model)) joint s word outputs=
      emittedLaw (rationalRows (flatten model)) joint t word outputs := by
  rw [flat_joint_all_words,flat_joint_all_words]

theorem flat_branch_margin (right : Bool) (s : State) (a : Bool) (o : Nat) :
    (rationalRows (flatten model) s a).foldr (fun e acc => (if branch right e.1=o then e.2 else 0)+acc) 0=marginalR a o := by
  by_cases h0 : o=0
  · subst o
    cases s with
    | mk p u v r phase =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases right <;> cases a <;> decide +kernel
  · by_cases h1 : o=1
    · subst o
      cases s with
      | mk p u v r phase =>
        cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases right <;> cases a <;> decide +kernel
    · have no : ∀ s, branch right s≠o := by
        intro s eq
        rcases emission_domain right s with hs | hs <;> omega
      simp only [no,if_false,marginalR,h0,h1,or_self]
      cases a <;> simpa using (no_emissionsR (rationalRows (flatten model) s _))

theorem flat_branch_all_words (right : Bool) (s : State) (word : List Bool) (outputs : List Nat) :
    emittedLaw (rationalRows (flatten model)) (branch right) s word outputs=referenceR word outputs := by
  induction word generalizing s outputs with
  | nil => cases outputs <;> rfl
  | cons a rest ih =>
    cases outputs with
    | nil => rfl
    | cons o os => simp only [emittedLaw,ih,filtered_scaleR,flat_branch_margin,referenceR]

theorem flatten_preserves_branches (right : Bool) (s : State) (word : List Bool) (outputs : List Nat) :
    emittedLaw (rationalRows (flatten model)) (branch right) s word outputs=
      emittedLaw (rationalRows model) (branch right) s word outputs := by
  rw [flat_branch_all_words,branch_all_wordsR]

end CSTTT.FullNative.Binding
