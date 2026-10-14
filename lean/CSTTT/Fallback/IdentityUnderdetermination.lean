import CSTTT.Fallback.SafeNativeContinuation

namespace CSTTT.FallbackTheory.IdentityUnderdeterminationPrototype
open CSTTT.TargetTheory.GenericHandoff
open CSTTT.TargetTheory.GenericHandoff.NativeComposition
open NativeReceiptExtensionPrototype NativeTwoHopReceiptPrototype NativeSafeClosurePrototype
set_option autoImplicit false

-- Class(b): alternative numerical identity interpretations do not alter any
-- raw execution data or computed ancestry readout.
def identityCode (source chosen node : Nat) : Nat := if node=source then chosen else node
def NumericalIdentity (source chosen left right : Nat) : Prop :=
  identityCode source chosen left=identityCode source chosen right
def Compatible (ancestry : Nat → Nat → Prop) (source : Nat) (identity : Nat → Nat → Prop) : Prop :=
  Equivalence identity ∧
    (∀ target,target≠source → identity source target → ancestry source target) ∧
    ∀ left right,left≠source → right≠source → identity source left → identity source right → left=right

theorem numerical_equivalence (source chosen : Nat) : Equivalence (NumericalIdentity source chosen) := by
  exact ⟨fun _ => rfl,fun equal => equal.symm,fun first second => first.trans second⟩
theorem numerical_future_iff (source chosen target : Nat) (later : target≠source) :
    NumericalIdentity source chosen source target ↔ target=chosen := by
  simp [NumericalIdentity,identityCode,later,eq_comm]
theorem numerical_compatible (ancestry : Nat → Nat → Prop) (source chosen : Nat)
    (chosenAncestor : ancestry source chosen) : Compatible ancestry source (NumericalIdentity source chosen) := by
  refine ⟨numerical_equivalence source chosen,?_,?_⟩
  · intro target later equal
    have targetEq := (numerical_future_iff source chosen target later).mp equal
    simpa [targetEq] using chosenAncestor
  · intro left right laterLeft laterRight equalLeft equalRight
    exact ((numerical_future_iff source chosen left laterLeft).mp equalLeft).trans
      ((numerical_future_iff source chosen right laterRight).mp equalRight).symm

-- BOTH full equivalence relations are ancestry-compatible and each has one
-- later identity, but they disagree on the actual source's selected branch.
theorem two_identity_extensions (ancestry : Nat → Nat → Prop) (source left right : Nat)
    (leftAncestor : ancestry source left) (rightAncestor : ancestry source right)
    (leftLater : left≠source) (rightLater : right≠source) (distinct : left≠right) :
    Compatible ancestry source (NumericalIdentity source left) ∧
    Compatible ancestry source (NumericalIdentity source right) ∧
    NumericalIdentity source left source left ∧ ¬NumericalIdentity source left source right ∧
    NumericalIdentity source right source right ∧ ¬NumericalIdentity source right source left ∧
    NumericalIdentity source left ≠ NumericalIdentity source right := by
  have chooseLeft := (numerical_future_iff source left left leftLater).mpr rfl
  have chooseRight := (numerical_future_iff source right right rightLater).mpr rfl
  have rejectRight : ¬NumericalIdentity source left source right := by
    intro equal
    exact distinct ((numerical_future_iff source left right rightLater).mp equal).symm
  have rejectLeft : ¬NumericalIdentity source right source left := by
    intro equal
    exact distinct ((numerical_future_iff source right left leftLater).mp equal)
  refine ⟨numerical_compatible ancestry source left leftAncestor,
    numerical_compatible ancestry source right rightAncestor,chooseLeft,rejectRight,chooseRight,rejectLeft,?_⟩
  intro equal
  rw [equal] at chooseLeft
  exact rejectLeft chooseLeft

-- EVERY Nat length is supplied by actual supported update/fission. The two
-- interpretations share the SAME raw execution, full-register copies, whole
-- historical package, individual game and computed ancestry predicate.
theorem actual_arbitrary_length_identity_underdetermination (affected : Owner)
    (leftNames rightNames : Owner → CarrierId) (history : Factor) (length : Nat) :
    ∃ commands finished state,
      SafeCommands commands ∧ commands.length=length+1 ∧
      extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
        history commands=some finished ∧
      finished.read (5+length)=some state ∧ finished.read (6+length)=some state ∧
      PostWithdrawalQualifiedPrototype.qualifiedPackageAt (withdrawnCurrent affected) false state ∧
      NativeAcquiredWithdrawalPrototype.ContinuationLaw affected false state ∧
      Compatible
        (fun source target => ancestryDecision leftNames rightNames (withdrawnCurrent affected)
          NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected) history commands source target=some true)
        0 (NumericalIdentity 0 (5+length)) ∧
      Compatible
        (fun source target => ancestryDecision leftNames rightNames (withdrawnCurrent affected)
          NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected) history commands source target=some true)
        0 (NumericalIdentity 0 (6+length)) ∧
      NumericalIdentity 0 (5+length) 0 (5+length) ∧ ¬NumericalIdentity 0 (5+length) 0 (6+length) ∧
      NumericalIdentity 0 (6+length) 0 (6+length) ∧ ¬NumericalIdentity 0 (6+length) 0 (5+length) ∧
      NumericalIdentity 0 (5+length) ≠ NumericalIdentity 0 (6+length) := by
  obtain ⟨commands,finished,state,safe,size,actual,leftRead,rightRead,leftAncestor,rightAncestor,package,law⟩ :=
    canonical_arbitrary_length_fission affected leftNames rightNames history length
  have extensions := two_identity_extensions
    (fun source target => ancestryDecision leftNames rightNames (withdrawnCurrent affected)
      NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected) history commands source target=some true)
    0 (5+length) (6+length) leftAncestor rightAncestor (by omega) (by omega) (by omega)
  exact ⟨commands,finished,state,safe,size,actual,leftRead,rightRead,package,law,extensions⟩

end CSTTT.FallbackTheory.IdentityUnderdeterminationPrototype
