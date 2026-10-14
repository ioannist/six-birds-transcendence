import CSTTT.Robustness.DefectVector
import CSTTT.Countermodels.RealControls
import Init.Data.Rat.Lemmas
namespace CSTTT.RationalDefectTheory
open CSTTT
structure Component where
  label : Nat
  hard : Bool
  defect : Rat
  tolerance : Rat
  deriving DecidableEq, Repr

def ComponentAccepts (c : Component) : Prop :=
  0≤c.defect ∧ 0≤c.tolerance ∧ if c.hard then c.defect=0 else c.defect≤c.tolerance
def VectorAccepts (v : List Component) : Prop := ∀ c∈v, ComponentAccepts c
def NoWorse (lower upper : List Component) : Prop :=
  ListForall₂ (fun lo hi => lo.label=hi.label ∧ lo.hard=hi.hard ∧ lo.tolerance=hi.tolerance ∧
    0≤lo.defect ∧ lo.defect≤hi.defect) lower upper

theorem exact_component_coverage (v : List Component) (h : VectorAccepts v) :
    (∀ c∈v, c.hard=true → c.defect=0) ∧
    (∀ c∈v, c.hard=false → c.defect≤c.tolerance) := by
  constructor
  · intro c member hard
    have hc := h c member
    simpa [ComponentAccepts,hard] using hc.2.2
  · intro c member hard
    have hc := h c member
    simpa [ComponentAccepts,hard] using hc.2.2

theorem component_downward (lo hi : Component)
    (sameHard : lo.hard=hi.hard) (sameTolerance : lo.tolerance=hi.tolerance)
    (nonnegative : 0≤lo.defect) (order : lo.defect≤hi.defect)
    (accepted : ComponentAccepts hi) : ComponentAccepts lo := by
  refine ⟨nonnegative,by simpa [sameTolerance] using accepted.2.1,?_⟩
  cases hh : hi.hard with
  | false =>
    have hl := sameHard.trans hh
    have hs : hi.defect≤hi.tolerance := by simpa [hh] using accepted.2.2
    simpa [hl,sameTolerance] using Rat.le_trans order hs
  | true =>
    have hl := sameHard.trans hh
    have hz : hi.defect=0 := by simpa [hh] using accepted.2.2
    have bound : lo.defect≤0 := by simpa [hz] using order
    simpa [hl] using Rat.le_antisymm bound nonnegative

theorem vector_downward {lower upper : List Component}
    (order : NoWorse lower upper) (accepted : VectorAccepts upper) : VectorAccepts lower := by
  intro component member
  induction order with
  | nil => simp at member
  | @cons lo hi lowerTail upperTail hhead htail ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · obtain ⟨_,hh,ht,hn,ho⟩ := hhead
      exact component_downward component hi hh ht hn ho (accepted hi (by simp))
    · apply ih _ member
      intro c hc
      exact accepted c (by simp [hc])

def liftNat (label : Nat) (c : CSTTT.DefectTheory.DefectComponent) : Component :=
  ⟨label,c.hard,c.defect,c.tolerance⟩

def liftVectorFrom (start : Nat) : CSTTT.DefectTheory.DefectVector → List Component
  | [] => []
  | c::rest => liftNat start c::liftVectorFrom (start+1) rest

theorem nat_component_exact (label : Nat) (c : CSTTT.DefectTheory.DefectComponent) :
    ComponentAccepts (liftNat label c) ↔ CSTTT.DefectTheory.ComponentAccepts c := by
  cases hh : c.hard <;>
    simp [ComponentAccepts,liftNat,CSTTT.DefectTheory.ComponentAccepts,hh,
      Rat.natCast_nonneg,Rat.natCast_eq_zero_iff,Rat.natCast_le_natCast]

theorem nat_vector_exact (v : CSTTT.DefectTheory.DefectVector) (start : Nat) :
    VectorAccepts (liftVectorFrom start v) ↔ CSTTT.DefectTheory.VectorAccepts v := by
  induction v generalizing start with
  | nil => simp [VectorAccepts,liftVectorFrom,CSTTT.DefectTheory.VectorAccepts]
  | cons c cs ih =>
    constructor
    · intro accepted component member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact (nat_component_exact start component).mp (accepted _ (by simp [liftVectorFrom]))
      · have tail : VectorAccepts (liftVectorFrom (start+1) cs) := by
          intro cc hc
          exact accepted cc (by simp [liftVectorFrom,hc])
        exact (ih (start+1)).mp tail component member
    · intro accepted component member
      simp only [liftVectorFrom,List.mem_cons] at member
      rcases member with rfl | member
      · exact (nat_component_exact start c).mpr (accepted c (by simp))
      · have tail : CSTTT.DefectTheory.VectorAccepts cs := by
          intro cc hc
          exact accepted cc (by simp [hc])
        exact (ih (start+1)).mpr tail component member

def scalar (v : List Component) : Rat := (v.map Component.defect).sum

theorem nat_scalar_exact (v : CSTTT.DefectTheory.DefectVector) (start : Nat) :
    scalar (liftVectorFrom start v)=((v.map CSTTT.DefectTheory.DefectComponent.defect).sum : Rat) := by
  induction v generalizing start with
  | nil => rfl
  | cons c cs ih =>
    simpa [scalar,liftVectorFrom,liftNat,Rat.natCast_add] using
      congrArg (fun s : Rat => (c.defect : Rat)+s) (ih (start+1))

/-- Transfer the already committed actual TTN10 controls; no new fixture is
evaluated or adjusted here. The general vector laws quantify arbitrary Rat. -/
theorem released_equal_scalar_counter :
    scalar (liftVectorFrom 0 CSTTT.RealControls.scalarAcceptedVector)=
      scalar (liftVectorFrom 0 CSTTT.RealControls.scalarHardVector) ∧
    VectorAccepts (liftVectorFrom 0 CSTTT.RealControls.scalarAcceptedVector) ∧
    ¬ VectorAccepts (liftVectorFrom 0 CSTTT.RealControls.scalarHardVector) := by
  have old := CSTTT.RealControls.ttn10_equal_scalar_different_acceptance
  refine ⟨?_,(nat_vector_exact _ 0).mpr old.2.2.2.2.1,?_⟩
  · rw [nat_scalar_exact,nat_scalar_exact,old.2.1]
  · intro accepted
    exact old.2.2.2.2.2 ((nat_vector_exact _ 0).mp accepted)

theorem released_same_labeled_schema :
    (liftVectorFrom 0 CSTTT.RealControls.scalarAcceptedVector).map
      (fun c => (c.label,c.hard,c.tolerance)) =
    (liftVectorFrom 0 CSTTT.RealControls.scalarHardVector).map
      (fun c => (c.label,c.hard,c.tolerance)) := by decide

theorem scalar_does_not_determine_exact_acceptance :
    ∃ x y : List Component, x≠[] ∧ y≠[] ∧ scalar x=scalar y ∧
      VectorAccepts x ∧ ¬ VectorAccepts y := by
  exact ⟨liftVectorFrom 0 CSTTT.RealControls.scalarAcceptedVector,
    liftVectorFrom 0 CSTTT.RealControls.scalarHardVector,by decide,by decide,
    released_equal_scalar_counter⟩

/-- Exact acceptance includes nonnegative raw defect/tolerance values, and
both directions are proved for every rational-valued component. -/
theorem exact_acceptance_iff (v : List Component) :
    VectorAccepts v ↔
      (∀ c∈v, 0≤c.defect ∧ 0≤c.tolerance) ∧
      (∀ c∈v, c.hard=true → c.defect=0) ∧
      (∀ c∈v, c.hard=false → c.defect≤c.tolerance) := by
  constructor
  · intro accepted
    exact ⟨fun c hc => ⟨(accepted c hc).1,(accepted c hc).2.1⟩,
      exact_component_coverage v accepted⟩
  · rintro ⟨nonnegative,hard,soft⟩ c member
    refine ⟨(nonnegative c member).1,(nonnegative c member).2,?_⟩
    cases hh : c.hard with
    | false => simpa [hh] using soft c member hh
    | true => simpa [hh] using hard c member hh

/-- The already released controls have identical labeled gate schemas.
This strengthens scalar failure without adding a newly evaluated fixture. -/
theorem scalar_failure_with_same_schema :
    ∃ x y : List Component, x≠[] ∧ y≠[] ∧
      x.map (fun c => (c.label,c.hard,c.tolerance)) =
        y.map (fun c => (c.label,c.hard,c.tolerance)) ∧
      scalar x=scalar y ∧ VectorAccepts x ∧ ¬ VectorAccepts y := by
  exact ⟨liftVectorFrom 0 CSTTT.RealControls.scalarAcceptedVector,
    liftVectorFrom 0 CSTTT.RealControls.scalarHardVector,
    by decide,by decide,released_same_labeled_schema,released_equal_scalar_counter⟩

/-- No predicate of the scalar sum recovers exact acceptance for all vectors. -/
theorem scalar_classifier_impossible (classify : Rat → Prop) :
    ¬ (∀ v : List Component, VectorAccepts v ↔ classify (scalar v)) := by
  intro exactClassifier
  obtain ⟨x,y,_,_,same,accepted,rejected⟩ :=
    scalar_does_not_determine_exact_acceptance
  have scalarAccepts := (exactClassifier x).mp accepted
  rw [same] at scalarAccepts
  exact rejected ((exactClassifier y).mpr scalarAccepts)

/-- Even the entire labeled gate schema together with the scalar sum fails
 to recover acceptance. The actual schema and sum agree for both controls. -/
theorem schema_scalar_classifier_impossible
    (classify : List (Nat × Bool × Rat) → Rat → Prop) :
    ¬ (∀ v : List Component,
      VectorAccepts v ↔ classify (v.map (fun c => (c.label,c.hard,c.tolerance))) (scalar v)) := by
  intro exactClassifier
  obtain ⟨x,y,_,_,sameSchema,sameScalar,accepted,rejected⟩ := scalar_failure_with_same_schema
  have verdict := (exactClassifier x).mp accepted
  rw [sameSchema,sameScalar] at verdict
  exact rejected ((exactClassifier y).mpr verdict)

end CSTTT.RationalDefectTheory
