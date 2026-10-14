import CSTTT.POS04.GenericTransport
import CSTTT.Transport.RawBridge
import CSTTT.Prospects.Statements

namespace CSTTT.FallbackTheory.RawPredictiveQuotient
open CSTTT.TransportTheory
variable {H S T E R SC TC RR M : Type}
-- Class (b): predictive raw equations only; no corridor, strict record or ancestry premise.
def MapLaws (b : RawBridge H S T E R SC TC RR M) : Prop :=
  (∀ s, b.targetClass (b.mapState s)=b.mapClass (b.sourceClass s)) ∧
  FutureMapLaws b ∧ Function.Injective b.mapClass
-- Class (b): derive all-query transport directly from raw class/transition/enumeration equations.
theorem actual_future_transport (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b) :
    ∀ s query, targetFuture b (b.mapState s) query=sourceFuture b s query := by
  have wordEq (w : List Nat) : ∀ s d,
      targetWord b (b.mapState s) w (b.mapState d)=sourceWord b s w d := by
    induction w with
    | nil =>
      intro s d
      have heq : (b.targetClass (b.mapState s)=b.targetClass (b.mapState d)) ↔
          b.sourceClass s=b.sourceClass d := by
        rw [laws.1 s,laws.1 d]
        exact ⟨fun h => laws.2.2 h,congrArg b.mapClass⟩
      simp only [sourceWord,targetWord]
      by_cases hs : b.sourceClass s=b.sourceClass d
      · simp [hs,heq.mpr hs]
      · have ht : ¬ b.targetClass (b.mapState s)=b.targetClass (b.mapState d) := fun h => hs (heq.mp h)
        simp [hs,ht]
    | cons action rest ih =>
      intro s d
      simp only [sourceWord,targetWord,laws.2.1.1,List.map_map]
      congr 1
      apply List.map_congr_left
      intro u _
      simp only [Function.comp_apply]
      rw [laws.2.1.2 s u action,ih u d]
  intro s query
  cases query with
  | nil => rfl
  | cons destination word =>
    simp only [sourceFuture,targetFuture,laws.2.1.1,List.getElem?_map]
    cases hd : b.sourceStates[destination]? with
    | none => simp
    | some d => simpa [hd] using wordEq word s d
-- Class (b): released bridge local laws instantiate the smaller predictive-only contract.
theorem from_released_core (b : RawBridge H S T E R SC TC RR M)
    (hc : BridgeCoreLaws b) (hf : FutureMapLaws b) (hi : Function.Injective b.mapClass) : MapLaws b :=
  ⟨fun s => (hc.1 s).2.1,hf,hi⟩
-- Class (b): prediction is calculated from the raw action-word recursion.
def sourceEquivalent (b : RawBridge H S T E R SC TC RR M) (x y : S) : Prop :=
  ∀ query, sourceFuture b x query=sourceFuture b y query
-- Class (b): target prediction uses the same declared raw query language.
def targetEquivalent (b : RawBridge H S T E R SC TC RR M) (x y : T) : Prop :=
  ∀ query, targetFuture b x query=targetFuture b y query
-- Class (b): the actual source predictive relation is an equivalence.
def sourceSetoid (b : RawBridge H S T E R SC TC RR M) : Setoid S where
  r := sourceEquivalent b
  iseqv := ⟨fun _ _ => rfl,fun h q => (h q).symm,fun h k q => (h q).trans (k q)⟩
-- Class (b): the actual target predictive relation is an equivalence.
def targetSetoid (b : RawBridge H S T E R SC TC RR M) : Setoid T where
  r := targetEquivalent b
  iseqv := ⟨fun _ _ => rfl,fun h q => (h q).symm,fun h k q => (h q).trans (k q)⟩
-- Class (b): raw transition/class-map equations derive respectfulness.
theorem actual_bridge_respects (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b) :
    CSTTT.Prospects.PredictiveBridgeDescent S T b.mapState (sourceEquivalent b) (targetEquivalent b) := by
  intro x y equivalent query
  rw [actual_future_transport b laws x query,actual_future_transport b laws y query]
  exact equivalent query
-- Class (b): construct the representative-independent quotient map from the actual raw map.
def bridge (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b) :
    Quotient (sourceSetoid b) → Quotient (targetSetoid b) :=
  Quotient.lift (fun x => Quotient.mk (targetSetoid b) (b.mapState x))
    (fun _ _ equivalent => Quotient.sound (actual_bridge_respects b laws _ _ equivalent))
-- Class (b): return exactly the actual mapped state's predictive class.
theorem bridge_mk (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b) (x : S) :
    bridge b laws (Quotient.mk (sourceSetoid b) x)=Quotient.mk (targetSetoid b) (b.mapState x) := rfl
-- Class (b): equivalent representatives have the same actual quotient result.
theorem representative_independent (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b)
    (x y : S) (equivalent : sourceEquivalent b x y) :
    bridge b laws (Quotient.mk (sourceSetoid b) x)=
      bridge b laws (Quotient.mk (sourceSetoid b) y) := by
  exact congrArg (bridge b laws) (Quotient.sound equivalent)
-- Class (b): exact quotient return necessarily respects actual predictive equivalence.
theorem descended_map_forces_respectful (b : RawBridge H S T E R SC TC RR M)
    (f : Quotient (sourceSetoid b) → Quotient (targetSetoid b))
    (actual : ∀ x, f (Quotient.mk (sourceSetoid b) x)=Quotient.mk (targetSetoid b) (b.mapState x)) :
    CSTTT.Prospects.PredictiveBridgeDescent S T b.mapState (sourceEquivalent b) (targetEquivalent b) := by
  intro x y equivalent
  have eq := congrArg f (Quotient.sound equivalent)
  rw [actual x,actual y] at eq
  exact Quotient.exact eq
-- Class (b): the actual representative equation uniquely determines the quotient map.
theorem unique_bridge (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b)
    (f : Quotient (sourceSetoid b) → Quotient (targetSetoid b))
    (actual : ∀ x, f (Quotient.mk (sourceSetoid b) x)=Quotient.mk (targetSetoid b) (b.mapState x)) :
    f=bridge b laws := by
  funext q
  induction q using Quotient.inductionOn with
  | _ x => exact actual x
-- Class (b): calculate finite source signatures from declared raw predictive queries.
def sourceSignature (b : RawBridge H S T E R SC TC RR M) (queries : List (List Nat)) (x : S) : List Nat :=
  queries.map (sourceFuture b x)
-- Class (b): calculate target signatures from the same declared query list.
def targetSignature (b : RawBridge H S T E R SC TC RR M) (queries : List (List Nat)) (x : T) : List Nat :=
  queries.map (targetFuture b x)
-- Class (b): local raw bridge laws preserve every finite signature.
theorem actual_finite_signature (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b)
    (queries : List (List Nat)) (x : S) :
    targetSignature b queries (b.mapState x)=sourceSignature b queries x := by
  unfold targetSignature sourceSignature
  exact List.map_congr_left (fun q _ => actual_future_transport b laws x q)
-- Class (b): exact equality of finite source signatures descends to target signatures.
theorem finite_signature_respects (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b)
    (queries : List (List Nat)) (x y : S)
    (equal : sourceSignature b queries x=sourceSignature b queries y) :
    targetSignature b queries (b.mapState x)=targetSignature b queries (b.mapState y) := by
  rw [actual_finite_signature b laws queries x,actual_finite_signature b laws queries y]
  exact equal
-- Class (b): the exact actual predictive quotient map is injective.
theorem bridge_injective (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b) :
    Function.Injective (bridge b laws) := by
  intro q r equal
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      have target : targetEquivalent b (b.mapState x) (b.mapState y) := Quotient.exact equal
      apply Quotient.sound
      intro query
      rw [← actual_future_transport b laws x query,← actual_future_transport b laws y query]
      exact target query
-- Class (b): every enumerated target has an actual preimage from the declared source enumeration.
theorem target_covered_preimage (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (t : T) (member : t∈b.targetStates) : ∃ s, s∈b.sourceStates ∧ b.mapState s=t := by
  rw [laws.2.1.1] at member
  exact List.mem_map.mp member
-- Class (b): whole-target coverage upgrades actual quotient descent to surjectivity.
theorem bridge_surjective (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (complete : ∀ t, t∈b.targetStates) : Function.Surjective (bridge b laws) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ t =>
    obtain ⟨s,_,eq⟩ := target_covered_preimage b laws t (complete t)
    exact ⟨Quotient.mk (sourceSetoid b) s,congrArg (Quotient.mk (targetSetoid b)) eq⟩
-- Class (b): enumerate actual source predictive classes from the raw finite state list.
def sourceClassList (b : RawBridge H S T E R SC TC RR M) : List (Quotient (sourceSetoid b)) :=
  b.sourceStates.map (Quotient.mk (sourceSetoid b))
-- Class (b): finite raw source coverage covers every actual full predictive class.
theorem source_classes_covered (b : RawBridge H S T E R SC TC RR M)
    (complete : ∀ s, s∈b.sourceStates) : ∀ q, q∈sourceClassList b := by
  intro q
  induction q using Quotient.inductionOn with
  | _ s => exact List.mem_map.mpr ⟨s,complete s,rfl⟩
-- Class (b): raw finite state coverage constructs an actual finite quotient presentation.
def sourceClassEnum (b : RawBridge H S T E R SC TC RR M)
    (complete : ∀ s, s∈b.sourceStates) : CSTTT.FiniteEnum (Quotient (sourceSetoid b)) :=
  ⟨sourceClassList b,source_classes_covered b complete⟩
-- Class (b): finite-probe equivalence is computed signature equality, not a supplied equivalence predicate.
def finiteSourceSetoid (b : RawBridge H S T E R SC TC RR M) (queries : List (List Nat)) : Setoid S where
  r := fun x y => sourceSignature b queries x=sourceSignature b queries y
  iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩
-- Class (b): the target finite partition uses its actual raw signature.
def finiteTargetSetoid (b : RawBridge H S T E R SC TC RR M) (queries : List (List Nat)) : Setoid T where
  r := fun x y => targetSignature b queries x=targetSignature b queries y
  iseqv := ⟨fun _ => rfl,Eq.symm,Eq.trans⟩
-- Class (b): construct the finite-signature quotient bridge from the actual map.
def finiteBridge (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b) (queries : List (List Nat)) :
    Quotient (finiteSourceSetoid b queries) → Quotient (finiteTargetSetoid b queries) :=
  Quotient.lift (fun x => Quotient.mk (finiteTargetSetoid b queries) (b.mapState x))
    (fun x y eq => Quotient.sound (finite_signature_respects b laws queries x y eq))
-- Class (b): the finite quotient bridge returns exactly the actual mapped state class.
theorem finite_bridge_mk (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (queries : List (List Nat)) (x : S) :
    finiteBridge b laws queries (Quotient.mk (finiteSourceSetoid b queries) x)=
      Quotient.mk (finiteTargetSetoid b queries) (b.mapState x) := rfl
-- Class (b): a declared finite signature is a coarsening of actual all-query prediction.
theorem full_implies_finite (b : RawBridge H S T E R SC TC RR M) (queries : List (List Nat))
    (x y : S) (eq : sourceEquivalent b x y) : sourceSignature b queries x=sourceSignature b queries y :=
  List.map_congr_left (fun q _ => eq q)
-- Class (b): derive source finite coarsening from the actual full predictive quotient.
def sourceCoarsen (b : RawBridge H S T E R SC TC RR M) (queries : List (List Nat)) :
    Quotient (sourceSetoid b) → Quotient (finiteSourceSetoid b queries) :=
  Quotient.lift (fun x => Quotient.mk (finiteSourceSetoid b queries) x)
    (fun x y eq => Quotient.sound (full_implies_finite b queries x y eq))
-- Class (b): derive target finite coarsening from actual full target prediction.
def targetCoarsen (b : RawBridge H S T E R SC TC RR M) (queries : List (List Nat)) :
    Quotient (targetSetoid b) → Quotient (finiteTargetSetoid b queries) :=
  Quotient.lift (fun x => Quotient.mk (finiteTargetSetoid b queries) x)
    (fun _ _ eq => Quotient.sound (List.map_congr_left (fun q _ => eq q)))
-- Class (b): full raw descent and finite coarsening commute on every source class.
theorem coarsening_square (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (queries : List (List Nat)) (q : Quotient (sourceSetoid b)) :
    targetCoarsen b queries (bridge b laws q)=finiteBridge b laws queries (sourceCoarsen b queries q) := by
  induction q using Quotient.inductionOn with
  | _ x => rfl
-- Class (b): finite source classes are presented directly by the actual raw source list.
def finiteSourceClassEnum (b : RawBridge H S T E R SC TC RR M) (queries : List (List Nat))
    (complete : ∀ s, s∈b.sourceStates) : CSTTT.FiniteEnum (Quotient (finiteSourceSetoid b queries)) where
  elems := b.sourceStates.map (Quotient.mk (finiteSourceSetoid b queries))
  complete := by
    intro q
    induction q using Quotient.inductionOn with
    | _ s => exact List.mem_map.mpr ⟨s,complete s,rfl⟩
-- Class (b): finite target classes are presented directly by the actual raw target list.
def finiteTargetClassEnum (b : RawBridge H S T E R SC TC RR M) (queries : List (List Nat))
    (complete : ∀ t, t∈b.targetStates) : CSTTT.FiniteEnum (Quotient (finiteTargetSetoid b queries)) where
  elems := b.targetStates.map (Quotient.mk (finiteTargetSetoid b queries))
  complete := by
    intro q
    induction q using Quotient.inductionOn with
    | _ t => exact List.mem_map.mpr ⟨t,complete t,rfl⟩
end CSTTT.FallbackTheory.RawPredictiveQuotient

namespace CSTTT.FallbackTheory.RawPredictiveQuotient
open CSTTT.TransportTheory
variable {H S T E R SC TC RR M : Type}
-- Class (b): deterministic complete current-class query family from raw enumeration.
def classQueries (b : RawBridge H S T E R SC TC RR M) : List (List Nat) :=
  (List.range b.sourceStates.length).map (fun i => [i])
-- Class (b): the actual finite raw signature detects source class equality under raw coverage.
theorem class_queries_detect (b : RawBridge H S T E R SC TC RR M)
    (complete : ∀ s, s∈b.sourceStates) (x y : S)
    (eq : sourceSignature b (classQueries b) x=sourceSignature b (classQueries b) y) :
    b.sourceClass x=b.sourceClass y := by
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp (complete x)
  have bound : i<b.sourceStates.length := (List.getElem?_eq_some_iff.mp hi).choose
  have mem : [i]∈classQueries b := List.mem_map.mpr ⟨i,List.mem_range.mpr bound,rfl⟩
  have query := List.map_inj_left.mp eq [i] mem
  letI := b.sourceClassDecEq
  by_cases same : b.sourceClass x=b.sourceClass y
  · exact same
  · have opposite : b.sourceClass y≠b.sourceClass x := Ne.symm same
    simp [sourceFuture,hi,sourceWord,opposite] at query
-- Class (b): source raw row bisimulation gives the reverse all-query implication.
theorem class_implies_full (b : RawBridge H S T E R SC TC RR M)
    (bisim : SourceActionBisim b) (x y : S) (eq : b.sourceClass x=b.sourceClass y) :
    sourceEquivalent b x y := source_future_sufficient_of_bisim b bisim x y eq
-- Class (b): the deterministic finite probe partition exactly equals the actual all-query partition.
theorem finite_full_iff (b : RawBridge H S T E R SC TC RR M)
    (complete : ∀ s, s∈b.sourceStates) (bisim : SourceActionBisim b) (x y : S) :
    sourceSignature b (classQueries b) x=sourceSignature b (classQueries b) y ↔ sourceEquivalent b x y := by
  exact ⟨fun eq => class_implies_full b bisim x y (class_queries_detect b complete x y eq),
    full_implies_finite b (classQueries b) x y⟩
-- Class (b): the same actual finite partition is exactly the supplied raw class code.
theorem finite_class_iff (b : RawBridge H S T E R SC TC RR M)
    (complete : ∀ s, s∈b.sourceStates) (bisim : SourceActionBisim b) (x y : S) :
    sourceSignature b (classQueries b) x=sourceSignature b (classQueries b) y ↔
      b.sourceClass x=b.sourceClass y := by
  exact ⟨class_queries_detect b complete x y,fun eq =>
    full_implies_finite b (classQueries b) x y (class_implies_full b bisim x y eq)⟩
-- Class (b): the actual all-query equivalence is neither broader nor narrower than the raw class under coverage/bisimulation.
theorem full_class_iff (b : RawBridge H S T E R SC TC RR M)
    (complete : ∀ s, s∈b.sourceStates) (bisim : SourceActionBisim b) (x y : S) :
    sourceEquivalent b x y ↔ b.sourceClass x=b.sourceClass y :=
  (finite_full_iff b complete bisim x y).symm.trans (finite_class_iff b complete bisim x y)
-- Class (b): the finite coarsening is injective when the deterministic complete probe family is exact.
theorem complete_coarsening_injective (b : RawBridge H S T E R SC TC RR M)
    (complete : ∀ s, s∈b.sourceStates) (bisim : SourceActionBisim b) :
    Function.Injective (sourceCoarsen b (classQueries b)) := by
  intro q r eq
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      exact Quotient.sound ((finite_full_iff b complete bisim x y).mp (Quotient.exact eq))
-- Class (b): every finite class has an actual full predictive representative.
theorem source_coarsening_surjective (b : RawBridge H S T E R SC TC RR M)
    (queries : List (List Nat)) : Function.Surjective (sourceCoarsen b queries) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨Quotient.mk (sourceSetoid b) x,rfl⟩
-- Class (b): actual finite bridge is injective for every declared finite query family.
theorem finite_bridge_injective (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b) (queries : List (List Nat)) : Function.Injective (finiteBridge b laws queries) := by
  intro q r eq
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      have target : targetSignature b queries (b.mapState x)=targetSignature b queries (b.mapState y) :=
        Quotient.exact eq
      rw [actual_finite_signature b laws queries x,actual_finite_signature b laws queries y] at target
      exact Quotient.sound target
-- Class (b): whole raw target coverage gives surjectivity of the actual finite bridge.
theorem finite_bridge_surjective (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b) (queries : List (List Nat)) (complete : ∀ t, t∈b.targetStates) :
    Function.Surjective (finiteBridge b laws queries) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ t =>
    obtain ⟨s,_,eq⟩ := target_covered_preimage b laws t (complete t)
    exact ⟨Quotient.mk (finiteSourceSetoid b queries) s,congrArg (Quotient.mk (finiteTargetSetoid b queries)) eq⟩
-- Class (b): the same finite raw family characterizes the whole actual target predictive partition under both raw coverage laws.
theorem target_finite_full_iff (b : RawBridge H S T E R SC TC RR M)
    (laws : MapLaws b) (sourceComplete : ∀ s, s∈b.sourceStates)
    (targetComplete : ∀ t, t∈b.targetStates) (bisim : SourceActionBisim b) (t u : T) :
    targetSignature b (classQueries b) t=targetSignature b (classQueries b) u ↔ targetEquivalent b t u := by
  obtain ⟨x,_,rfl⟩ := target_covered_preimage b laws t (targetComplete t)
  obtain ⟨y,_,rfl⟩ := target_covered_preimage b laws u (targetComplete u)
  rw [actual_finite_signature b laws (classQueries b) x,actual_finite_signature b laws (classQueries b) y]
  constructor
  · intro eq query
    rw [actual_future_transport b laws x query,actual_future_transport b laws y query]
    exact (finite_full_iff b sourceComplete bisim x y).mp eq query
  · intro eq
    apply (finite_full_iff b sourceComplete bisim x y).mpr
    intro query
    rw [← actual_future_transport b laws x query,← actual_future_transport b laws y query]
    exact eq query
end CSTTT.FallbackTheory.RawPredictiveQuotient

namespace CSTTT.FallbackTheory.ReleasedPredictiveQuotient
open CSTTT.TransportTheory CSTTT.POS04 CSTTT.Objecthood.T1Audit
open CSTTT.FallbackTheory.RawPredictiveQuotient
-- Class (b): reuse the existing committed raw bridge, without a new fixture or input intervention.
theorem released_map_laws : MapLaws (pos04RawBridge .positive) :=
  from_released_core _ pos04_bridge_raw_laws.1 pos04_bridge_raw_laws.2.2.1 pos04_bridge_raw_laws.2.2.2.1
-- Class (b): whole raw source coverage is proved from the ten released kernel states.
theorem released_source_coverage : ∀ s, s∈(pos04RawBridge .positive).sourceStates := by
  intro s; cases s <;> decide +kernel
-- Class (b): whole raw target coverage uses the same existing target enumeration.
theorem released_target_coverage : ∀ t, t∈(pos04RawBridge .positive).targetStates := by
  intro t; cases t <;> decide +kernel
-- Class (b): exact finite/current-class/all-query agreement for every released source pair.
theorem released_source_partition (x y : KState) :
    sourceSignature (pos04RawBridge .positive) (classQueries (pos04RawBridge .positive)) x=
      sourceSignature (pos04RawBridge .positive) (classQueries (pos04RawBridge .positive)) y ↔
    sourceEquivalent (pos04RawBridge .positive) x y :=
  finite_full_iff _ released_source_coverage pos04_bridge_raw_laws.2.1 x y
-- Class (b): the finite raw target partition exactly agrees with actual all-query prediction.
theorem released_target_partition (x y : KState) :
    targetSignature (pos04RawBridge .positive) (classQueries (pos04RawBridge .positive)) x=
      targetSignature (pos04RawBridge .positive) (classQueries (pos04RawBridge .positive)) y ↔
    targetEquivalent (pos04RawBridge .positive) x y :=
  target_finite_full_iff _ released_map_laws released_source_coverage released_target_coverage
    pos04_bridge_raw_laws.2.1 x y
-- Class (b): derive finite raw quotient coverage, with repeated equivalent representatives allowed.
def released_source_presentation : CSTTT.FiniteEnum (Quotient (sourceSetoid (pos04RawBridge .positive))) :=
  sourceClassEnum _ released_source_coverage
-- Class (b): both actual predictive quotients are inhabited by an existing released kernel state.
theorem released_quotients_nonempty :
    Nonempty (Quotient (sourceSetoid (pos04RawBridge .positive))) ∧
      Nonempty (Quotient (targetSetoid (pos04RawBridge .positive))) :=
  ⟨⟨Quotient.mk _ KState.p1w0⟩,⟨Quotient.mk _ KState.p1w0⟩⟩
-- Class (b): the released C2 split proves the actual finite signature is informative.
theorem released_c2_split_distinguished :
    sourceSignature (pos04RawBridge .positive) (classQueries (pos04RawBridge .positive)) KState.p1w0≠
      sourceSignature (pos04RawBridge .positive) (classQueries (pos04RawBridge .positive)) KState.p1w1 := by
  intro eq
  have classes := (finite_class_iff (pos04RawBridge .positive) released_source_coverage
    pos04_bridge_raw_laws.2.1 KState.p1w0 KState.p1w1).mp eq
  exact (c2_split_each_tag .source).2 classes
-- Class (b): the already-declared repeated M class gives distinct actual representatives of one predictive quotient.
theorem released_nonidentity_partition :
    KState.p0w0≠KState.p0w1 ∧ sourceEquivalent (pos04RawBridge .positive) KState.p0w0 KState.p0w1 := by
  exact ⟨by decide +kernel,class_implies_full _ pos04_bridge_raw_laws.2.1 _ _ (by decide +kernel)⟩
-- Class (b): raw-law return yields an actual bijection of the released finite predictive quotients.
theorem released_finite_bridge_bijective :
    Function.Injective (finiteBridge (pos04RawBridge .positive) released_map_laws (classQueries (pos04RawBridge .positive))) ∧
    Function.Surjective (finiteBridge (pos04RawBridge .positive) released_map_laws (classQueries (pos04RawBridge .positive))) :=
  ⟨finite_bridge_injective _ _ _,finite_bridge_surjective _ _ _ released_target_coverage⟩
end CSTTT.FallbackTheory.ReleasedPredictiveQuotient
