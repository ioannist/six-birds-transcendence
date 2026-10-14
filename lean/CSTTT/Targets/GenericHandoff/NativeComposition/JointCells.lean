import CSTTT.Targets.GenericHandoff.NativeComposition.PackageBundle
import CSTTT.Targets.GenericHandoff.JointHistoryTransport

/-! C7 recombination surrogate consumes actual native histories, safe rows,
receiver and events alongside independently declared primitive coupling tables.
The hidden paths coincide branchwise but their joint displays differ. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeJointCells
open RegisterInterpreter NativePackagePrimitives NativePackageBundle

def schema : JointRules.Schema Factor Bool Factor Bool Factor Bool Bool Bool Unit Stage Bool :=
  ⟨factors,[false,true],factors,factors,[false,true],[false,true],[false,true],(false,true),(),coupling,2,true,
    some,1,fun s t => if s=t then 1 else 0⟩
def events (i : Input) : List (JointRules.Event Stage Bool) :=
  i.temporal.events.map (fun e => ⟨e.id,e.fromStage,e.toStage,e.atomic,
    (!e.id && i.receiver.sourcePresent),i.receiver.targetFunded⟩)
def receiver (i : Input) : JointRules.Receiver :=
  ⟨i.receiver.sourcePresent,i.receiver.targetFunded,i.receiver.funded,i.receiver.mixedRequired⟩
def data (b : Bundle) : JointRules.Raw Factor Bool Factor Bool Factor Bool Bool Bool Unit Stage Bool :=
  ⟨b.supplement.joint,b.native.temporal.rows,b.native.temporal.policy,b.native.temporal.histories,
    b.native.temporal.publishedP,events b.native,b.native.temporal.realized,receiver b.native⟩
def bindings (cell : Owner) (copy : Bool) : JointRules.Bindings Owner NativePackageBundle.Value
    Factor Bool Factor Bool Factor Bool Bool Bool Unit Stage Bool :=
  let get := NativePackageBundle.select copy
  ⟨⟨cell,fun p => (get p).supplement.joint⟩,⟨cell,fun p => (get p).native.temporal.rows⟩,
    ⟨cell,fun p => (get p).native.temporal.policy⟩,⟨cell,fun p => (get p).native.temporal.histories⟩,
    ⟨cell,fun p => (get p).native.temporal.publishedP⟩,⟨cell,fun p => events (get p).native⟩,
    ⟨cell,fun p => (get p).native.temporal.realized⟩,⟨cell,fun p => receiver (get p).native⟩⟩
def canonicalData (cell : Owner) (copy : Bool) := data ⟨AvailabilityPublication.selected cell copy,supplement⟩

theorem decoded (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    JointRules.decoded (bindings cell copy) a=(a cell).map (fun p => data (select copy p)) := by
  cases ha : a cell <;> simp [JointRules.decoded,bindings,CellView.read,ha,data]
theorem acceptance_iff (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    JointRules.AssignedAccept schema (bindings cell copy) a ↔
      ∃ p, a cell=some p ∧ JointRules.SurrogateAccept schema (data (select copy p)) := by
  simp only [JointRules.AssignedAccept,decoded]
  cases a cell <;> simp
theorem missing_rejected (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value)
    (hm : a cell=none) : ¬ JointRules.AssignedAccept schema (bindings cell copy) a := by
  rw [acceptance_iff]
  simp [hm]
theorem publication_source_decoded (a : Assignment Owner NativePackageBundle.Value) (o : Owner) :
    JointRules.decoded (bindings (swapOwner o) true) (NativePackageBundle.image a)=
      JointRules.decoded (bindings o false) a := by
  rw [decoded,decoded]
  have h := congrArg (fun z : Option Bundle => z.map data) (copied_source a o)
  simpa [Option.map_map] using h
theorem publication_source_accept_iff (a : Assignment Owner NativePackageBundle.Value) (o : Owner) :
    JointRules.AssignedAccept schema (bindings (swapOwner o) true) (NativePackageBundle.image a) ↔
      JointRules.AssignedAccept schema (bindings o false) a := by
  simp only [JointRules.AssignedAccept,publication_source_decoded]

theorem domain : JointRules.DomainCheck schema := by
  refine ⟨by decide +kernel,factor_mem,by decide +kernel,?_,by decide +kernel,factor_mem,
    by decide +kernel,factor_mem,by decide +kernel,?_,by decide +kernel,?_,by decide +kernel,?_⟩
  all_goals intro b; cases b <;> decide +kernel
theorem gate (cell : Owner) (copy : Bool) : JointRules.Gate schema (canonicalData cell copy) := by
  refine ⟨domain,by decide +kernel,?_,?_,?_⟩
  · cases cell <;> cases copy <;> simp only [JointRules.RowsValid] <;> decide +kernel
  · cases cell <;> cases copy <;> rfl
  · cases cell <;> cases copy <;> decide +kernel
theorem displays_distinct (cell : Owner) (copy : Bool) :
    JointRules.display schema (canonicalData cell copy) false≠JointRules.display schema (canonicalData cell copy) true := by
  have hn : (JointRules.display schema (canonicalData cell copy) false).head?≠
      (JointRules.display schema (canonicalData cell copy) true).head? := by
    cases cell <;> cases copy <;> decide +kernel
  intro he
  exact hn (congrArg List.head? he)
theorem rule (cell : Owner) (copy : Bool) : JointRules.Rule schema (canonicalData cell copy) := by
  refine ⟨?_,?_,?_,?_⟩
  · cases cell <;> cases copy <;> unfold JointRules.Local <;> decide +kernel
  · cases cell <;> cases copy <;> unfold JointRules.Histories
    all_goals intro h hh; rcases h with ⟨p,v,j⟩
    all_goals cases p <;> cases v <;> cases j <;> rfl
  · refine ⟨by decide +kernel,?_,?_⟩
    · cases cell <;> cases copy <;> rfl
    · intro he; exact displays_distinct cell copy (congrArg Prod.snd he)
  · have hm : JointRules.mixed schema (canonicalData cell copy)=true := by cases cell <;> cases copy <;> rfl
    have ha : JointRules.active schema (canonicalData cell copy)=true := by cases cell <;> cases copy <;> rfl
    refine ⟨hm,ha,?_,?_⟩
    · change JointRules.receiverDisplay schema (canonicalData cell copy) false≠
        JointRules.receiverDisplay schema (canonicalData cell copy) true
      simpa only [JointRules.receiverDisplay,hm,ha,Bool.and_self,ite_true] using displays_distinct cell copy
    · intro s hs t ht
      cases cell <;> cases copy <;> exact AvailabilityFactor.safe_policy_weight false s t
theorem canonical_decoded (cell : Owner) (copy : Bool) :
    JointRules.decoded (bindings cell copy) NativePackageBundle.canonical=some (canonicalData cell copy) := by
  cases cell <;> cases copy <;> rfl
theorem c7 (cell : Owner) (copy : Bool) :
    JointRules.AssignedAccept schema (bindings cell copy) NativePackageBundle.canonical :=
  ⟨_,canonical_decoded cell copy,gate cell copy,rule cell copy⟩

def eraseObservable (b : Bundle) : Bundle :=
  {b with supplement := {b.supplement with joint := {b.supplement.joint with observables := []}}}
theorem erased_actual_displays (b : Bundle) :
    JointRules.receiverDisplay schema (data (eraseObservable b)) false=
      JointRules.receiverDisplay schema (data (eraseObservable b)) true := by
  simp [JointRules.receiverDisplay,JointRules.display,data,eraseObservable]
theorem erased_actual_c7_rejected (b : Bundle) : ¬ JointRules.SurrogateAccept schema (data (eraseObservable b)) :=
  JointRules.equal_displays_rejected _ _ (erased_actual_displays b)
def cutSource (b : Bundle) : Bundle :=
  {b with native := {b.native with receiver := {b.native.receiver with sourcePresent := false}}}
theorem cut_actual_active (b : Bundle) : JointRules.active schema (data (cutSource b))=false := by
  simp [JointRules.active,data,cutSource,receiver]
theorem cut_actual_displays (b : Bundle) :
    JointRules.receiverDisplay schema (data (cutSource b)) false=
      JointRules.receiverDisplay schema (data (cutSource b)) true := by
  simp [JointRules.receiverDisplay,cut_actual_active]
theorem cut_actual_c7_rejected (b : Bundle) : ¬ JointRules.SurrogateAccept schema (data (cutSource b)) :=
  JointRules.equal_displays_rejected _ _ (cut_actual_displays b)

theorem doubled_history_eq_iff {X : Type} (xs ys : List X) : xs++xs=ys++ys ↔ xs=ys := by
  constructor
  · intro he
    have h := congrArg (fun zs : List X => zs.take (zs.length/2)) he
    simpa only [half_double] using h
  · intro he; rw [he]
theorem published_pair_count (b : Bundle) (id : Bool) (l r : Factor) :
    JointRules.pairCount (data (publishBundle b)) id l r=JointRules.pairCount (data b) id l r := by
  simp only [JointRules.pairCount,data,publishBundle,publish,doubled_history_eq_iff]
theorem published_distribution (b : Bundle) (id : Bool) :
    JointRules.distribution schema (data (publishBundle b)) id=JointRules.distribution schema (data b) id := by
  simp only [JointRules.distribution,published_pair_count]
  rfl
def historyImage (xs : List Factor) := xs++xs
theorem history_image_recovered (xs : List Factor) :
    (historyImage xs).take ((historyImage xs).length/2)=xs := half_double xs
theorem published_branchwise (b : Bundle) (id : Bool) :
    JointRules.branchwise schema (data (publishBundle b)) id=
      ((JointRules.branchwise schema (data b) id).1.map historyImage,
        (JointRules.branchwise schema (data b) id).2.map historyImage) := by
  simp [JointRules.branchwise,data,publishBundle,publish,historyImage,List.map_map,Function.comp_def]
theorem actual_history_transport (b : Bundle) :
    JointHistoryTransport.Transport schema schema (data b) (data (publishBundle b)) historyImage := by
  refine ⟨rfl,?_⟩
  intro id hi
  exact ⟨(published_branchwise b id).symm,rfl,(published_distribution b id).symm⟩
theorem published_receiver_display (b : Bundle) (id : Bool) :
    JointRules.receiverDisplay schema (data (publishBundle b)) id=JointRules.receiverDisplay schema (data b) id := by
  simp only [JointRules.receiverDisplay,JointRules.mixed,JointRules.active,JointRules.display,data,
    publishBundle,events,receiver,publish]
  exact congrArg (fun dist => if JointRules.mixed schema (data b) && JointRules.active schema (data b) then
      if () ∈ b.supplement.joint.observables then dist else [] else []) (published_distribution b id)

/-- The old state-by-state branch transport cannot encode an actual doubled
history. Preserve that parent and use a history encoding in the stronger return. -/
theorem original_state_transport_rejected (stateMap : Factor → Factor) :
    ¬ JointRules.Transport schema schema (canonicalData true true) (canonicalData true false) stateMap := by
  intro ht
  have hb := (ht.2 false (by decide +kernel)).1
  have hl := congrArg (fun p : List (List Factor) × List (List Factor) => p.1.head?.map List.length) hb
  simp only [JointRules.branchwise,canonicalData,data,schema,AvailabilityPublication.selected,
    List.map_cons,List.map_nil,List.head?_cons,Option.map_some,List.length_map] at hl
  change some 2=some 4 at hl
  cases hl

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeJointCells
