import CSTTT.Targets.GenericHandoff.NativeComposition.ExposureRepair

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePrivacyKernelPrototype
open RegisterInterpreter
set_option autoImplicit false
abbrev Kernel := Bool × Bool
def kernelStates : List Kernel := [(false,false),(false,true),(true,false),(true,true)]
def embed (s : Kernel) : Factor := (false,s)
def nativeNext (s : Factor) (action : Bool) : Factor :=
  if s.1 then s else if action then (if s.2.1 then (false,false,s.2.2) else (true,false,s.2.2))
  else (false,!s.2.1,s.2.2)
def nativeRows (s : Factor) (action : Bool) : List (Factor × Nat) := [(nativeNext s action,1)]
def nativeLabels (s : Factor) : Nat := if s.1 then 2 else bit s.2.1
def nativeInput (owner : Owner) : Input :=
  {canonicalInput owner with temporal := {factorData owner with
    rows := nativeRows,positions := fun _ => 0,hazards := Prod.fst,classes := nativeLabels,
    publishedP := fun s t => if nativeNext s false=t then 1 else 0,
    histories := fun s => [s,nativeNext s false]}}
def destination (o : Factor) : Option Kernel := if o.1 then none else some o.2
def start : Kernel := (false,false)
def finish : Kernel := (true,false)
def labels (s : Kernel) : Nat := bit s.1
def clause : ProfileRules.ClauseSchema Kernel Bool Factor :=
  ⟨⟨kernelStates,[false,true],destination,fun _ => 2,[0,1,2],(start,finish),(1,2,2),1⟩,factors,1,labels⟩
def schema : ExposureRules.Schema Kernel Bool Factor Unit := ⟨clause,()⟩
-- Connector states are computed from actual supported native outcomes.
def connector (i : Input) : List Kernel :=
  start :: (i.temporal.rows (embed start) false).filterMap (fun edge => destination edge.1)
def data (i : Input) : ExposureRules.Raw Kernel Bool Factor Unit :=
  ⟨(fun s => i.temporal.rows (embed s)),(fun s => i.temporal.positions (embed s)),i.temporal.hazards,
    [.position,.availability],(fun _ => false),(fun _ => connector i),(fun s => i.temporal.classes (embed s))⟩
def profile (i : Input) := ExposureRules.profile schema (data i)
-- Stronger class(b) C4 repair replaces the contradictory exposure conjunct.
def FullPrivacy (d : ExposureRules.Raw Kernel Bool Factor Unit) : Prop :=
  ExposureRules.Gate schema d ∧ ExposureRules.Collision schema d ∧ ExposureRules.Connector schema d ∧
    ExposureRules.FullNonExposure schema d ∧ d.channels≠[]

-- Actual native future probes include out-of-kernel exits. No supplied M map.
def future : Factor → List Bool → Bool
  | state,[] => state.1
  | state,action::rest => future (nativeNext state action) rest

theorem native_labels_equivalence (s t : Factor) : nativeLabels s=nativeLabels t ↔
    s.1=t.1 ∧ (s.1=false → s.2.1=t.2.1) := by
  rcases s with ⟨p,v,j⟩; rcases t with ⟨q,w,k⟩
  cases p <;> cases v <;> cases q <;> cases w <;> decide +kernel +revert

theorem native_future_bisim (s t : Factor) (equal : nativeLabels s=nativeLabels t) (action : Bool) :
    nativeLabels (nativeNext s action)=nativeLabels (nativeNext t action) := by
  obtain ⟨hp,hv⟩ := (native_labels_equivalence s t).mp equal
  rcases s with ⟨p,v,j⟩; rcases t with ⟨q,w,k⟩
  cases p <;> cases q <;> cases v <;> cases w <;> cases action <;> simp_all [nativeNext,nativeLabels,bit]

theorem all_future_from_labels (s t : Factor) (equal : nativeLabels s=nativeLabels t) (word : List Bool) :
    future s word=future t word := by
  induction word generalizing s t with
  | nil => exact (native_labels_equivalence s t).mp equal |>.1
  | cons action rest ih => exact ih _ _ (native_future_bisim s t equal action)

theorem kernel_all_future_exact (s t : Kernel) :
    (∀ word,future (embed s) word=future (embed t) word) ↔ s.1=t.1 := by
  constructor
  · intro allWords
    have probe := allWords [true]
    cases s with | mk v j => cases t with | mk w k =>
      cases v <;> cases w <;> simp_all [future,embed,nativeNext]
  · intro same word
    apply all_future_from_labels
    simp [nativeLabels,embed,same]

theorem kernel_mem (s : Kernel) : s∈kernelStates := by
  rcases s with ⟨v,j⟩; cases v <;> cases j <;> decide +kernel +revert

theorem domain : ProfileRules.DomainCheck clause := by
  refine ⟨by decide +kernel +revert,by decide +kernel +revert,by decide +kernel +revert,kernel_mem,?_,factor_mem⟩
  intro action; cases action <;> simp [clause]

theorem actual_prediction (owner : Owner) (s : Kernel) :
    ExposureRules.predictive schema (data (nativeInput owner)) s=(0,[[false],[!s.1]]) := by
  rcases s with ⟨v,j⟩; cases v <;> rfl

theorem actual_prediction_exact (owner : Owner) (s t : Kernel) :
    ExposureRules.predictive schema (data (nativeInput owner)) s=
      ExposureRules.predictive schema (data (nativeInput owner)) t ↔ s.1=t.1 := by
  rw [actual_prediction,actual_prediction]
  rcases s with ⟨v,j⟩; rcases t with ⟨w,k⟩
  cases v <;> cases w <;> decide +kernel +revert

theorem actual_prediction_all_future (owner : Owner) (s t : Kernel) :
    ExposureRules.predictive schema (data (nativeInput owner)) s=
      ExposureRules.predictive schema (data (nativeInput owner)) t ↔
      ∀ word,future (embed s) word=future (embed t) word := by
  rw [actual_prediction_exact,kernel_all_future_exact]

theorem actual_current_constant (owner : Owner) (s t : Kernel) :
    ExposureRules.current schema (data (nativeInput owner)) s=ExposureRules.current schema (data (nativeInput owner)) t := by
  rcases s with ⟨v,j⟩; rcases t with ⟨w,k⟩
  cases v <;> cases w <;> rfl

theorem actual_nonexposure (owner : Owner) :
    ExposureRules.FullNonExposure schema (data (nativeInput owner)) := by
  rintro ⟨channel,member,⟨s,t,different⟩,_⟩
  have alternatives : channel=.position ∨ channel=.availability := by simpa [data] using member
  rcases alternatives with rfl|rfl
  · exact different rfl
  · exact different (by rcases s with ⟨v,j⟩; rcases t with ⟨w,k⟩; cases v <;> cases w <;> rfl)

theorem actual_linked (owner : Owner) : ProfileRules.Linked clause (profile (nativeInput owner))
    (data (nativeInput owner)).classes := by
  refine ⟨rfl,?_⟩
  intro s t
  change ExposureRules.predictive schema (data (nativeInput owner)) s=ExposureRules.predictive schema (data (nativeInput owner)) t ↔ (data (nativeInput owner)).classes s=(data (nativeInput owner)).classes t
  rw [actual_prediction_exact]
  rcases s with ⟨v,j⟩; rcases t with ⟨w,k⟩
  cases v <;> cases w <;> decide +kernel +revert

theorem actual_first (owner : Owner) : ProfileRules.first (profile (nativeInput owner))=labels := by
  funext s
  rcases s with ⟨v,j⟩; cases v <;> cases j <;> decide +kernel +revert

theorem actual_second (owner : Owner) : ProfileRules.second (profile (nativeInput owner))=labels := by
  change ProfileRules.step (profile (nativeInput owner)) (ProfileRules.first (profile (nativeInput owner)))=labels
  rw [actual_first]
  funext s
  rcases s with ⟨v,j⟩; cases v <;> cases j <;> decide +kernel +revert

theorem actual_recursive_profile (owner : Owner) : ProfileRules.RecursiveProfile (profile (nativeInput owner)) := by
  unfold ProfileRules.RecursiveProfile
  rw [actual_first,actual_second]
  refine ⟨by decide +kernel +revert,by decide +kernel +revert,by decide +kernel +revert,?_,?_⟩
  · intro s t; rfl
  · intro s t
    exact ((actual_linked owner).2 s t).symm

theorem actual_stable_profile (owner : Owner) : ProfileRules.StableProfile (profile (nativeInput owner)) := by
  have fixed : ProfileRules.step (profile (nativeInput owner)) labels=labels := by
    have second := actual_second owner
    change ProfileRules.step (profile (nativeInput owner)) (ProfileRules.first (profile (nativeInput owner)))=labels at second
    rwa [actual_first] at second
  refine ⟨actual_recursive_profile owner,?_,?_,?_⟩
  · rw [actual_second]; exact fixed
  · rw [actual_first]
    exact (ProfileRules.block_coverage_iff _ _).mp (by clear fixed; decide +kernel +revert)
  · rw [actual_second]
    exact (ProfileRules.block_coverage_iff _ _).mp (by clear fixed; decide +kernel +revert)

theorem actual_promotion (owner : Owner) : ProfileRules.Promotion (profile (nativeInput owner)) := by
  unfold ProfileRules.Promotion
  decide +kernel +revert

theorem actual_collision (owner : Owner) : ExposureRules.Collision schema (data (nativeInput owner)) := by
  exact ⟨actual_current_constant owner start finish,by rw [actual_prediction,actual_prediction]; decide +kernel +revert⟩

theorem actual_gate (owner : Owner) : ExposureRules.Gate schema (data (nativeInput owner)) := by
  refine ⟨domain,?_,actual_linked owner,by decide +kernel +revert,by decide +kernel +revert,by decide +kernel +revert⟩
  simp only [ProfileRules.RowsValid]
  decide +kernel +revert

theorem actual_connector (owner : Owner) : ExposureRules.Connector schema (data (nativeInput owner)) := by
  refine ⟨?_,actual_collision owner⟩
  decide +kernel +revert

theorem actual_full_privacy (owner : Owner) : FullPrivacy (data (nativeInput owner)) :=
  ⟨actual_gate owner,actual_collision owner,actual_connector owner,actual_nonexposure owner,by decide +kernel +revert⟩

theorem old_surrogate_rejected (owner : Owner) :
    ¬ExposureRules.SurrogateAccept schema (data (nativeInput owner)) :=
  fun accepted => actual_nonexposure owner accepted.2.2.2

def revealPredictive (d : ExposureRules.Raw Kernel Bool Factor Unit) := {d with channels:=d.channels++[ExposureRules.Channel.predictive]}
theorem revealed_exposed (d : ExposureRules.Raw Kernel Bool Factor Unit) (collision : ExposureRules.Collision schema d) :
    ExposureRules.Exposed schema (revealPredictive d) := by
  refine ⟨.predictive,by simp [revealPredictive],⟨start,finish,?_⟩,?_⟩
  · intro equal
    exact collision.2 (by simpa [ExposureRules.channel,ExposureRules.predictive,ExposureRules.profile,revealPredictive,schema,clause] using equal)
  · intro s t equal
    simp only [ExposureRules.channel]
    rw [equal]

theorem revealed_privacy_rejected (d : ExposureRules.Raw Kernel Bool Factor Unit) (privacy : FullPrivacy d) :
    ¬FullPrivacy (revealPredictive d) := fun revealed => revealed.2.2.2.1 (revealed_exposed d privacy.2.1)

-- Actual maintained support: every safe native step remains inside the kernel.
def safeSteps : Factor → Nat → Factor
  | state,0 => state
  | state,n+1 => safeSteps (nativeNext state false) n
theorem safe_kernel_forever (s : Kernel) (n : Nat) : (safeSteps (embed s) n).1=false := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih (!s.1,s.2)

def viabilitySchema (owner : Owner) : OperationalViability.Schema Kernel Bool Factor Owner :=
  ⟨kernelStates,[false,true],destination,1,owner,⟨1,1,1⟩,(fun s t => if (!s.1,s.2)=t then 1 else 0)⟩
def viabilityData (i : Input) : OperationalViability.Raw Kernel Bool Factor Owner :=
  ⟨(fun s => i.temporal.rows (embed s)),(fun _ => false),i.temporal.resource,i.temporal.ledger⟩
theorem viability_domain (owner : Owner) : OperationalViability.DomainCheck (viabilitySchema owner) := by
  refine ⟨by decide +kernel +revert,kernel_mem,by decide +kernel +revert,?_,by decide +kernel +revert,by decide +kernel +revert⟩
  intro action; cases action <;> simp [viabilitySchema]
theorem kernel_viable (owner : Owner) : ViableSet.Viable
    (OperationalViability.retain (viabilitySchema owner) (viabilityData (nativeInput owner))) kernelStates := by
  intro s member
  rcases s with ⟨v,j⟩; cases v <;> cases j <;> decide +kernel +revert
theorem greatest_kernel_contains (owner : Owner) (s : Kernel) :
    s∈OperationalViability.greatest (viabilitySchema owner) (viabilityData (nativeInput owner)) :=
  OperationalViability.greatest_contains _ _ kernel_mem kernelStates (kernel_viable owner) (kernel_mem s)
theorem actual_viability (owner : Owner) : OperationalViability.Accept (viabilitySchema owner) (viabilityData (nativeInput owner)) := by
  refine ⟨viability_domain owner,?_,by decide +kernel +revert,by simp [OperationalViability.LedgerCheck,OperationalViability.budgetAfter,viabilityData,nativeInput,canonicalInput,factorData,viabilitySchema],?_⟩
  · intro empty
    have member := greatest_kernel_contains owner start
    simp [empty] at member
  · intro s hs t ht
    simp [OperationalViability.weight,viabilitySchema,viabilityData,nativeInput,canonicalInput,factorData,nativeRows,nativeNext,embed,destination]
def unfunded (i : Input) : Input := {i with temporal:={i.temporal with resource:={i.temporal.resource with rechargeAvailable:=false}}}
theorem unfunded_kernel_empty (owner : Owner) :
    OperationalViability.greatest (viabilitySchema owner) (viabilityData (unfunded (nativeInput owner)))=[] := by
  apply OperationalViability.unavailable_empty _ _ kernel_mem
  simp [OperationalViability.available,viabilityData,unfunded]

-- All consumed raw fields belong to the selected actual input pair.
def bindings (cell : Owner) (copy : Bool) : ExposureRules.Bindings Owner MemoryValue Kernel Bool Factor Unit :=
  let get := MemoryFrames.selectInput copy
  ⟨⟨cell,fun pair s => (get pair).temporal.rows (embed s)⟩,
    ⟨cell,fun pair s => (get pair).temporal.positions (embed s)⟩,
    ⟨cell,fun pair => (get pair).temporal.hazards⟩,
    ⟨cell,fun _ => [.position,.availability]⟩,⟨cell,fun _ _ => false⟩,
    ⟨cell,fun pair _ => connector (get pair)⟩,
    ⟨cell,fun pair s => (get pair).temporal.classes (embed s)⟩⟩
theorem decoded (cell : Owner) (copy : Bool) (assignment : Assignment Owner MemoryValue) :
    ExposureRules.decoded (bindings cell copy) assignment=
      (assignment cell).map (fun pair => data (MemoryFrames.selectInput copy pair)) := by
  cases h : assignment cell <;> simp [ExposureRules.decoded,bindings,CellView.read,h,data]
noncomputable def privacyBit (d : ExposureRules.Raw Kernel Bool Factor Unit) : Bool := by
  classical
  exact decide (FullPrivacy d)
noncomputable def readout (cell : Owner) (copy : Bool) (assignment : Assignment Owner MemoryValue) : Option Bool := by
  classical
  exact (ExposureRules.decoded (bindings cell copy) assignment).map privacyBit
theorem readout_some_exact (cell : Owner) (copy : Bool) (assignment : Assignment Owner MemoryValue) (value : Bool) :
    readout cell copy assignment=some value ↔ ∃ pair,assignment cell=some pair ∧
      value=privacyBit (data (MemoryFrames.selectInput copy pair)) := by
  classical
  cases assigned : assignment cell <;> simp [readout,decoded,assigned,eq_comm]
theorem readout_true_exact (cell : Owner) (copy : Bool) (assignment : Assignment Owner MemoryValue) :
    readout cell copy assignment=some true ↔ ∃ pair,assignment cell=some pair ∧
      FullPrivacy (data (MemoryFrames.selectInput copy pair)) := by
  classical
  rw [readout_some_exact]
  simp [privacyBit]
theorem readout_false_exact (cell : Owner) (copy : Bool) (assignment : Assignment Owner MemoryValue) :
    readout cell copy assignment=some false ↔ ∃ pair,assignment cell=some pair ∧
      ¬FullPrivacy (data (MemoryFrames.selectInput copy pair)) := by
  classical
  rw [readout_some_exact]
  simp [privacyBit]
theorem readout_none_exact (cell : Owner) (copy : Bool) (assignment : Assignment Owner MemoryValue) :
    readout cell copy assignment=none ↔ assignment cell=none := by
  classical
  cases assigned : assignment cell <;> simp [readout,decoded,assigned]
theorem data_publish (i : Input) : data (publish i)=data i := rfl
theorem published_readout (cell : Owner) (assignment : Assignment Owner MemoryValue) :
    readout (swapOwner cell) true (memoryImage assignment)=readout cell false assignment := by
  classical
  simp only [readout,decoded]
  have mapped := congrArg (fun selected : Option Input => selected.map data) (published_source assignment cell)
  have equal : (memoryImage assignment (swapOwner cell)).map (fun pair => data (MemoryFrames.selectInput true pair))=
      (assignment cell).map (fun pair => data (MemoryFrames.selectInput false pair)) := by
    simpa [sourceInputs,currentInputs,MemoryFrames.selectInput,Option.map_map] using mapped
  rw [equal]

-- Read the actual optional singleton row and its positive support before folding.
def rawStep (i : Input) (state : Factor) (action : Bool) : Option Factor :=
  match i.temporal.rows state action with
  | [(next,weight)] => if 0<weight then some next else none
  | _ => none
def rawFuture (i : Input) : Factor → List Bool → Option Bool
  | state,[] => some (i.temporal.hazards state)
  | state,action::rest => (rawStep i state action).bind (fun next => rawFuture i next rest)
theorem actual_raw_step (owner : Owner) (state : Factor) (action : Bool) :
    rawStep (nativeInput owner) state action=some (nativeNext state action) := rfl
theorem actual_raw_future (owner : Owner) (state : Factor) (word : List Bool) :
    rawFuture (nativeInput owner) state word=some (future state word) := by
  induction word generalizing state with
  | nil => rfl
  | cons action rest ih => simp [rawFuture,actual_raw_step,ih,future]
theorem actual_raw_future_exact (owner : Owner) (s t : Kernel) :
    (∀ word,rawFuture (nativeInput owner) (embed s) word=rawFuture (nativeInput owner) (embed t) word) ↔
      ExposureRules.predictive schema (data (nativeInput owner)) s=ExposureRules.predictive schema (data (nativeInput owner)) t := by
  simp only [actual_raw_future,Option.some.injEq]
  exact (actual_prediction_all_future owner s t).symm

-- Every decoder of the COMPLETE current channel tuple is constant, so joint
-- current instrumentation cannot undo the declared non-exposure result.
theorem every_current_decoder_constant {Y : Type} (owner : Owner)
    (decoder : List ((Nat × List Bool) × Option (Nat × List (List Bool))) → Y) (s t : Kernel) :
    decoder (ExposureRules.current schema (data (nativeInput owner)) s)=
      decoder (ExposureRules.current schema (data (nativeInput owner)) t) :=
  congrArg decoder (actual_current_constant owner s t)
theorem no_current_decoder_exposes {Y : Type} (owner : Owner)
    (decoder : List ((Nat × List Bool) × Option (Nat × List (List Bool))) → Y) :
    ¬∃ s t,decoder (ExposureRules.current schema (data (nativeInput owner)) s)≠
      decoder (ExposureRules.current schema (data (nativeInput owner)) t) := by
  rintro ⟨s,t,different⟩
  exact different (every_current_decoder_constant owner decoder s t)

def assigned : Assignment Owner MemoryValue := fun owner => some (nativeInput owner,nativeInput owner)
theorem actual_assigned_readout (owner : Owner) (copy : Bool) : readout owner copy assigned=some true := by
  apply (readout_true_exact _ _ _).mpr
  refine ⟨(nativeInput owner,nativeInput owner),rfl,?_⟩
  cases copy <;> exact actual_full_privacy owner
-- Exact finite coherent C2/C3/C4/maintained-kernel return, not full8Pkg.
theorem same_native_kernel_return (owner : Owner) :
    readout owner false assigned=some true ∧
    ProfileRules.Promotion (profile (nativeInput owner)) ∧
    ProfileRules.StableProfile (profile (nativeInput owner)) ∧
    OperationalViability.Accept (viabilitySchema owner) (viabilityData (nativeInput owner)) ∧
    (∀ s t,(∀ word,rawFuture (nativeInput owner) (embed s) word=rawFuture (nativeInput owner) (embed t) word) ↔ s.1=t.1) ∧
    ExposureRules.current schema (data (nativeInput owner)) start=ExposureRules.current schema (data (nativeInput owner)) finish ∧
    rawFuture (nativeInput owner) (embed start) [true]≠rawFuture (nativeInput owner) (embed finish) [true] ∧
    rawStep (nativeInput owner) (embed start) false=some (embed finish) := by
  refine ⟨actual_assigned_readout owner false,actual_promotion owner,actual_stable_profile owner,actual_viability owner,?_,
    actual_current_constant owner start finish,?_,rfl⟩
  · intro s t
    simp only [actual_raw_future,Option.some.injEq]
    exact kernel_all_future_exact s t
  · rw [actual_raw_future,actual_raw_future]
    decide +kernel +revert

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePrivacyKernelPrototype
