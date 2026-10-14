import CSTTT.Targets.GenericHandoff.POS04RouteExecution

/-! Independently stated semantic route readout. The readout uses actual
source execution, the coordinate receiver, all target response branches, raw
path identity, a shared arrival endpoint, and retained registers/readouts.
It does not add package/interface bookkeeping to obtain gate equivalence.
The exact adapter includes completeness for precisely the consumed primitives
and applies to arbitrary partial assignments. Full named-lineage equivalence
is still pending; this is its route component, not the whole lineage readout.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RouteReadout
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04RegisterDynamics
open POS04RouteExecution
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def residueFor (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId) : List KState × List EventId :=
  (acquisitionHistory a .source r,(pathsFor a r).path)

theorem expected_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) (r : RouteId) :
    RouteComponent.expected routeRaw a r = some (residueFor a r) := by
  unfold RouteComponent.expected
  dsimp only [routeRaw]
  rw [words_read a hc,routes_read a hc]
  simp only [provenance,StaticView.read,Expr.eval]
  rw [cell_value (hc .histories (by simp [dependencies])),
    cell_value (hc .routeTable (by simp [dependencies]))]
  apply congrArg some
  dsimp only [pathsFor]
  rw [POS04ExecutionFrontier.source_path]
  rfl

theorem path_identity_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) (r : RouteId) :
    RouteComponent.pathIdentity routeRaw a r = some (wordFor a r,(pathsFor a r).path) := by
  unfold RouteComponent.pathIdentity
  dsimp only [routeRaw]
  rw [words_read a hc,routes_read a hc]
  rfl

theorem register_eq (a : CSTTT.POS04.Assigned.Assignment) (x : Registers Unit FrameValue) :
    routeRaw.register.eval a x () = some ((x ()).2.residue) := rfl
theorem probe_eq (a : CSTTT.POS04.Assigned.Assignment) (x : Registers Unit FrameValue) :
    routeRaw.readout.eval a x () =
      some ((x ()).2.residue.1.head?.map (fun s => ambientPhase (.inK s))) := rfl
theorem endpoint_eq (a : CSTTT.POS04.Assigned.Assignment) (x : Registers Unit FrameValue) :
    routeRaw.endpoint.eval a x () = some ((x ()).1,(x ()).2.factor) := rfl
theorem owner_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (x : Registers Unit FrameValue) :
    routeRaw.owner.eval a x () = some (tagCarrierId ((a (.resources .target)).getD
      (canonicalValue (.resources .target))).owner) := by
  simp only [routeRaw,Expr.eval]
  rw [cell_value (hc (.resources .target) (by simp [dependencies]))]
  rfl

def RetainedReadout (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId)
    (probe : Nat) (endpoint : Tag × Ambient) : Prop :=
  (∃ entry, ResultReadout a r entry) ∧
  (∀ arrived, ArrivalReadout a r arrived → ((arrived ()).1,(arrived ()).2.factor) = endpoint) ∧
  (∀ entry, ResultReadout a r entry →
    (entry ()).2.residue = residueFor a r ∧
    (entry ()).2.residue.1.head?.map (fun s => ambientPhase (.inK s)) = some probe ∧
    tagCarrierId ((a (.resources .target)).getD (canonicalValue (.resources .target))).owner = tagCarrierId .target)

theorem retained_readout_iff (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a)
    (r : RouteId) (probe : Nat) (endpoint : Tag × Ambient) :
    RouteComponent.Retained POS04ExecutionFrontier.schema routeRaw a (ready a hc)
      r (residueFor a r) probe endpoint ↔ RetainedReadout a r probe endpoint := by
  change (RouteComponent.expected routeRaw a r = some (residueFor a r) ∧
    (∃ entry, RouteComponent.Result POS04ExecutionFrontier.schema routeRaw a (ready a hc) r entry) ∧
    (∀ arrived, AcquisitionExecution.Arrival POS04ExecutionFrontier.schema acquisition a (ready a hc) r arrived →
      routeRaw.endpoint.eval a arrived () = some endpoint) ∧
    (∀ entry, RouteComponent.Result POS04ExecutionFrontier.schema routeRaw a (ready a hc) r entry →
      routeRaw.register.eval a entry () = some (residueFor a r) ∧
      routeRaw.readout.eval a entry () = some (some probe) ∧
      routeRaw.owner.eval a entry () = some (tagCarrierId .target))) ↔ _
  simp only [expected_eq a hc,true_and,
    result_readout_iff a hc,arrival_readout_iff a hc,endpoint_eq,register_eq,probe_eq,owner_eq a hc,
    Option.some.injEq]
  rfl

/-- Semantic comparison keeps distinct RAW paths, a shared computed endpoint,
and EVERY support branch, not just a selected `ExecutedMemory` witness. -/
def RouteReadout (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  ∃ r s, r ∈ routeIds ∧ s ∈ routeIds ∧ r ≠ s ∧
    (wordFor a r,(pathsFor a r).path) ≠ (wordFor a s,(pathsFor a s).path) ∧
    residueFor a r ≠ residueFor a s ∧
    ∃ nr ns endpoint, nr ≠ ns ∧
      RetainedReadout a r nr endpoint ∧ RetainedReadout a s ns endpoint

theorem route_readout_iff (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    RoutePass a ↔ RouteReadout a := by
  constructor
  · rintro ⟨h,r,s,hr,hs,hrs,hpath,rr,sr,nr,ns,endpoint,hres,hprobe,hret,hset⟩
    have er := hret.1
    have es := hset.1
    rw [expected_eq a hc] at er es
    have er' := Option.some.inj er
    have es' := Option.some.inj es
    subst rr; subst sr
    rw [path_identity_eq a hc,path_identity_eq a hc] at hpath
    exact ⟨r,s,hr,hs,hrs,(fun he => hpath (congrArg some he)),hres,nr,ns,endpoint,hprobe,
      (retained_readout_iff a hc r nr endpoint).mp hret,
      (retained_readout_iff a hc s ns endpoint).mp hset⟩
  · rintro ⟨r,s,hr,hs,hrs,hpath,hres,nr,ns,endpoint,hprobe,hret,hset⟩
    refine ⟨ready_route a hc,r,s,hr,hs,hrs,?_,residueFor a r,residueFor a s,nr,ns,endpoint,hres,hprobe,
      (retained_readout_iff a hc r nr endpoint).mpr hret,
      (retained_readout_iff a hc s ns endpoint).mpr hset⟩
    rw [path_identity_eq a hc,path_identity_eq a hc]
    exact fun he => hpath (Option.some.inj he)

theorem positive_readout : RouteReadout canonical :=
  (route_readout_iff canonical (canonical_complete _)).mp positive

theorem semantic_status_binding (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    RouteComponent.statusOf POS04ExecutionFrontier.schema routeRaw a = .routeIndexed ↔ RouteReadout a :=
  (status_preserves_full_comparison a).trans (route_readout_iff a hc)

/-- Exact arbitrary-partial adapter. A missing consumed cell rejects; an
unconsumed interface declaration is NOT an extra semantic obligation. -/
theorem route_readout_partial_iff (a : CSTTT.POS04.Assigned.Assignment) :
    RoutePass a ↔ Complete dependencies a ∧ RouteReadout a := by
  constructor
  · intro h
    have hc := (ready_route_iff a).mp h.1
    exact ⟨hc,(route_readout_iff a hc).mp h⟩
  · rintro ⟨hc,hr⟩
    exact (route_readout_iff a hc).mpr hr

theorem semantic_status_partial_binding (a : CSTTT.POS04.Assigned.Assignment) :
    RouteComponent.statusOf POS04ExecutionFrontier.schema routeRaw a = .routeIndexed ↔
      Complete dependencies a ∧ RouteReadout a :=
  (status_preserves_full_comparison a).trans (route_readout_partial_iff a)

/-- Direct semantic failure: no branch of the target response is available,
while the source-history guard in POS04RouteExecution remains positive. -/
theorem erased_target_no_result (r : RouteId) (entry : Registers Unit FrameValue) :
    ¬ ResultReadout erasedTargetRows r entry := by
  rintro ⟨_,_,o,hp,_⟩
  simp [StrategyGame.PositiveSupport,erased_target_row] at hp

theorem erased_target_no_readout : ¬ RouteReadout erasedTargetRows := by
  rintro ⟨r,s,_,_,_,_,_,nr,ns,endpoint,_,hr,_⟩
  obtain ⟨entry,he⟩ := hr.1
  exact erased_target_no_result r entry he

theorem source_absent_no_arrival (a : CSTTT.POS04.Assigned.Assignment)
    (input : Receiver) (hi : a .receiverInput = some input) (absent : input.sourcePresent = false)
    (r : RouteId) (arrived : Registers Unit FrameValue) : ¬ ArrivalReadout a r arrived := by
  rintro ⟨_,_,ha,_⟩
  have he : (POS04RouteExecution.receiverFor a).sourcePresent = false := by
    simp [POS04RouteExecution.receiverFor,hi,absent]
  unfold AcquisitionExecution.Activated at ha
  rw [he] at ha
  simp at ha

theorem source_absent_no_readout (a : CSTTT.POS04.Assigned.Assignment)
    (input : Receiver) (hi : a .receiverInput = some input) (absent : input.sourcePresent = false) :
    ¬ RouteReadout a := by
  rintro ⟨r,s,_,_,_,_,_,nr,ns,endpoint,_,hr,_⟩
  obtain ⟨entry,he⟩ := hr.1
  exact source_absent_no_arrival a input hi absent r _ he.1

/-- Regression from G6c: reverse the two distinct raw pasts, without fixing
either route's output to a baseline number in the generic gate. -/
def reversed : CSTTT.POS04.Assigned.Assignment := image reversedHistories.assignment

theorem reversed_complete : Complete dependencies reversed := by
  intro k hk
  cases k with
  | rows t => cases t <;> rfl
  | lower t => cases t <;> rfl
  | protocols t => cases t <;> rfl
  | ticks t => cases t <;> rfl
  | joint t => cases t <;> rfl
  | resources t => cases t <;> rfl
  | _ => rfl

theorem reversed_arrival_readout (r : RouteId) :
    ArrivalReadout reversed r (frame .target (arrivalRun reversed r)) := by
  have hp := (arrival_readout_iff canonical (canonical_complete _) r _).mp (canonical_arrival r)
  refine ⟨hp.1,?_,?_,?_,rfl⟩
  · exact hp.2.1
  · exact hp.2.2.1
  · cases r <;> decide +kernel

theorem reversed_result (r : RouteId) :
    ResultReadout reversed r (frame .target
      (actualUpdate6 (runInputs6 reversed .target) (arrivalRun reversed r)
        (responseAction reversed (arrivalRun reversed r)) (.inK .p2w1))) := by
  refine ⟨reversed_arrival_readout r,?_,.inK .p2w1,?_,rfl⟩
  · unfold StrategyGame.Normalized
    refine ⟨?_,?_,.inK .p2w1,1,?_,by decide⟩
    · cases r <;> decide +kernel
    · cases r <;> decide +kernel
    · cases r <;> decide +kernel
  · exact ⟨1,by cases r <;> decide +kernel,by decide⟩

def reversedProbe : RouteId → Nat | .a => 1 | .b => 0

theorem reversed_retained (r : RouteId) :
    RetainedReadout reversed r (reversedProbe r) (.target,.inK .p1w0) := by
  refine ⟨⟨_,reversed_result r⟩,?_,?_⟩
  · intro arrived ha
    rw [ha.2.2.2.2]
    cases r <;> rfl
  · rintro entry ⟨_,_,o,_,hu⟩
    rw [hu]
    cases r <;> exact ⟨rfl,rfl,rfl⟩

theorem reversed_readout : RouteReadout reversed := by
  refine ⟨.a,.b,by decide,by decide,by decide,by decide,by decide,1,0,
    (.target,.inK .p1w0),by decide,reversed_retained .a,reversed_retained .b⟩

theorem reversed_pass : RoutePass reversed :=
  (route_readout_partial_iff reversed).mpr ⟨reversed_complete,reversed_readout⟩

/-- Sensitivity for EVERY consumed dependency, at the route component itself. -/
theorem missing_dependency_rejected (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ dependencies) : ¬ RoutePass (put a k none) := by
  intro h
  have hc := (route_readout_partial_iff _).mp h
  have present := hc.1 k hk
  simp at present

theorem interface_not_consumed : Cell.interface ∉ dependencies := by decide
theorem hazards_not_consumed : Cell.hazards ∉ dependencies := by decide
theorem writer_not_consumed : Cell.writers ∉ dependencies := by decide

end CSTTT.TargetTheory.GenericHandoff.POS04RouteReadout
