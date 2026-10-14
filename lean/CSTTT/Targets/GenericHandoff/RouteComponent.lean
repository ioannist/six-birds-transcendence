import CSTTT.Targets.GenericHandoff.AcquisitionExecution
import CSTTT.Temporal.Signature

/-! Executed route comparison for generic raw handoffs. A result is an actual
activated arrival followed by a normalized positive-support response and the
shared updater. The register, owner and future probe are read AFTER that step.
The provenance encoder is a raw typed instruction over assigned histories and
paths, not a supplied route name or desired endpoint/readout. All resulting
support branches must retain it. No comparison pair ever means flatness.
The full closure-wide register laws remain a separate execution/game gate. -/
namespace CSTTT.TargetTheory.GenericHandoff.RouteComponent
open RegisterInterpreter

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O Stage Id History RouteId Residue Endpoint : Type) where
  acquisition : AcquisitionExecution.Raw Cell Value R RV D A O Stage Id History RouteId
  provenance : StaticView Cell Value (History → List (D × A × O) → List Id → Residue)
  register : Expr Cell Value R RV Unit Residue
  readout : Expr Cell Value R RV Unit (Option Nat)
  owner : Expr Cell Value R RV Unit CarrierId
  endpoint : Expr Cell Value R RV Unit Endpoint

variable {Cell R D A O Stage Id History RouteId Residue Endpoint : Type}
    {Value : Cell → Type} {RV : R → Type} [DecidableEq Stage]

abbrev Config (Stage Id History RouteId : Type) := AcquisitionExecution.Schema Stage Id History RouteId

def scope (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint) :=
  raw.provenance.dependencies ++ raw.register.dependencies ++ raw.readout.dependencies ++
    raw.owner.dependencies ++ raw.endpoint.dependencies

def Ready (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) : Prop :=
  AcquisitionExecution.Ready raw.acquisition a ∧ Complete (scope raw) a

/-- Option bind rejects every missing history, route or encoder input. -/
def expected (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (r : RouteId) : Option Residue := do
  let hist ← raw.acquisition.histories.read a
  let routes ← raw.acquisition.routes.read a
  let encode ← raw.provenance.read a
  pure (encode (routes r).history (hist (routes r).history) (routes r).path)

def pathIdentity (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (r : RouteId) : Option (List (D × A × O) × List Id) := do
  let hist ← raw.acquisition.histories.read a
  let routes ← raw.acquisition.routes.read a
  pure (hist (routes r).history,(routes r).path)

/-- Route-attributed phase-2 relation: no endpoint, branch or readout is
supplied. The relation uses exactly the acquisition's rows and updater. -/
def Result (cfg : Config Stage Id History RouteId) (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (h : AcquisitionExecution.Ready raw.acquisition a)
    (r : RouteId) (entry : Registers R RV) : Prop :=
  AcquisitionExecution.DomainCheck cfg raw.acquisition ∧ ∃ arrived routes da outcome,
    AcquisitionExecution.Arrival cfg raw.acquisition a h r arrived ∧
    raw.acquisition.routes.read a = some routes ∧
    raw.acquisition.arrivalResponse.eval a arrived ((routes r).history,r) = some da ∧
    da.1 ∈ raw.acquisition.execution.disturbances ∧ da.2 ∈ raw.acquisition.execution.actions ∧
    StrategyGame.Normalized (AcquisitionExecution.rows raw.acquisition a) arrived da.1 da.2 ∧
    StrategyGame.PositiveSupport (AcquisitionExecution.rows raw.acquisition a) arrived da.1 da.2 outcome ∧
    entry = AcquisitionExecution.update raw.acquisition a h arrived da.1 da.2 outcome

theorem result_entry_iff (cfg : Config Stage Id History RouteId) (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (h : AcquisitionExecution.Ready raw.acquisition a) (entry : Registers R RV) :
    (∃ r, Result cfg raw a h r entry) ↔ AcquisitionExecution.Entry cfg raw.acquisition a h entry := by
  constructor
  · rintro ⟨r,hd,arrived,routes,da,o,ha,hr,he,hdd,haa,hn,hp,hu⟩
    exact ⟨hd,r,arrived,routes,da,o,ha,hr,he,hdd,haa,hn,hp,hu⟩
  · rintro ⟨hd,r,arrived,routes,da,o,ha,hr,he,hdd,haa,hn,hp,hu⟩
    exact ⟨r,hd,arrived,routes,da,o,ha,hr,he,hdd,haa,hn,hp,hu⟩

def Retained (cfg : Config Stage Id History RouteId) (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (h : AcquisitionExecution.Ready raw.acquisition a)
    (r : RouteId) (residue : Residue) (read : Nat) (endpoint : Endpoint) : Prop :=
  expected raw a r = some residue ∧
    (∃ entry, Result cfg raw a h r entry) ∧
    (∀ arrived, AcquisitionExecution.Arrival cfg raw.acquisition a h r arrived →
      raw.endpoint.eval a arrived () = some endpoint) ∧
    (∀ entry, Result cfg raw a h r entry →
      raw.register.eval a entry () = some residue ∧ raw.readout.eval a entry () = some (some read) ∧
      raw.owner.eval a entry () = some cfg.target)

/-- Domain membership, actual raw-path distinction, a shared computed
endpoint, nonempty support, and every resulting branch are all gates. -/
def Indexed (cfg : Config Stage Id History RouteId) (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (h : AcquisitionExecution.Ready raw.acquisition a) : Prop :=
  ∃ r s, r ∈ cfg.routes ∧ s ∈ cfg.routes ∧ r ≠ s ∧
    pathIdentity raw a r ≠ pathIdentity raw a s ∧
    ∃ rr sr nr ns endpoint, rr ≠ sr ∧ nr ≠ ns ∧
      Retained cfg raw a h r rr nr endpoint ∧ Retained cfg raw a h s sr ns endpoint

def Pass (cfg : Config Stage Id History RouteId) (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) : Prop := ∃ h : Ready raw a, Indexed cfg raw a h.1

noncomputable def statusOf (cfg : Config Stage Id History RouteId) (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) : CSTTT.RouteStatus := by
  classical
  exact if Pass cfg raw a then .routeIndexed else .unresolved

theorem status_indexed_iff (cfg : Config Stage Id History RouteId) (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) : statusOf cfg raw a = .routeIndexed ↔ Pass cfg raw a := by
  classical
  simp [statusOf]

theorem never_flat (cfg : Config Stage Id History RouteId) (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) : statusOf cfg raw a ≠ .flat := by
  classical
  unfold statusOf
  split <;> decide

/-- Separate missing guards include the response, initializer and updater
through AcquisitionExecution.Ready, not merely the display dependencies. -/
theorem missing_acquisition_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.acquisition.dependencies)
    (hm : a k = none) : ¬ Pass cfg raw a := by
  rintro ⟨h,_⟩
  exact AcquisitionExecution.missing_dependency_rejected raw.acquisition a k hk hm h.1

theorem missing_readout_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ scope raw)
    (hm : a k = none) : ¬ Pass cfg raw a := by
  rintro ⟨h,_⟩
  have hp := h.2 k hk
  rw [hm] at hp
  contradiction

theorem empty_comparison_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (bad : cfg.routes = []) : ¬ Pass cfg raw a := by
  rintro ⟨_,r,s,hr,_⟩
  simp [bad] at hr

theorem constant_paths_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (bad : ∀ r s, pathIdentity raw a r = pathIdentity raw a s) : ¬ Pass cfg raw a := by
  rintro ⟨_,r,s,_,_,_,hp,_⟩
  exact hp (bad r s)

theorem no_result_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value)
    (bad : ∀ (h : AcquisitionExecution.Ready raw.acquisition a) r e, ¬ Result cfg raw a h r e) : ¬ Pass cfg raw a := by
  rintro ⟨h,r,s,_,_,_,_,rr,sr,nr,ns,endpoint,_,_,hr,_⟩
  obtain ⟨entry,he⟩ := hr.2.1
  exact bad h.1 r entry he

theorem constant_register_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (c : Residue)
    (bad : ∀ entry, raw.register.eval a entry () = some c) : ¬ Pass cfg raw a := by
  rintro ⟨_,r,s,_,_,_,_,rr,sr,nr,ns,endpoint,hn,_,hr,hs⟩
  obtain ⟨re,hre⟩ := hr.2.1
  obtain ⟨se,hse⟩ := hs.2.1
  have er : c = rr := Option.some.inj ((bad re).symm.trans (hr.2.2.2 re hre).1)
  have es : c = sr := Option.some.inj ((bad se).symm.trans (hs.2.2.2 se hse).1)
  exact hn (er.symm.trans es)

theorem undefined_probe_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value)
    (bad : ∀ entry, raw.readout.eval a entry () = some none) : ¬ Pass cfg raw a := by
  rintro ⟨_,r,s,_,_,_,_,rr,sr,nr,ns,endpoint,_,_,hr,_⟩
  obtain ⟨re,hre⟩ := hr.2.1
  have er := (hr.2.2.2 re hre).2.1
  rw [bad re] at er
  simp at er

theorem owner_mismatch_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (owner : CarrierId) (hne : owner ≠ cfg.target)
    (bad : ∀ entry, raw.owner.eval a entry () = some owner) : ¬ Pass cfg raw a := by
  rintro ⟨_,r,s,_,_,_,_,rr,sr,nr,ns,endpoint,_,_,hr,_⟩
  obtain ⟨re,hre⟩ := hr.2.1
  have er := (hr.2.2.2 re hre).2.2
  rw [bad re] at er
  exact hne (Option.some.inj er)

/-- The route readout is taken from the shared updater's actual result after
an activated arrival. This links the component to the independent acquisition
semantics, rather than to supplied per-route result tables. -/
theorem result_actual_update (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (h : AcquisitionExecution.Ready raw.acquisition a)
    (r : RouteId) (entry : Registers R RV) (he : Result cfg raw a h r entry) :
    ∃ arrived d act o, AcquisitionExecution.Arrival cfg raw.acquisition a h r arrived ∧
      StrategyGame.PositiveSupport (AcquisitionExecution.rows raw.acquisition a) arrived d act o ∧
      entry = AcquisitionExecution.update raw.acquisition a h arrived d act o := by
  rcases he with ⟨_,arrived,_,da,o,ha,_,_,_,_,_,hp,hu⟩
  exact ⟨arrived,da.1,da.2,o,ha,hp,hu⟩

theorem source_absent_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (receiver : AcquisitionExecution.Receiver)
    (hr : raw.acquisition.receiver.read a = some receiver) (bad : receiver.sourcePresent = false) :
    ¬ Pass cfg raw a := by
  apply no_result_rejected cfg raw a
  intro h r entry he
  obtain ⟨arrived,_,_,_,ha,_,_⟩ := result_actual_update cfg raw a h r entry he
  rcases ha with ⟨hist,routes,events,realized,input,_,_,_,_,hi,_,_,_,active,_⟩
  have eq : input = receiver := Option.some.inj (hi.symm.trans hr)
  subst input
  simp [AcquisitionExecution.Activated,bad] at active

omit [DecidableEq Stage] in
theorem encoded_provenance_missing (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (r : RouteId) (k : Cell)
    (hk : k ∈ raw.provenance.dependencies) (hm : a k = none) : expected raw a r = none := by
  simp [expected,raw.provenance.missing a k hk hm]

theorem constant_probe_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (c : Nat)
    (bad : ∀ entry, raw.readout.eval a entry () = some (some c)) : ¬ Pass cfg raw a := by
  rintro ⟨_,r,s,_,_,_,_,rr,sr,nr,ns,endpoint,_,hn,hr,hs⟩
  obtain ⟨re,hre⟩ := hr.2.1
  obtain ⟨se,hse⟩ := hs.2.1
  have er : c = nr := Option.some.inj (Option.some.inj ((bad re).symm.trans (hr.2.2.2 re hre).2.1))
  have es : c = ns := Option.some.inj (Option.some.inj ((bad se).symm.trans (hs.2.2.2 se hse).2.1))
  exact hn (er.symm.trans es)

/-- Named executed readout: two actual response results carry different
retained registers and different future probes, both owned by the target. -/
def ExecutedMemory (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) : Prop :=
  ∃ h : AcquisitionExecution.Ready raw.acquisition a, ∃ r s re se rr sr nr ns,
    Result cfg raw a h r re ∧ Result cfg raw a h s se ∧ rr ≠ sr ∧ nr ≠ ns ∧
    raw.register.eval a re () = some rr ∧ raw.register.eval a se () = some sr ∧
    raw.readout.eval a re () = some (some nr) ∧ raw.readout.eval a se () = some (some ns) ∧
    raw.owner.eval a re () = some cfg.target ∧ raw.owner.eval a se () = some cfg.target

theorem route_memory_sound (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (h : Pass cfg raw a) : ExecutedMemory cfg raw a := by
  rcases h with ⟨hready,r,s,_,_,_,_,rr,sr,nr,ns,endpoint,hn,hm,hr,hs⟩
  obtain ⟨re,hre⟩ := hr.2.1
  obtain ⟨se,hse⟩ := hs.2.1
  have vr := hr.2.2.2 re hre
  have vs := hs.2.2.2 se hse
  exact ⟨hready.1,r,s,re,se,rr,sr,nr,ns,hre,hse,hn,hm,vr.1,vs.1,vr.2.1,vs.2.1,vr.2.2,vs.2.2⟩

/-- Direct failure of the named readout, not an inference from gate failure. -/
theorem constant_register_no_memory (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value) (c : Residue)
    (bad : ∀ entry, raw.register.eval a entry () = some c) : ¬ ExecutedMemory cfg raw a := by
  rintro ⟨_,r,s,re,se,rr,sr,nr,ns,_,_,hn,_,hr,hs,_⟩
  have er : c = rr := Option.some.inj ((bad re).symm.trans hr)
  have es : c = sr := Option.some.inj ((bad se).symm.trans hs)
  exact hn (er.symm.trans es)

theorem endpoint_mismatch_rejected (cfg : Config Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (a : Assignment Cell Value)
    (bad : ∀ (h : AcquisitionExecution.Ready raw.acquisition a) r s re se,
      r ≠ s → AcquisitionExecution.Arrival cfg raw.acquisition a h r re →
      AcquisitionExecution.Arrival cfg raw.acquisition a h s se →
      raw.endpoint.eval a re () ≠ raw.endpoint.eval a se ()) : ¬ Pass cfg raw a := by
  rintro ⟨h,r,s,_,_,hrs,_,rr,sr,nr,ns,endpoint,_,_,hr,hs⟩
  obtain ⟨re,hre⟩ := hr.2.1
  obtain ⟨se,hse⟩ := hs.2.1
  obtain ⟨ar,_,_,_,har,_,_⟩ := result_actual_update cfg raw a h.1 r re hre
  obtain ⟨as',_,_,_,has,_,_⟩ := result_actual_update cfg raw a h.1 s se hse
  exact bad h.1 r s ar as' hrs har has ((hr.2.2.1 ar har).trans (hs.2.2.1 as' has).symm)

end CSTTT.TargetTheory.GenericHandoff.RouteComponent
