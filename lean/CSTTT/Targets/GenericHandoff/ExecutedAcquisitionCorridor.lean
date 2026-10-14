import CSTTT.Targets.GenericHandoff.AcquisitionCorridor

/-! G4 corridor coordinates tied to the actual executed acquisition frontier.
All helper objects are defined from a single frontier/raw assignment. Typed
coordinate encodings are raw maps, checked against every audited terminal.
Terminal coverage in AuditCheck ensures no declared history evades this link.
This is the corridor/execution boundary, not the full heterogeneous G1c bridge.
-/
namespace CSTTT.TargetTheory.GenericHandoff.ExecutedAcquisitionCorridor
open RegisterInterpreter CSTTT.TransportTheory CSTTT.CorridorTheory.AtomicChain

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O P Residue Maintenance Stage Id History RouteId : Type) where
  frontier : ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId
  names : AcquisitionCorridor.Names Id
  seeds : StaticView Cell Value (AcquisitionCorridor.Seeds History)
  predictiveCoordinate : StaticView Cell Value (P → Nat)
  historyCoordinate : Residue → List String
  routeCoordinate : Residue → List String

variable {Cell R D A O P Residue Maintenance Stage Id History RouteId : Type}
  {Value : Cell → Type} {RV : R → Type}
  [DecidableEq O] [DecidableEq Stage] [DecidableEq P]
  [DecidableEq Residue] [DecidableEq Maintenance]

def corridor (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId) :
    AcquisitionCorridor.Raw Cell Value R RV D A O Stage Id History RouteId :=
  ⟨raw.frontier.acquisition,raw.frontier.schema,raw.names,raw.seeds⟩

/-- Readout equations on actual terminal executions, not desired acceptance.
The same terminal selectors occur in AuditCheck's coverage obligation. -/
def SeedCoherence (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : ExecutionFrontier.Ready raw.frontier a)
    (v : AcquisitionCorridor.View Stage Id History RouteId) : Prop :=
  ∃ coordinate, raw.predictiveCoordinate.read a = some coordinate ∧
    (∀ i j : Audited raw.frontier.audit,
      coordinate (ExecutionFrontier.observation raw.frontier a h i.val).predictive =
        coordinate (ExecutionFrontier.observation raw.frontier a h j.val).predictive →
      (ExecutionFrontier.observation raw.frontier a h i.val).predictive =
        (ExecutionFrontier.observation raw.frontier a h j.val).predictive) ∧
    ∀ histories, raw.frontier.acquisition.histories.read a = some histories →
      ∀ i ∈ raw.frontier.audit, i.2 = (histories i.1).length →
        v.seeds.predictive i.1 = coordinate (ExecutionFrontier.observation raw.frontier a h i).predictive ∧
        v.seeds.history i.1 = raw.historyCoordinate (ExecutionFrontier.observation raw.frontier a h i).residue ∧
        v.seeds.history i.1 ++ (v.routes (raw.frontier.auditRoute i)).path.map raw.names.event =
          raw.routeCoordinate (ExecutionFrontier.observation raw.frontier a h i).residue

def Valid (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  ExecutionFrontier.Valid raw.frontier a ∧ AcquisitionCorridor.Pass (corridor raw) a ∧
    ∀ h : ExecutionFrontier.Ready raw.frontier a, ∀ v,
      AcquisitionCorridor.read (corridor raw) a = some v → SeedCoherence raw a h v

theorem histories_have_executed_seeds
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Valid raw a)
    (hist : History) (hhist : hist ∈ raw.frontier.schema.histories) :
    ∃ ready : ExecutionFrontier.Ready raw.frontier a,
    ∃ v : AcquisitionCorridor.View Stage Id History RouteId,
    ∃ i : Audited raw.frontier.audit, ∃ coordinate : P → Nat,
      raw.predictiveCoordinate.read a = some coordinate ∧
      AcquisitionCorridor.read (corridor raw) a = some v ∧ i.val.1 = hist ∧
      ExecutionFrontier.Closure raw.frontier a ready (ExecutionFrontier.snapshot raw.frontier a ready i.val) ∧
      v.seeds.predictive hist = coordinate (ExecutionFrontier.observation raw.frontier a ready i.val).predictive ∧
      v.seeds.history hist = raw.historyCoordinate (ExecutionFrontier.observation raw.frontier a ready i.val).residue ∧
      v.seeds.history hist ++ (v.routes (raw.frontier.auditRoute i.val)).path.map raw.names.event =
        raw.routeCoordinate (ExecutionFrontier.observation raw.frontier a ready i.val).residue := by
  obtain ⟨ready,ha,_⟩ := h.1
  obtain ⟨histories,he,hcheck,hcover⟩ := ha.2
  obtain ⟨i,hi,hh,ht⟩ := hcover hist hhist
  obtain ⟨_,v,hv,_⟩ := h.2.1
  have hend : i.2 = (histories i.1).length := by simpa only [hh] using ht
  obtain ⟨coordinate,hcoord,_,hseeds⟩ := h.2.2 ready v hv
  have hs := hseeds histories he i hi hend
  exact ⟨ready,v,⟨i,hi⟩,coordinate,hcoord,hv,hh,(ExecutionFrontier.snapshot_execution _ _ ready ha i hi).2,
    by simpa only [hh] using hs.1,by simpa only [hh] using hs.2.1,by simpa only [hh] using hs.2.2⟩

/-- The corridor witness and all-word full-interface future theorem are
derived from their own computed gates. Neither is inferred from the other. -/
theorem soundness (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Valid raw a) :
    (∀ rid ∈ raw.frontier.schema.routes, AcquisitionCorridor.Readout (corridor raw) a rid) ∧
    ∃ ready : ExecutionFrontier.Ready raw.frontier a,
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.frontier) a ready.2) ∧
      RegisterFuture.ReadoutLawGate (ExecutionFrontier.temporal raw.frontier) raw.frontier.recipes a ready.2
        (ExecutionFrontier.roots raw.frontier a ready) := by
  constructor
  · intro rid hr
    exact AcquisitionCorridor.constructs (corridor raw) a h.2.1 rid hr
  · obtain ⟨ready,_,future,laws,_⟩ := ExecutionFrontier.soundness raw.frontier a h.1
    exact ⟨ready,future,laws⟩

theorem seed_mismatch_guard (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (ready : ExecutionFrontier.Ready raw.frontier a)
    (v : AcquisitionCorridor.View Stage Id History RouteId) (hv : AcquisitionCorridor.read (corridor raw) a = some v)
    (histories : History → List (D × A × O)) (hh : raw.frontier.acquisition.histories.read a = some histories)
    (i : Audited raw.frontier.audit) (ht : i.val.2 = (histories i.val.1).length)
    (coordinate : P → Nat) (hcoord : raw.predictiveCoordinate.read a = some coordinate)
    (bad : ¬ (v.seeds.predictive i.val.1 = coordinate (ExecutionFrontier.observation raw.frontier a ready i.val).predictive ∧
      v.seeds.history i.val.1 = raw.historyCoordinate (ExecutionFrontier.observation raw.frontier a ready i.val).residue ∧
      v.seeds.history i.val.1 ++ (v.routes (raw.frontier.auditRoute i.val)).path.map raw.names.event =
        raw.routeCoordinate (ExecutionFrontier.observation raw.frontier a ready i.val).residue)) :
    ¬ Valid raw a := by
  intro h
  obtain ⟨other,ho,_,hs⟩ := h.2.2 ready v hv
  have he := Option.some.inj (ho.symm.trans hcoord)
  subst other
  exact bad (hs histories hh i.val i.property ht)

theorem missing_atomic_guard (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hm : raw.frontier.acquisition.events.read a = none) : ¬ Valid raw a :=
  fun h => ExecutionFrontier.missing_atomic_view raw.frontier a hm h.1

theorem missing_coordinate_guard (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.predictiveCoordinate.dependencies) (hm : a k = none) :
    ¬ Valid raw a := by
  rintro ⟨⟨ready,_⟩,⟨_,v,hv,_⟩,coherence⟩
  obtain ⟨coord,hc,_⟩ := coherence ready v hv
  rw [raw.predictiveCoordinate.missing a k hk hm] at hc
  contradiction

end CSTTT.TargetTheory.GenericHandoff.ExecutedAcquisitionCorridor
