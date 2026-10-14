import CSTTT.Transport.FutureDynamics
import CSTTT.Temporal.Clock

/-! Exact finite images, not bounded approximations of a run. Each code is a
raw value together with proof that it occurs on the audited finite frontier.
Decoding is projection of that value. The finite enum can contain duplicate
entries (as `FiniteEnum` permits); the image type itself identifies equal values.
Unbounded run counters are never truncated or reduced modulo an audit bound. -/
/- The candidate-parametric lemmas in this module are algebraic codec schemas,
not evidence about a RawBridge execution. FrozenBridgeSnapshotResult uses
only the observation/code/dynamics defined from that bridge. Legacy display
and decoder data below cannot be used as certification inputs. -/
namespace CSTTT.TransportTheory

abbrev Audited {I : Type} (frontier : List I) := {i : I // i ∈ frontier}

theorem audited_nonempty {I : Type} (frontier : List I) (hf : frontier ≠ []) :
    Nonempty (Audited frontier) := by
  cases frontier with
  | nil => exact False.elim (hf rfl)
  | cons first rest => exact ⟨⟨first, by simp⟩⟩

abbrev SnapshotImage {I V : Type} (frontier : List I) (readout : I → V) :=
  {v : V // v ∈ frontier.map readout}

def snapshotImageEnum {I V : Type} (frontier : List I) (readout : I → V) :
    FiniteEnum (SnapshotImage frontier readout) where
  elems := (frontier.map readout).attach
  complete := List.mem_attach _

def encodeSnapshotValue {I V : Type} (frontier : List I) (readout : I → V)
    (i : Audited frontier) : SnapshotImage frontier readout :=
  ⟨readout i.val, List.mem_map_of_mem i.property⟩

def decodeSnapshotValue {I V : Type} {frontier : List I} {readout : I → V}
    (v : SnapshotImage frontier readout) : V := v.val

theorem snapshot_value_roundtrip {I V : Type}
    (frontier : List I) (readout : I → V) (i : Audited frontier) :
    decodeSnapshotValue (encodeSnapshotValue frontier readout i) = readout i.val := rfl

theorem snapshot_value_no_loss {I V : Type}
    (frontier : List I) (readout : I → V) (i j : Audited frontier) :
    encodeSnapshotValue frontier readout i = encodeSnapshotValue frontier readout j ↔
      readout i.val = readout j.val :=
  ⟨congrArg Subtype.val, fun h => Subtype.ext h⟩

def mapSnapshotImage {I V W : Type} (frontier : List I)
    (source : I → V) (target : I → W) (mapRaw : V → W)
    (commutes : ∀ i ∈ frontier, mapRaw (source i) = target i)
    (v : SnapshotImage frontier source) : SnapshotImage frontier target :=
  ⟨mapRaw v.val, by
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp v.property
    exact List.mem_map.mpr ⟨i, hi, (commutes i hi).symm.trans (congrArg mapRaw heq)⟩⟩

theorem snapshot_map_encode {I V W : Type} (frontier : List I)
    (source : I → V) (target : I → W) (mapRaw : V → W)
    (hc : ∀ i ∈ frontier, mapRaw (source i) = target i) (i : Audited frontier) :
    mapSnapshotImage frontier source target mapRaw hc
      (encodeSnapshotValue frontier source i) = encodeSnapshotValue frontier target i :=
  Subtype.ext (hc i.val i.property)

theorem snapshot_map_decode {I V W : Type} (frontier : List I)
    (source : I → V) (target : I → W) (mapRaw : V → W)
    (hc : ∀ i ∈ frontier, mapRaw (source i) = target i)
    (v : SnapshotImage frontier source) :
    decodeSnapshotValue (mapSnapshotImage frontier source target mapRaw hc v) =
      mapRaw (decodeSnapshotValue v) := rfl

/-- The eight frozen data components, with the unbounded numerical readouts
still in Nat. `futureSufficient` is supplied later as a computed all-word
predicate, and never as an input proposition. -/
structure TemporalSnapshotReadout (Predictive Residue Maintenance : Type) where
  predictive : Predictive
  order : Nat
  tickPhase : Nat
  progress : Nat
  record : Nat
  residue : Residue
  maintenance : Maintenance
  owner : CarrierId
  deriving DecidableEq

def snapshotAlphabet {I P R M : Type} (frontier : List I)
    (readout : I → TemporalSnapshotReadout P R M) : TemporalAlphabet where
  predictiveType := SnapshotImage frontier (fun i => (readout i).predictive)
  orderType := SnapshotImage frontier (fun i => (readout i).order)
  tickType := SnapshotImage frontier (fun i => (readout i).tickPhase)
  progressType := SnapshotImage frontier (fun i => (readout i).progress)
  recordType := SnapshotImage frontier (fun i => (readout i).record)
  routeType := SnapshotImage frontier (fun i => (readout i).residue)
  maintenanceType := SnapshotImage frontier (fun i => (readout i).maintenance)
  predictiveEnum := snapshotImageEnum _ _
  orderEnum := snapshotImageEnum _ _
  tickEnum := snapshotImageEnum _ _
  progressEnum := snapshotImageEnum _ _
  recordEnum := snapshotImageEnum _ _
  routeEnum := snapshotImageEnum _ _
  maintenanceEnum := snapshotImageEnum _ _

/-- The only proposition placed in the frozen present is the all-word test
computed by G1b from the raw future model. It is proved by bisimulation below. -/
def frozenSnapshot {I P R M X A O C V : Type} [DecidableEq V]
    (model : FullFutureModel X A O C V) (frontier : List I)
    (readout : I → TemporalSnapshotReadout P R M) (i : Audited frontier) :
    TemporalSignature (snapshotAlphabet frontier readout) where
  predictiveNow :=
    ⟨encodeSnapshotValue frontier _ i, encodeSnapshotValue frontier _ i,
      FullFutureSufficient model⟩
  orderState := encodeSnapshotValue frontier _ i
  tickPhase := encodeSnapshotValue frontier _ i
  progressState := encodeSnapshotValue frontier _ i
  arrowRecord := encodeSnapshotValue frontier _ i
  maintenanceState := encodeSnapshotValue frontier _ i
  owner := (readout i.val).owner

def decodeFrozenSnapshot {I P R M : Type} (frontier : List I)
    (readout : I → TemporalSnapshotReadout P R M)
    (s : TemporalSignature (snapshotAlphabet frontier readout)) :
    TemporalSnapshotReadout P R M :=
  ⟨s.predictiveNow.predictiveClass.val, s.orderState.val, s.tickPhase.val,
    s.progressState.val, s.arrowRecord.val, s.predictiveNow.routeResidue.val,
    s.maintenanceState.val, s.owner⟩

/-- One whole-record equality includes each of the eight field codecs. -/
theorem frozen_snapshot_roundtrip {I P R M X A O C V : Type} [DecidableEq V]
    (model : FullFutureModel X A O C V) (frontier : List I)
    (readout : I → TemporalSnapshotReadout P R M) (i : Audited frontier) :
    decodeFrozenSnapshot frontier readout (frozenSnapshot model frontier readout i) =
      readout i.val := rfl

/-- The owner field has the fixed CarrierId type in the frozen structure.
Its auxiliary exact image also has a codec; the signature stores its decoding. -/
theorem frozen_snapshot_owner_codec {I P R M X A O C V : Type} [DecidableEq V]
    (model : FullFutureModel X A O C V) (frontier : List I)
    (readout : I → TemporalSnapshotReadout P R M) (i : Audited frontier) :
    (frozenSnapshot model frontier readout i).owner =
      decodeSnapshotValue (encodeSnapshotValue frontier (fun j => (readout j).owner) i) := rfl

structure SnapshotRawMaps (P Q R M : Type) where
  predictive : P → Q
  order : Nat → Nat
  tickPhase : Nat → Nat
  progress : Nat → Nat
  record : Nat → Nat
  residue : R → R
  maintenance : M → M
  owner : CarrierId → CarrierId

def mapSnapshotReadout {P Q R M : Type} (maps : SnapshotRawMaps P Q R M)
    (v : TemporalSnapshotReadout P R M) : TemporalSnapshotReadout Q R M :=
  ⟨maps.predictive v.predictive, maps.order v.order, maps.tickPhase v.tickPhase,
    maps.progress v.progress, maps.record v.record, maps.residue v.residue,
    maps.maintenance v.maintenance, maps.owner v.owner⟩

/-- Independent raw equations, prior to constructing either frozen signature. -/
def SnapshotMapCheck {I P Q R M : Type} (frontier : List I)
    (source : I → TemporalSnapshotReadout P R M)
    (target : I → TemporalSnapshotReadout Q R M) (maps : SnapshotRawMaps P Q R M) : Prop :=
  ∀ i ∈ frontier, mapSnapshotReadout maps (source i) = target i

/-- The full observation has exact forward and reverse snapshot equations.
The decoder may be partial off the audited frontier (e.g. excluded ambient
exit states), but it must recover every field exactly on that frontier. -/
structure SnapshotObservationData (I X C V P R M : Type) where
  run : I → X
  code : TemporalSnapshotReadout P R M → C
  display : TemporalSnapshotReadout P R M → V
  decode : V → Option (TemporalSnapshotReadout P R M)

def SnapshotObservationCheck {I X A O C V P R M : Type}
    (model : FullFutureModel X A O C V) (frontier : List I)
    (readout : I → TemporalSnapshotReadout P R M)
    (link : SnapshotObservationData I X C V P R M) : Prop :=
  ∀ i ∈ frontier, model.observe (link.run i) = link.display (readout i) ∧
    link.decode (model.observe (link.run i)) = some (readout i) ∧
    model.code (link.run i) = link.code (readout i)

def transportFrozenSnapshot {I P Q R M : Type} (frontier : List I)
    (source : I → TemporalSnapshotReadout P R M)
    (target : I → TemporalSnapshotReadout Q R M) (maps : SnapshotRawMaps P Q R M)
    (hc : SnapshotMapCheck frontier source target maps)
    (s : TemporalSignature (snapshotAlphabet frontier source)) :
    TemporalSignature (snapshotAlphabet frontier target) where
  predictiveNow :=
    ⟨mapSnapshotImage frontier _ _ maps.predictive
        (fun i hi => congrArg TemporalSnapshotReadout.predictive (hc i hi))
        s.predictiveNow.predictiveClass,
      mapSnapshotImage frontier _ _ maps.residue
        (fun i hi => congrArg TemporalSnapshotReadout.residue (hc i hi))
        s.predictiveNow.routeResidue,
      s.predictiveNow.futureSufficient⟩
  orderState := mapSnapshotImage frontier _ _ maps.order
    (fun i hi => congrArg TemporalSnapshotReadout.order (hc i hi)) s.orderState
  tickPhase := mapSnapshotImage frontier _ _ maps.tickPhase
    (fun i hi => congrArg TemporalSnapshotReadout.tickPhase (hc i hi)) s.tickPhase
  progressState := mapSnapshotImage frontier _ _ maps.progress
    (fun i hi => congrArg TemporalSnapshotReadout.progress (hc i hi)) s.progressState
  arrowRecord := mapSnapshotImage frontier _ _ maps.record
    (fun i hi => congrArg TemporalSnapshotReadout.record (hc i hi)) s.arrowRecord
  maintenanceState := mapSnapshotImage frontier _ _ maps.maintenance
    (fun i hi => congrArg TemporalSnapshotReadout.maintenance (hc i hi)) s.maintenanceState
  owner := maps.owner s.owner

theorem frozen_transport_decodes {I P Q R M : Type} (frontier : List I)
    (source : I → TemporalSnapshotReadout P R M)
    (target : I → TemporalSnapshotReadout Q R M) (maps : SnapshotRawMaps P Q R M)
    (hc : SnapshotMapCheck frontier source target maps)
    (s : TemporalSignature (snapshotAlphabet frontier source)) :
    decodeFrozenSnapshot frontier target (transportFrozenSnapshot frontier source target maps hc s) =
      mapSnapshotReadout maps (decodeFrozenSnapshot frontier source s) := rfl

/-- Equality is in the frozen target type, not only in a parallel readout
record. Each image-map equation is the exact encode/transport commuting square. -/
theorem frozen_snapshot_transport {I P Q R M X A O C V : Type} [DecidableEq V]
    (model : FullFutureModel X A O C V) (frontier : List I)
    (source : I → TemporalSnapshotReadout P R M)
    (target : I → TemporalSnapshotReadout Q R M) (maps : SnapshotRawMaps P Q R M)
    (hc : SnapshotMapCheck frontier source target maps) (i : Audited frontier) :
    transportFrozenSnapshot frontier source target maps hc
      (frozenSnapshot model frontier source i) = frozenSnapshot model frontier target i := by
  simp only [transportFrozenSnapshot, frozenSnapshot, snapshot_map_encode,
    TemporalSignature.mk.injEq, true_and]
  exact congrArg TemporalSnapshotReadout.owner (hc i.val i.property)

/-- All eight inverse codec equations, including the fixed owner field.
The future component is separately proved from the raw bisimulation. -/
theorem frozen_snapshot_all_field_codecs {I P R M X A O C V : Type} [DecidableEq V]
    (model : FullFutureModel X A O C V) (frontier : List I)
    (readout : I → TemporalSnapshotReadout P R M) (i : Audited frontier) :
    let s := frozenSnapshot model frontier readout i
    s.predictiveNow.predictiveClass.val = (readout i.val).predictive ∧
    s.orderState.val = (readout i.val).order ∧
    s.tickPhase.val = (readout i.val).tickPhase ∧
    s.progressState.val = (readout i.val).progress ∧
    s.arrowRecord.val = (readout i.val).record ∧
    s.predictiveNow.routeResidue.val = (readout i.val).residue ∧
    s.maintenanceState.val = (readout i.val).maintenance ∧
    s.owner = (readout i.val).owner :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem frozen_snapshot_full_future {I P R M X A O C V : Type} [DecidableEq V]
    (model : FullFutureModel X A O C V) (hb : FullOneStepBisim model)
    (frontier : List I) (readout : I → TemporalSnapshotReadout P R M)
    (i : Audited frontier) :
    (frozenSnapshot model frontier readout i).predictiveNow.futureSufficient :=
  full_future_sufficient_of_bisim model hb

/-- The decoded signature also recovers the complete future-model snapshot.
Both directions are required; an arbitrary display that hides a field cannot
pass the reverse equation on the audited frontier. -/
theorem frozen_snapshot_full_observation_link
    {I P R M X A O C V : Type} [DecidableEq V]
    (model : FullFutureModel X A O C V) (frontier : List I)
    (readout : I → TemporalSnapshotReadout P R M)
    (link : SnapshotObservationData I X C V P R M)
    (hl : SnapshotObservationCheck model frontier readout link) (i : Audited frontier) :
    model.observe (link.run i.val) =
      link.display (decodeFrozenSnapshot frontier readout
        (frozenSnapshot model frontier readout i)) ∧
    link.decode (model.observe (link.run i.val)) =
      some (decodeFrozenSnapshot frontier readout
        (frozenSnapshot model frontier readout i)) :=
  ⟨(hl i.val i.property).1, (hl i.val i.property).2.1⟩

/-- The frozen snapshot itself determines the code used by the all-word
test. Equal decoded frozen fields therefore give equal futures; the raw
model's code cannot smuggle in an extra, unrepresented snapshot coordinate. -/
theorem frozen_snapshot_future_from_fields
    {I P R M X A O C V : Type} [DecidableEq V]
    (model : FullFutureModel X A O C V) (hb : FullOneStepBisim model)
    (frontier : List I) (readout : I → TemporalSnapshotReadout P R M)
    (link : SnapshotObservationData I X C V P R M)
    (hl : SnapshotObservationCheck model frontier readout link)
    (i j : Audited frontier)
    (heq : decodeFrozenSnapshot frontier readout (frozenSnapshot model frontier readout i) =
      decodeFrozenSnapshot frontier readout (frozenSnapshot model frontier readout j))
    (word : List A) (trace : List V) :
    fullFuture model (link.run i.val) word trace =
      fullFuture model (link.run j.val) word trace := by
  have hcode : model.code (link.run i.val) = model.code (link.run j.val) := by
    rw [(hl i.val i.property).2.2, (hl j.val j.property).2.2]
    exact congrArg link.code heq
  exact full_future_sufficient_of_bisim model hb _ _ hcode word trace

end CSTTT.TransportTheory
