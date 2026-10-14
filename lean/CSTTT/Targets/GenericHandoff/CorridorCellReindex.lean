import CSTTT.Targets.GenericHandoff.AcquisitionCellReindex
import CSTTT.Targets.GenericHandoff.RawCorridorSequence
import CSTTT.Targets.GenericHandoff.StagedAssignmentSpan

/-! The whole raw corridor and heterogeneous request translate into the
computed staged namespace. Decoded geometry, parent checks and actual legs
are exact on every partial assignment; no cached leg list is supplied. -/
namespace CSTTT.TargetTheory.GenericHandoff.CorridorCellReindex
open RegisterInterpreter CellReindex
variable {SC TC R D A O Stage Id History RouteId : Type}
  {SV : SC → Type} {TV : TC → Type} {RV : R → Type}

def raw (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionCorridor.Raw SC SV R RV D A O Stage Id History RouteId) :
    AcquisitionCorridor.Raw TC TV R RV D A O Stage Id History RouteId :=
  ⟨AcquisitionCellReindex.raw cell value r.acquisition,r.schema,r.names,CellReindex.view cell value r.seeds⟩

theorem read_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionCorridor.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV) :
    AcquisitionCorridor.read (raw cell value r) a = AcquisitionCorridor.read r (pullback cell value a) := by
  simp only [AcquisitionCorridor.read,raw,AcquisitionCellReindex.raw,view_equation,cell_view_equation]

variable [DecidableEq Stage]
theorem leg_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionCorridor.Raw SC SV R RV D A O Stage Id History RouteId)
    (v : AcquisitionCorridor.View Stage Id History RouteId) (rid : RouteId) :
    AcquisitionCorridor.leg (raw cell value r) v rid = AcquisitionCorridor.leg r v rid := rfl

theorem view_check_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionCorridor.Raw SC SV R RV D A O Stage Id History RouteId)
    (v : AcquisitionCorridor.View Stage Id History RouteId) :
    AcquisitionCorridor.ViewCheck (raw cell value r) v ↔ AcquisitionCorridor.ViewCheck r v := Iff.rfl

theorem parent_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionCorridor.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV) :
    AcquisitionCorridor.Pass (raw cell value r) a ↔ AcquisitionCorridor.Pass r (pullback cell value a) := by
  unfold AcquisitionCorridor.Pass
  rw [read_equation]
  exact and_congr (AcquisitionCellReindex.ready_iff cell value r.acquisition a) Iff.rfl

theorem legs_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionCorridor.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV) (rid : RouteId) :
    AcquisitionCorridor.legs (raw cell value r) a rid =
      AcquisitionCorridor.legs r (pullback cell value a) rid := by
  simp only [AcquisitionCorridor.legs,read_equation,leg_equation]

theorem semantic_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : AcquisitionCorridor.Raw SC SV R RV D A O Stage Id History RouteId) (a : Assignment TC TV) (rid : RouteId) :
    AcquisitionCorridor.Readout (raw cell value r) a rid ↔
      AcquisitionCorridor.Readout r (pullback cell value a) rid := by
  simp only [AcquisitionCorridor.Readout,legs_equation]

omit [DecidableEq Stage] in
def request (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (q : RawCorridorSequence.Request SC SV) : RawCorridorSequence.Request TC TV :=
  ⟨q.Register,q.registerValue,q.Disturbance,q.Action,q.Outcome,q.Stage,q.Id,q.History,q.Route,
    q.stageEq,raw cell value q.raw,q.route⟩

omit [DecidableEq Stage] in
theorem request_leg (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (q : RawCorridorSequence.Request SC SV) (a : Assignment TC TV) :
    RawCorridorSequence.leg (request cell value q) a =
      RawCorridorSequence.leg q (pullback cell value a) := by
  letI := q.stageEq
  simp only [RawCorridorSequence.leg,request,read_equation,leg_equation]

omit [DecidableEq Stage] in
theorem request_parent_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (q : RawCorridorSequence.Request SC SV) (a : Assignment TC TV) :
    RawCorridorSequence.Parent (request cell value q) a ↔
      RawCorridorSequence.Parent q (pullback cell value a) := by
  letI := q.stageEq
  exact and_congr (parent_iff cell value q.raw a) Iff.rfl

omit [DecidableEq Stage] in
theorem chain_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (qs : List (RawCorridorSequence.Request SC SV)) (a : Assignment TC TV) :
    RawCorridorSequence.chain a (qs.map (request cell value)) =
      RawCorridorSequence.chain (pullback cell value a) qs := by
  induction qs with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.map_cons,RawCorridorSequence.chain,request_leg,ih]

omit [DecidableEq Stage] in
theorem seams_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (qs : List (RawCorridorSequence.Request SC SV)) (a : Assignment TC TV) :
    RawCorridorSequence.seams a (qs.map (request cell value)) =
      RawCorridorSequence.seams (pullback cell value a) qs := by
  induction qs with
  | nil => rfl
  | cons q rest ih =>
    cases rest with
    | nil => rfl
    | cons r tail =>
      simp only [List.map_cons,RawCorridorSequence.seams,RawCorridorSequence.seam,request_leg]
      simp only [List.map_cons] at ih
      rw [ih]

omit [DecidableEq Stage] in
theorem chain_semantic_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (qs : List (RawCorridorSequence.Request SC SV)) (a : Assignment TC TV) :
    RawCorridorSequence.Readout a (qs.map (request cell value)) ↔
      RawCorridorSequence.Readout (pullback cell value a) qs := by
  simp only [RawCorridorSequence.Readout,chain_equation]

omit [DecidableEq Stage] in
theorem outer_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (qs : List (RawCorridorSequence.Request SC SV)) :
    RawCorridorSequence.OuterDistinct (qs.map (request cell value)) ↔ RawCorridorSequence.OuterDistinct qs := by
  simp only [RawCorridorSequence.OuterDistinct,List.head?_map,List.getLast?_map,Option.map_map]
  rfl

omit [DecidableEq Stage] in
theorem checked_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (qs : List (RawCorridorSequence.Request SC SV)) (a : Assignment TC TV) :
    RawCorridorSequence.Checked a (qs.map (request cell value)) ↔
      RawCorridorSequence.Checked (pullback cell value a) qs := by
  constructor
  · rintro ⟨hn,hp,hj,hd⟩
    refine ⟨fun he => hn (by simp [he]),?_,?_,(outer_iff cell value qs).mp hd⟩
    · intro q hq
      exact (request_parent_iff cell value q a).mp (hp _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
    · rw [← seams_equation cell value qs a]
      exact hj
  · rintro ⟨hn,hp,hj,hd⟩
    refine ⟨?_,?_,?_,(outer_iff cell value qs).mpr hd⟩
    · intro he
      exact hn (List.map_eq_nil_iff.mp he)
    · intro q hq
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
      exact (request_parent_iff cell value r a).mpr (hp r hr)
    · rw [seams_equation]
      exact hj

end CSTTT.TargetTheory.GenericHandoff.CorridorCellReindex
