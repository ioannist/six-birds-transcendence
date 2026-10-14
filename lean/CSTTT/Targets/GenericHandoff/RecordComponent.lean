import CSTTT.Targets.GenericHandoff.AcquisitionExecution
import CSTTT.Transport.RawRecordArrow

/-! The record-arrow component is constructed from the shared raw event table,
realization, writers and event clock. Neither record edges nor record ranks are
inputs. Its transport law is checked on those computed objects; it does not
stand for the separate closure-wide post-exit record update law. -/
namespace CSTTT.TargetTheory.GenericHandoff.RecordComponent
open CSTTT.RecordTheory RegisterInterpreter

structure Data (Stage Id Route : Type) where
  events : Id → Option (AcquisitionExecution.Event Stage)
  realized : List Stage
  sourceWriter : Route → Bool
  targetWriter : Route → Bool
  clock : Stage → Nat

structure Schema (Id Route : Type) where
  events : List Id
  routes : List Route

variable {Cell Stage Id Route : Type} {Value : Cell → Type} [DecidableEq Stage]

def strict (d : Data Stage Id Route) (e : AcquisitionExecution.Event Stage) : Bool :=
  e.atomic && e.strictStep && decide (e.fromStage ∈ d.realized) && decide (e.toStage ∈ d.realized) &&
    decide (e.orderAdvance > 0 ∧ d.clock e.toStage = d.clock e.fromStage + e.orderAdvance)

def edges (cfg : Schema Id Route) (d : Data Stage Id Route) (source : Bool) : List (Id × Id) :=
  cfg.events.flatMap fun i => cfg.events.filterMap fun j =>
    match d.events i,d.events j with
    | some e,some f =>
      let support := if source then e.sourceSupport && f.sourceSupport else e.targetSupport && f.targetSupport
      let writers := cfg.routes.all (if source then d.sourceWriter else d.targetWriter)
      if decide (e.toStage = f.fromStage) && support && writers && strict d e && strict d f
      then some (i,j) else none
    | _,_ => none

def rank (d : Data Stage Id Route) (i : Id) : Nat :=
  ((d.events i).map fun e => d.clock e.toStage).getD 0

def transport (cfg : Schema Id Route) (d : Data Stage Id Route) : RawRecordTransport Id Id :=
  ⟨edges cfg d true,edges cfg d false,id,rank d,rank d,id,fun i j => rank d j - rank d i⟩

def Check (cfg : Schema Id Route) (d : Data Stage Id Route) : Prop :=
  cfg.routes ≠ [] ∧ (∀ r ∈ cfg.routes, d.sourceWriter r = true ∧ d.targetWriter r = true) ∧
    (∀ i ∈ cfg.events, ∃ e, d.events i = some e ∧ strict d e = true) ∧
    edges cfg d true ≠ [] ∧ (∀ p ∈ edges cfg d true, p ∈ edges cfg d false)

/-- Arithmetic increments are computed from the independent event clock.
There is no TargetArrow field or assumed strictness verdict. -/
theorem positive_increment (cfg : Schema Id Route) (d : Data Stage Id Route) :
    PositiveRecordIncrement (transport cfg d) := by
  intro i j h
  have hs : rank d i < rank d j := h.2
  change rank d j = rank d i + (rank d j - rank d i) ∧ 0 < rank d j - rank d i
  omega

theorem sound (cfg : Schema Id Route) (d : Data Stage Id Route) (h : Check cfg d) :
    ∀ i j, SourceArrow (transport cfg d) i j → TargetArrow (transport cfg d) i j := by
  apply monotoneRecordDescentTransportsArrow_generic (transport cfg d)
  · exact ⟨fun i j hij => h.2.2.2.2 (i,j) hij,fun _ => rfl⟩
  · exact positive_increment cfg d

theorem clock_strict_on_edge (cfg : Schema Id Route) (d : Data Stage Id Route)
    (i j : Id) (h : (i,j) ∈ edges cfg d true) : rank d i < rank d j := by
  obtain ⟨i',_,hi⟩ := List.mem_flatMap.mp h
  obtain ⟨j',_,hj⟩ := List.mem_filterMap.mp hi
  cases he : d.events i' with
  | none => simp [he] at hj
  | some e =>
    cases hf : d.events j' with
    | none => simp [he,hf] at hj
    | some f =>
      simp only [he,hf,if_true] at hj
      split at hj
      · rename_i hc
        have pairEq : (i',j') = (i,j) := Option.some.inj hj
        cases pairEq
        simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
        have heq := hc.1.1.1.1
        have hstrict := hc.2
        simp only [strict,Bool.and_eq_true,decide_eq_true_eq] at hstrict
        simp only [rank,he,hf,Option.map_some,Option.getD_some]
        rw [heq]
        omega
      · contradiction

theorem nonempty_arrow (cfg : Schema Id Route) (d : Data Stage Id Route) (h : Check cfg d) :
    ∃ i j, SourceArrow (transport cfg d) i j := by
  obtain ⟨p,hp⟩ := List.exists_mem_of_ne_nil _ h.2.2.2.1
  exact ⟨p.1,p.2,hp,clock_strict_on_edge cfg d _ _ hp⟩

def Pass (cfg : Schema Id Route) (v : StaticView Cell Value (Data Stage Id Route))
    (a : Assignment Cell Value) : Prop := ∃ d, v.read a = some d ∧ Check cfg d

theorem locality (cfg : Schema Id Route) (v : StaticView Cell Value (Data Stage Id Route))
    {a b : Assignment Cell Value} (h : Agrees v.dependencies a b) : Pass cfg v a ↔ Pass cfg v b := by
  simp only [Pass,v.locality h]

theorem missing_rejected (cfg : Schema Id Route) (v : StaticView Cell Value (Data Stage Id Route))
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ v.dependencies) (hm : a k = none) : ¬ Pass cfg v a := by
  simp [Pass,v.missing a k hk hm]

theorem writer_rejected (cfg : Schema Id Route) (d : Data Stage Id Route) (r : Route)
    (hr : r ∈ cfg.routes) (bad : d.sourceWriter r = false ∨ d.targetWriter r = false) : ¬ Check cfg d := by
  intro h
  have hw := h.2.1 r hr
  rcases bad with bad | bad <;> simp_all

theorem unrealized_rejected (cfg : Schema Id Route) (d : Data Stage Id Route) (i : Id)
    (hi : i ∈ cfg.events) (e : AcquisitionExecution.Event Stage) (he : d.events i = some e)
    (bad : e.toStage ∉ d.realized) : ¬ Check cfg d := by
  intro h
  obtain ⟨f,hf,hs⟩ := h.2.2.1 i hi
  have hfe : f = e := Option.some.inj (hf.symm.trans he)
  subst f
  simp [strict,bad] at hs

theorem zero_clock_rejected (cfg : Schema Id Route) (d : Data Stage Id Route) (i : Id)
    (hi : i ∈ cfg.events) (e : AcquisitionExecution.Event Stage) (he : d.events i = some e)
    (bad : d.clock e.toStage = d.clock e.fromStage) : ¬ Check cfg d := by
  intro h
  obtain ⟨f,hf,hs⟩ := h.2.2.1 i hi
  have hfe : f = e := Option.some.inj (hf.symm.trans he)
  subst f
  simp only [strict,Bool.and_eq_true,decide_eq_true_eq] at hs
  omega

end CSTTT.TargetTheory.GenericHandoff.RecordComponent
