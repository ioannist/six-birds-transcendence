import CSTTT.Targets.GenericHandoff.SupportedAcquisitionSequence
import CSTTT.Targets.GenericHandoff.AcquisitionCellReindex

/-! Exact arbitrary-partial namespace transport of supported acquisition
sequencing, including complete computed entry and sequential readouts. -/
namespace CSTTT.TargetTheory.GenericHandoff.SupportedSequenceCellReindex
open RegisterInterpreter CellReindex AcquisitionExecution SupportedAcquisitionSequence
variable {SC TC R S D A O Stage Id H Route : Type} {SV : SC → Type} {TV : TC → Type}
  {RV : R → Type} {WV : S → Type} [DecidableEq D] [DecidableEq A] [DecidableEq O]
variable (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)

theorem boundary_ready_iff (p : (k : S) → Expr SC SV R RV Unit (WV k)) (a : Assignment TC TV) :
    RegisterSubstitution.Ready (fun k => expression cell value (p k)) a ↔
      RegisterSubstitution.Ready p (pullback cell value a) := by
  constructor
  · intro h k; exact (CellReindex.ready_iff cell value (p k) a).mp (h k)
  · intro h k; exact (CellReindex.ready_iff cell value (p k) a).mpr (h k)

theorem boundary_equation (p : (k : S) → Expr SC SV R RV Unit (WV k))
    (a : Assignment TC TV) (h : RegisterSubstitution.Ready (fun k => expression cell value (p k)) a)
    (j : RegisterSubstitution.Ready p (pullback cell value a)) (x : Registers R RV) :
    RegisterSubstitution.translate (fun k => expression cell value (p k)) a h x () =
      RegisterSubstitution.translate p (pullback cell value a) j x () := by
  funext k
  have he := evaluation cell value (p k) a x ()
  have hl := RegisterSubstitution.translation_equation (fun k => expression cell value (p k)) a h x () k
  have hr := RegisterSubstitution.translation_equation p (pullback cell value a) j x () k
  exact Option.some.inj (hl.symm.trans (he.trans hr))

theorem step_equation (raw : Raw SC SV R RV D A O Stage Id H Route) (a : Assignment TC TV)
    (x : Registers R RV) (d : D) (act : A) (o : O) :
    stepCheck (AcquisitionCellReindex.raw cell value raw) a x d act o =
      stepCheck raw (pullback cell value a) x d act o := by
  simp only [stepCheck,AcquisitionCellReindex.rows_equation]
  rfl

theorem fold_equation (raw : Raw SC SV R RV D A O Stage Id H Route) (a : Assignment TC TV)
    (h : Ready (AcquisitionCellReindex.raw cell value raw) a)
    (j : Ready raw (pullback cell value a)) (x : Registers R RV) (word : List (D × A × O)) :
    supportedFold (AcquisitionCellReindex.raw cell value raw) a h x word =
      supportedFold raw (pullback cell value a) j x word := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [supportedFold,step_equation cell value raw a,
      AcquisitionCellReindex.update_equation cell value raw a h j,ih]

theorem from_start_equation (raw : Raw SC SV R RV D A O Stage Id H Route) (a : Assignment TC TV)
    (h : Ready (AcquisitionCellReindex.raw cell value raw) a)
    (j : Ready raw (pullback cell value a)) (x : Registers R RV) (rid : Route) :
    fromStart (AcquisitionCellReindex.raw cell value raw) a h x rid =
      fromStart raw (pullback cell value a) j x rid := by
  simp only [fromStart,fold_equation cell value raw a h j,
    AcquisitionCellReindex.receive_equation cell value raw a h j]
  simp only [AcquisitionCellReindex.raw,view_equation,cell_view_equation]

theorem first_arrival_equation (raw : Raw SC SV R RV D A O Stage Id H Route) (a : Assignment TC TV)
    (h : Ready (AcquisitionCellReindex.raw cell value raw) a)
    (j : Ready raw (pullback cell value a)) (rid : Route) :
    firstArrival (AcquisitionCellReindex.raw cell value raw) a h rid =
      firstArrival raw (pullback cell value a) j rid := by
  simp only [firstArrival,from_start_equation cell value raw a h j,
    AcquisitionCellReindex.initial_equation cell value raw a h j]
  simp only [AcquisitionCellReindex.raw,cell_view_equation]

theorem post_exit_equation (raw : Raw SC SV R RV D A O Stage Id H Route) (a : Assignment TC TV)
    (h : Ready (AcquisitionCellReindex.raw cell value raw) a)
    (j : Ready raw (pullback cell value a)) (rid : Route) (o : O) (arrived : Option (Registers R RV)) :
    postExit (AcquisitionCellReindex.raw cell value raw) a h rid o arrived =
      postExit raw (pullback cell value a) j rid o arrived := by
  simp only [postExit,step_equation cell value raw a,
    AcquisitionCellReindex.update_equation cell value raw a h j]
  simp only [AcquisitionCellReindex.raw,cell_view_equation,evaluation]

theorem first_entry_equation (raw : Raw SC SV R RV D A O Stage Id H Route) (a : Assignment TC TV)
    (h : Ready (AcquisitionCellReindex.raw cell value raw) a)
    (j : Ready raw (pullback cell value a)) (rid : Route) (o : O) :
    firstEntry (AcquisitionCellReindex.raw cell value raw) a h rid o =
      firstEntry raw (pullback cell value a) j rid o := by
  simp only [firstEntry,first_arrival_equation cell value raw a h j,post_exit_equation cell value raw a h j]

theorem next_arrival_equation
    (first : Raw SC SV R RV D A O Stage Id H Route) (second : Raw SC SV S WV D A O Stage Id H Route)
    (p : (k : S) → Expr SC SV R RV Unit (WV k)) (a : Assignment TC TV)
    (hf : Ready (AcquisitionCellReindex.raw cell value first) a)
    (hs : Ready (AcquisitionCellReindex.raw cell value second) a)
    (hb : RegisterSubstitution.Ready (fun k => expression cell value (p k)) a)
    (jf : Ready first (pullback cell value a)) (js : Ready second (pullback cell value a))
    (jb : RegisterSubstitution.Ready p (pullback cell value a)) (l r : Route) (o : O) :
    nextArrival (AcquisitionCellReindex.raw cell value first) (AcquisitionCellReindex.raw cell value second)
      (fun k => expression cell value (p k)) a hf hs hb l r o =
    nextArrival first second p (pullback cell value a) jf js jb l r o := by
  simp only [nextArrival,first_entry_equation cell value first a hf jf,
    boundary_equation cell value p a hb jb,from_start_equation cell value second a hs js]

theorem next_entry_equation
    (first : Raw SC SV R RV D A O Stage Id H Route) (second : Raw SC SV S WV D A O Stage Id H Route)
    (p : (k : S) → Expr SC SV R RV Unit (WV k)) (a : Assignment TC TV)
    (hf : Ready (AcquisitionCellReindex.raw cell value first) a)
    (hs : Ready (AcquisitionCellReindex.raw cell value second) a)
    (hb : RegisterSubstitution.Ready (fun k => expression cell value (p k)) a)
    (jf : Ready first (pullback cell value a)) (js : Ready second (pullback cell value a))
    (jb : RegisterSubstitution.Ready p (pullback cell value a)) (l r : Route) (o u : O) :
    nextEntry (AcquisitionCellReindex.raw cell value first) (AcquisitionCellReindex.raw cell value second)
      (fun k => expression cell value (p k)) a hf hs hb l r o u =
    nextEntry first second p (pullback cell value a) jf js jb l r o u := by
  simp only [nextEntry,next_arrival_equation cell value first second p a hf hs hb jf js jb,
    post_exit_equation cell value second a hs js]

variable [DecidableEq Stage]
omit [DecidableEq D] [DecidableEq A] [DecidableEq O] in
theorem route_check_iff (raw : Raw SC SV R RV D A O Stage Id H Route) (a : Assignment TC TV)
    (cfg : Schema Stage Id H Route) (rid : Route) :
    RouteCheck cfg (AcquisitionCellReindex.raw cell value raw) a rid ↔ RouteCheck cfg raw (pullback cell value a) rid := by
  simp only [RouteCheck,AcquisitionCellReindex.raw,view_equation,cell_view_equation]

omit [DecidableEq D] [DecidableEq A] [DecidableEq O] in
theorem entry_iff (raw : Raw SC SV R RV D A O Stage Id H Route) (a : Assignment TC TV)
    (h : Ready (AcquisitionCellReindex.raw cell value raw) a) (j : Ready raw (pullback cell value a))
    (cfg : Schema Stage Id H Route) (entry : Registers R RV) :
    Entry cfg (AcquisitionCellReindex.raw cell value raw) a h entry ↔ Entry cfg raw (pullback cell value a) j entry := by
  have hr := funext (fun x => funext (fun d => funext (AcquisitionCellReindex.rows_equation cell value raw a x d)))
  simp only [Entry,hr,AcquisitionCellReindex.domain_iff,AcquisitionCellReindex.arrival_iff cell value raw a h j,
    AcquisitionCellReindex.update_equation cell value raw a h j]
  simp only [AcquisitionCellReindex.raw,AcquisitionCellReindex.execution,cell_view_equation,evaluation]

theorem readout_iff
    (first : Raw SC SV R RV D A O Stage Id H Route) (second : Raw SC SV S WV D A O Stage Id H Route)
    (p : (k : S) → Expr SC SV R RV Unit (WV k)) (lc rc : Schema Stage Id H Route) (a : Assignment TC TV)
    (l r : Route) (o u : O) :
    Readout (AcquisitionCellReindex.raw cell value first) (AcquisitionCellReindex.raw cell value second)
      (fun k => expression cell value (p k)) lc rc a l r o u ↔
    Readout first second p lc rc (pullback cell value a) l r o u := by
  constructor
  · rintro ⟨hf,hs,hb,before,after,hbe,hfirst,hae,hlast,anchor⟩
    have jf := (AcquisitionCellReindex.ready_iff cell value first a).mp hf
    have js := (AcquisitionCellReindex.ready_iff cell value second a).mp hs
    have jb : RegisterSubstitution.Ready p (pullback cell value a) := (boundary_ready_iff cell value p a).mp hb
    refine ⟨jf,js,jb,before,after,?_,(entry_iff cell value first a hf jf lc before).mp hfirst,?_,
      (entry_iff cell value second a hs js rc after).mp hlast,?_⟩
    · rw [← first_entry_equation cell value first a hf jf]; exact hbe
    · rw [← next_entry_equation cell value first second p a hf hs hb jf js jb]; exact hae
    · intro routes hr
      rw [← boundary_equation cell value p a hb jb,← AcquisitionCellReindex.initial_equation cell value second a hs js]
      apply anchor routes
      simpa only [AcquisitionCellReindex.raw,cell_view_equation] using hr
  · rintro ⟨jf,js,jb,before,after,hbe,hfirst,hae,hlast,anchor⟩
    have hf := (AcquisitionCellReindex.ready_iff cell value first a).mpr jf
    have hs := (AcquisitionCellReindex.ready_iff cell value second a).mpr js
    have hb : RegisterSubstitution.Ready (fun k => expression cell value (p k)) a := (boundary_ready_iff cell value p a).mpr jb
    refine ⟨hf,hs,hb,before,after,?_,(entry_iff cell value first a hf jf lc before).mpr hfirst,?_,
      (entry_iff cell value second a hs js rc after).mpr hlast,?_⟩
    · rw [first_entry_equation cell value first a hf jf]; exact hbe
    · rw [next_entry_equation cell value first second p a hf hs hb jf js jb]; exact hae
    · intro routes hr
      rw [boundary_equation cell value p a hb jb,AcquisitionCellReindex.initial_equation cell value second a hs js]
      apply anchor routes
      simpa only [AcquisitionCellReindex.raw,cell_view_equation] using hr

end CSTTT.TargetTheory.GenericHandoff.SupportedSequenceCellReindex
