import CSTTT.Targets.GenericHandoff.PackageRuntime
import CSTTT.Targets.GenericHandoff.POS04DispatcherEquivalence
import CSTTT.Targets.ComputedFIACH.Assembly

/-! Exact typed-stage/closed-dispatcher adapter for arbitrary POS-04 partial
assignments. The stage, cover and global are raw-data constructions. This is
not a positive-only callback or an assembled RawHandoff instance. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04DispatchedStage
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH
open ClauseDispatcher POS04Dispatcher
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def cover : RawCover Kind Cell :=
  ⟨kinds,fun k => POS04PackageEngine.cover.scopes (clause k),
    fun i j => POS04PackageEngine.cover.adjacent (clause i) (clause j)⟩
def stage : Stage (Index := Kind) POS04PackageEngine.lang :=
  fun k => POS04PackageEngine.stage (clause k)
def raw : DispatchedPackage.Raw Cell Cell Value Value where
  language := POS04PackageEngine.lang
  stage := stage
  referenceStage := stage
  sourceScopes := fun k => stagedSourceScope (arrivalCover .target) (clause k)
  cover := cover
  clauses := package .target

private theorem path_reindex {i j : Clause} {k : Cell}
    (h : CSTTT.PackageTheory.ScopedReach (fun a b => POS04PackageEngine.cover.adjacent a b = true)
      (fun c k => k ∈ POS04PackageEngine.cover.scopes c) k i j) :
    CSTTT.PackageTheory.ScopedReach (fun a b => cover.adjacent a b = true)
      (fun c k => k ∈ cover.scopes c) k (kind i) (kind j) := by
  induction h with
  | refl i hi => exact .refl _ (by simpa [cover] using hi)
  | step hi hj he tail ih =>
    exact .step (by simpa [cover] using hi) (by simpa [cover] using hj)
      (by simpa [cover] using he) ih

theorem cover_check : CSTTT.TargetTheory.GenericHandoff.CoverCheck cover := by
  constructor
  · intro k
    exact ⟨.c1,by decide,primitive_cells_complete k⟩
  · intro i j k hi hj
    have h := (POS04Adapter.canonical_cover_checked .target).2 (clause i) (clause j) k hi hj
    simpa using path_reindex h

theorem scope_check : DispatchedPackage.ScopeCheck raw := by
  intro c k
  cases c <;> cases k <;> first | decide +kernel | (rename_i tag; cases tag <;> decide +kernel)

theorem mapped_eq (a : CSTTT.POS04.Assigned.Assignment) (c : Kind) :
    mappedLocal raw.language a raw.stage raw.cover.scopes c =
      mappedLocal POS04PackageEngine.lang a POS04PackageEngine.stage POS04PackageEngine.cover.scopes (clause c) := rfl

theorem edges (a : CSTTT.POS04.Assigned.Assignment) :
    CSTTT.TargetTheory.GenericHandoff.EdgeCompatible cover (mappedLocal raw.language a raw.stage cover.scopes) := by
  intro i j k he hi hj
  have at_image (c : Kind) (hc : k ∈ cover.scopes c) :
      mappedLocal raw.language a raw.stage cover.scopes c k = image a k :=
    (congrFun (mapped_eq a c) k).trans
      ((congrFun (POS04Adapter.mapped_eq a canonicalStage (arrivalCover .target) (clause c)) k).trans
        (image_mapped a (clause c) k hc))
  exact (at_image i hi).trans (at_image j hj).symm

theorem global_eq_image (a : CSTTT.POS04.Assigned.Assignment) :
    DispatchedPackage.global raw a = image a := by
  funext k
  change glued cover (mappedLocal raw.language a raw.stage cover.scopes) k = _
  rw [glued_restricts cover _ cover_check (edges a) .c1 k (primitive_cells_complete k)]
  exact (congrFun (mapped_eq a .c1) k).trans
    ((congrFun (POS04Adapter.mapped_eq a canonicalStage (arrivalCover .target) .c1) k).trans
      (image_mapped a .c1 k (primitive_cells_complete k)))

theorem total_iff (a : CSTTT.POS04.Assigned.Assignment) :
    StageTotal raw.language a raw.stage cover.scopes ↔ CSTTT.POS04.Assigned.Complete primitiveCells a := by
  have h : StageTotal raw.language a raw.stage cover.scopes ↔
      StageTotal POS04PackageEngine.lang a POS04PackageEngine.stage POS04PackageEngine.cover.scopes := by
    constructor
    · intro ht c k hk
      simpa only [raw,stage,cover,clause_kind] using ht (kind c) k (by simpa [cover] using hk)
    · intro ht c k hk; exact ht (clause c) k hk
  exact h.trans (POS04PackageEngine.total_iff_complete a)

theorem source_coverage : SourceCoverage raw.language raw.stage raw.sourceScopes cover.scopes := by
  intro c s hs
  obtain ⟨k,hk,he⟩ := List.mem_map.mp hs
  exact ⟨k,hk,⟨swapCell k,fun v => some (translatedValue k v)⟩,rfl,he⟩

theorem local_iff_global (a : CSTTT.POS04.Assigned.Assignment) :
    PackageEngine.LocalChecks raw.language a raw.stage cover
      (fun c => (raw.clauses.rule c).accept) ↔ (package .target).accept (image a) := by
  have h := PackageEngine.local_checks_iff_global raw.language a raw.stage cover
    (fun c => (raw.clauses.rule c).accept) (fun c => (raw.clauses.rule c).scope)
    (fun c x y hx => (raw.clauses.rule c).locality hx) cover_check scope_check (edges a)
  change _ ↔ raw.clauses.accept (DispatchedPackage.global raw a) at h
  rw [global_eq_image] at h
  exact h

/-- The complete generic stage/cover check, not just canonical truth. -/
theorem valid_iff (a : CSTTT.POS04.Assigned.Assignment) :
    DispatchedPackage.Valid raw a ↔ PackageLane a := by
  constructor
  · intro h
    apply (POS04Dispatcher.p_iff a).mp
    exact ⟨(total_iff a).mp h.2.2.1,(local_iff_global a).mp h.2.2.2.2.2.2.1⟩
  · intro h
    obtain ⟨hc,hp⟩ := (POS04Dispatcher.p_iff a).mpr h
    exact ⟨cover_check,scope_check,(total_iff a).mpr hc,
      fun _ _ _ => rfl,fun _ _ _ => rfl,source_coverage,(local_iff_global a).mpr hp,edges a⟩

theorem positive : DispatchedPackage.Valid raw canonical := (valid_iff _).mpr package_lane_positive

theorem deleted (a : CSTTT.POS04.Assigned.Assignment) (k : Cell) :
    ¬ DispatchedPackage.Valid raw (CSTTT.POS04.Assigned.put a k none) :=
  fun h => package_lane_missing k ((valid_iff _).mp h)

theorem controls (v : PackageControl) :
    ¬ DispatchedPackage.Valid raw (exchangeAssignment (packageControl v)) :=
  fun h => POS04PackageEngine.package_controls v ((POS04PackageEngine.p_iff _).mpr ((valid_iff _).mp h))

/-- Exact adapter to the independently named legacy package readout. The
reverse direction recovers source completeness from the actual map's totality;
it does not infer a semantic negative from failure of a sufficient check. -/
theorem legacy_realization_iff (m : RawLaneModel) :
    ComputedFIACH.IntegratedTargetRealization m ↔ PackageLane m.assignment := by
  constructor
  · intro h
    apply (package_lane_iff _).mpr
    constructor
    · intro k _
      obtain ⟨arrow,_,hs,hp,_⟩ := h.1 .c1 (swapCell k) (primitive_cells_complete _)
      rw [hs,CSTTT.POS04.Assigned.swap_cell_involution] at hp
      exact hp
    · rw [image_eq_assembled]
      exact h.2.2.2.2
  · exact derive_package_lane m


variable {R D A O P Factor Resource Residue Stage Id History RouteId : Type} {RV : R → Type}

/-- Internal adapter: the package is POS-04; runtime components remain raw
parameters here. This is NOT the promised complete POS-04 RawHandoff value. -/
def bind (cfg : RuntimeComponents.Schema Factor Resource Stage Id History RouteId)
    (runtime : RuntimeComponents.Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (runCells : (k : Cell) → RegisterInterpreter.Expr Cell Value R RV Unit (Value k)) :
    PackageRuntime.Raw Cell Cell Value Value R RV D A O P Factor Resource Residue Stage Id History RouteId :=
  ⟨raw,cfg,runtime,runCells⟩

variable [DecidableEq Stage]

omit [DecidableEq Stage] in
theorem target_eq_image
    (cfg : RuntimeComponents.Schema Factor Resource Stage Id History RouteId)
    (runtime : RuntimeComponents.Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (runCells : (k : Cell) → RegisterInterpreter.Expr Cell Value R RV Unit (Value k))
    (a : CSTTT.POS04.Assigned.Assignment) : PackageRuntime.target (bind cfg runtime runCells) a = image a :=
  global_eq_image a

omit [DecidableEq Stage] in
theorem package_pass_iff
    (cfg : RuntimeComponents.Schema Factor Resource Stage Id History RouteId)
    (runtime : RuntimeComponents.Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (runCells : (k : Cell) → RegisterInterpreter.Expr Cell Value R RV Unit (Value k))
    (a : CSTTT.POS04.Assigned.Assignment) :
    PackageRuntime.PackagePass (bind cfg runtime runCells) a ↔ PackageLane a := valid_iff a

omit [DecidableEq Stage] in
/-- Independent semantic realization equivalence, retaining the total-cell
obligation on arbitrary partial inputs. No validity-gate failure is used to
negate the conclusion. -/
theorem realization_iff
    (cfg : RuntimeComponents.Schema Factor Resource Stage Id History RouteId)
    (runtime : RuntimeComponents.Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (runCells : (k : Cell) → RegisterInterpreter.Expr Cell Value R RV Unit (Value k))
    (a : CSTTT.POS04.Assigned.Assignment) :
    PackageRuntime.IntegratedTargetRealization (bind cfg runtime runCells) a ↔ PackageLane a := by
  constructor
  · intro h
    apply (POS04Dispatcher.p_iff a).mp
    constructor
    · intro k hk
      have ht := h.2.1 (swapCell k)
      rw [target_eq_image] at ht
      simp only [image,exchangeAssignment,Option.isSome_map] at ht
      exact (CSTTT.POS04.Assigned.swap_cell_involution k) ▸ ht
    · have ha := h.2.2
      change (package .target).accept (PackageRuntime.target (bind cfg runtime runCells) a) at ha
      rw [target_eq_image] at ha
      exact ha
  · intro hp
    exact PackageRuntime.package_soundness _ a ((package_pass_iff cfg runtime runCells a).mpr hp)

omit [DecidableEq Stage] in
theorem deletion_no_realization
    (cfg : RuntimeComponents.Schema Factor Resource Stage Id History RouteId)
    (runtime : RuntimeComponents.Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (runCells : (k : Cell) → RegisterInterpreter.Expr Cell Value R RV Unit (Value k))
    (a : CSTTT.POS04.Assigned.Assignment) (k : Cell) :
    ¬ PackageRuntime.IntegratedTargetRealization (bind cfg runtime runCells) (CSTTT.POS04.Assigned.put a k none) :=
  fun h => package_lane_missing k ((realization_iff cfg runtime runCells _).mp h)

omit [DecidableEq Stage] in
theorem realization_iff_named
    (cfg : RuntimeComponents.Schema Factor Resource Stage Id History RouteId)
    (runtime : RuntimeComponents.Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (runCells : (k : Cell) → RegisterInterpreter.Expr Cell Value R RV Unit (Value k))
    (m : RawLaneModel) :
    PackageRuntime.IntegratedTargetRealization (bind cfg runtime runCells) m.assignment ↔
      ComputedFIACH.IntegratedTargetRealization m :=
  (realization_iff cfg runtime runCells _).trans (legacy_realization_iff m).symm

end CSTTT.TargetTheory.GenericHandoff.POS04DispatchedStage
