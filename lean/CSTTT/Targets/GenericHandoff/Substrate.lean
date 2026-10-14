import CSTTT.Package.FiniteGluing

/-! G6d-1: dependent immutable cells. No clause evaluator or handoff verdict
is a parameter of this substrate. Source and target namespaces may differ.
Finite cover enumeration selects a local view constructively; adjacency is raw
and scoped connectivity is checked independently. -/
namespace CSTTT.TargetTheory.GenericHandoff

abbrev Assignment (Cell : Type) (Value : Cell → Type) :=
  (k : Cell) → Option (Value k)

section Cells
variable {Cell : Type} {Value : Cell → Type} [DecidableEq Cell]

def put (a : Assignment Cell Value) (k : Cell) (v : Option (Value k)) : Assignment Cell Value :=
  fun j => if h : j = k then h.symm ▸ v else a j
@[simp] theorem put_same (a : Assignment Cell Value) (k : Cell) (v : Option (Value k)) :
    put a k v k = v := by simp [put]
@[simp] theorem put_other (a : Assignment Cell Value) (k j : Cell)
    (v : Option (Value k)) (h : j ≠ k) : put a k v j = a j := by simp [put,h]

def decode (scope : List Cell) (a : Assignment Cell Value) : Assignment Cell Value :=
  fun k => if k ∈ scope then a k else none

def Agrees (scope : List Cell) (a b : Assignment Cell Value) : Prop :=
  ∀ k ∈ scope, a k = b k

def Complete (scope : List Cell) (a : Assignment Cell Value) : Prop :=
  ∀ k ∈ scope, (a k).isSome = true

theorem decoder_locality {scope : List Cell} {a b : Assignment Cell Value}
    (h : Agrees scope a b) : decode scope a = decode scope b := by
  funext k
  by_cases hk : k ∈ scope
  · simp [decode,hk,h k hk]
  · simp [decode,hk]

theorem decoder_outside (scope : List Cell) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∉ scope) : decode scope a k = none := by simp [decode,hk]

theorem decoder_missing (scope : List Cell) (a : Assignment Cell Value) (k : Cell)
    (hk : a k = none) : decode scope a k = none := by simp [decode,hk]

theorem missing_rejected (scope : List Cell) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ scope) : ¬ Complete scope (put a k none) := by
  intro h
  have hm := h k hk
  simp at hm

omit [DecidableEq Cell] in
theorem complete_locality {scope : List Cell} {a b : Assignment Cell Value}
    (h : Agrees scope a b) : Complete scope a ↔ Complete scope b := by
  unfold Complete
  constructor <;> intro hc k hk
  · rw [← h k hk]; exact hc k hk
  · rw [h k hk]; exact hc k hk
end Cells

/-- An immutable logical slot is a view onto a shared typed primitive cell. -/
structure CellView (Cell : Type) (Value : Cell → Type) (Output : Type) where
  cell : Cell
  project : Value cell → Output

def CellView.read {Cell : Type} {Value : Cell → Type} {Output : Type}
    (v : CellView Cell Value Output) (a : Assignment Cell Value) : Option Output :=
  (a v.cell).map v.project

theorem view_locality {Cell : Type} {Value : Cell → Type} {Output : Type}
    (v : CellView Cell Value Output) {a b : Assignment Cell Value}
    (h : a v.cell = b v.cell) : v.read a = v.read b := by simp [CellView.read,h]

theorem view_missing {Cell : Type} {Value : Cell → Type} {Output : Type}
    (v : CellView Cell Value Output) (a : Assignment Cell Value)
    (h : a v.cell = none) : v.read a = none := by simp [CellView.read,h]

/-- Raw typed map syntax with its fixed instruction semantics. This translates
primitive values, never computes or stores acceptance. -/
structure TranslationLanguage (SC TC : Type) (SV : SC → Type) (TV : TC → Type) where
  Instruction : SC → TC → Type
  execute : {s : SC} → {t : TC} → Instruction s t → SV s → Option (TV t)

structure CellArrow {SC TC : Type} {SV : SC → Type} {TV : TC → Type}
    (L : TranslationLanguage SC TC SV TV) (target : TC) where
  source : SC
  instruction : L.Instruction source target

abbrev Stage {SC TC Index : Type} {SV : SC → Type} {TV : TC → Type}
    (L : TranslationLanguage SC TC SV TV) :=
  Index → (target : TC) → Option (CellArrow L target)

section Stage
variable {SC TC Index : Type} {SV : SC → Type} {TV : TC → Type}
  [DecidableEq TC] (L : TranslationLanguage SC TC SV TV)

def mappedLocal (a : Assignment SC SV) (stage : Stage (Index := Index) L)
    (scopes : Index → List TC) (i : Index) : Assignment TC TV := fun k =>
  if k ∈ scopes i then
    (stage i k).bind fun arrow => (a arrow.source).bind (L.execute arrow.instruction)
  else none

def StageTotal (a : Assignment SC SV) (stage : Stage (Index := Index) L)
    (scopes : Index → List TC) : Prop :=
  ∀ i k, k ∈ scopes i → ∃ arrow, stage i k = some arrow ∧
    (a arrow.source).isSome = true ∧ ∀ v, L.execute arrow.instruction v ≠ none

def ReferenceCheck (stage reference : Stage (Index := Index) L)
    (scopes : Index → List TC) : Prop :=
  ∀ i k, k ∈ scopes i → (stage i k).map (fun arrow => arrow.source) =
    (reference i k).map (fun arrow => arrow.source)

omit [DecidableEq TC] in
theorem coordinate_change_rejected {stage reference : Stage (Index := Index) L}
    {scopes : Index → List TC} {i : Index} {k : TC} (hk : k ∈ scopes i)
    (h : (stage i k).map (fun arrow => arrow.source) ≠
      (reference i k).map (fun arrow => arrow.source)) : ¬ ReferenceCheck L stage reference scopes :=
  fun hr => h (hr i k hk)

def ValuePreserving (a : Assignment SC SV) (stage reference : Stage (Index := Index) L)
    (scopes : Index → List TC) : Prop :=
  ∀ i k, k ∈ scopes i → mappedLocal L a stage scopes i k = mappedLocal L a reference scopes i k

def SourceCoverage (stage : Stage (Index := Index) L) (sourceScopes : Index → List SC)
    (targetScopes : Index → List TC) : Prop :=
  ∀ i s, s ∈ sourceScopes i → ∃ t, t ∈ targetScopes i ∧
    ∃ arrow, stage i t = some arrow ∧ arrow.source = s

theorem mapped_complete {a : Assignment SC SV} {stage : Stage (Index := Index) L}
    {scopes : Index → List TC} (h : StageTotal L a stage scopes) (i : Index) :
    Complete (scopes i) (mappedLocal L a stage scopes i) := by
  intro k hk
  obtain ⟨arrow,ha,hv,hop⟩ := h i k hk
  simp only [mappedLocal,hk,if_true,ha,Option.bind_some]
  cases hs : a arrow.source with
  | none => rw [hs] at hv; contradiction
  | some v =>
    simp only [Option.bind_some]
    cases he : L.execute arrow.instruction v with
    | none => exact False.elim (hop v he)
    | some w => rfl

omit [DecidableEq TC] in
theorem missing_arrow_rejected {a : Assignment SC SV} {stage : Stage (Index := Index) L}
    {scopes : Index → List TC} {i : Index} {k : TC} (hk : k ∈ scopes i)
    (hm : stage i k = none) : ¬ StageTotal L a stage scopes := by
  intro h
  obtain ⟨arrow,ha,_⟩ := h i k hk
  rw [hm] at ha
  contradiction

omit [DecidableEq TC] in
theorem missing_source_rejected {a : Assignment SC SV} {stage : Stage (Index := Index) L}
    {scopes : Index → List TC} {i : Index} {k : TC} {arrow : CellArrow L k}
    (hk : k ∈ scopes i) (ha : stage i k = some arrow) (hm : a arrow.source = none) :
    ¬ StageTotal L a stage scopes := by
  intro h
  obtain ⟨other,ho,hv,_⟩ := h i k hk
  have he : other = arrow := Option.some.inj (ho.symm.trans ha)
  subst other
  simp [hm] at hv

theorem value_change_rejected {a : Assignment SC SV} {stage reference : Stage (Index := Index) L}
    {scopes : Index → List TC} {i : Index} {k : TC} (hk : k ∈ scopes i)
    (h : mappedLocal L a stage scopes i k ≠ mappedLocal L a reference scopes i k) :
    ¬ ValuePreserving L a stage reference scopes := fun hv => h (hv i k hk)
omit [DecidableEq TC] in
theorem broken_instruction_rejected {a : Assignment SC SV} {stage : Stage (Index := Index) L}
    {scopes : Index → List TC} {i : Index} {k : TC} {arrow : CellArrow L k}
    (hk : k ∈ scopes i) (ha : stage i k = some arrow) (v : SV arrow.source)
    (hm : L.execute arrow.instruction v = none) : ¬ StageTotal L a stage scopes := by
  intro h
  obtain ⟨other,ho,_,hop⟩ := h i k hk
  have he : other = arrow := Option.some.inj (ho.symm.trans ha)
  subst other
  exact hop v hm

omit [DecidableEq TC] in
theorem source_coverage_rejected {stage : Stage (Index := Index) L}
    {sourceScopes : Index → List SC} {targetScopes : Index → List TC}
    {i : Index} {s : SC} (hs : s ∈ sourceScopes i)
    (h : ∀ t, t ∈ targetScopes i → ∀ arrow, stage i t = some arrow → arrow.source ≠ s) :
    ¬ SourceCoverage L stage sourceScopes targetScopes := by
  intro hc
  obtain ⟨t,ht,arrow,ha,he⟩ := hc i s hs
  exact h t ht arrow ha he
end Stage

section Cover
variable {Index Cell : Type} {Value : Cell → Type} [DecidableEq Cell]

structure RawCover (Index Cell : Type) where
  indices : List Index
  scopes : Index → List Cell
  adjacent : Index → Index → Bool

def CoverCheck (r : RawCover Index Cell) : Prop :=
  (∀ k, ∃ i, i ∈ r.indices ∧ k ∈ r.scopes i) ∧
  ∀ i j k, k ∈ r.scopes i → k ∈ r.scopes j →
    CSTTT.PackageTheory.ScopedReach (fun a b => r.adjacent a b = true)
      (fun c k => k ∈ r.scopes c) k i j

def DependenciesCovered (r : RawCover Index Cell) (required : Index → List Cell) : Prop :=
  ∀ i k, k ∈ required i → k ∈ r.scopes i

omit [DecidableEq Cell] in
theorem missing_dependency_scope_rejected (r : RawCover Index Cell)
    (required : Index → List Cell) {i : Index} {k : Cell}
    (hk : k ∈ required i) (hm : k ∉ r.scopes i) : ¬ DependenciesCovered r required :=
  fun h => hm (h i k hk)

def EdgeCompatible (r : RawCover Index Cell) (locals : Index → Assignment Cell Value) : Prop :=
  ∀ i j k, r.adjacent i j = true → k ∈ r.scopes i → k ∈ r.scopes j → locals i k = locals j k

/-- Select by coverage, NOT by presence of a value. A missing chosen local must
remain missing; another local cannot silently supply a fallback. -/
def firstCover (scopes : Index → List Cell) (k : Cell) : List Index → Option Index
  | [] => none
  | i :: rest => if k ∈ scopes i then some i else firstCover scopes k rest

theorem firstCover_supported {scopes : Index → List Cell} {k : Cell} {is : List Index}
    {i : Index} (h : firstCover scopes k is = some i) : i ∈ is ∧ k ∈ scopes i := by
  induction is with
  | nil => simp [firstCover] at h
  | cons j rest ih =>
    by_cases hk : k ∈ scopes j
    · simp [firstCover,hk] at h
      subst i
      exact ⟨by simp,hk⟩
    · have hr : firstCover scopes k rest = some i := by simpa [firstCover,hk] using h
      obtain ⟨hi,hs⟩ := ih hr
      exact ⟨by simp [hi],hs⟩

theorem firstCover_exists {scopes : Index → List Cell} {k : Cell} {is : List Index}
    (h : ∃ i, i ∈ is ∧ k ∈ scopes i) : ∃ i, firstCover scopes k is = some i := by
  induction is with
  | nil => simp at h
  | cons j rest ih =>
    by_cases hk : k ∈ scopes j
    · exact ⟨j,by simp [firstCover,hk]⟩
    · obtain ⟨i,hi,hs⟩ := h
      have hm : i ∈ rest := by
        rcases List.mem_cons.mp hi with he | he
        · subst i; contradiction
        · exact he
      obtain ⟨i,he⟩ := ih ⟨i,hm,hs⟩
      exact ⟨i,by simpa [firstCover,hk] using he⟩

def glued (r : RawCover Index Cell) (locals : Index → Assignment Cell Value) : Assignment Cell Value :=
  fun k => (firstCover r.scopes k r.indices).bind (fun i => locals i k)

theorem glued_restricts (r : RawCover Index Cell) (locals : Index → Assignment Cell Value)
    (hc : CoverCheck r) (he : EdgeCompatible r locals) (i : Index) (k : Cell)
    (hk : k ∈ r.scopes i) : glued r locals k = locals i k := by
  obtain ⟨j,hj⟩ := firstCover_exists (hc.1 k)
  have hs := (firstCover_supported hj).2
  have hl := CSTTT.PackageTheory.localEqualityAlongScopedReach
    (localAssignment := fun i k => (⟨k,locals i k⟩ : Sigma (fun k => Option (Value k))))
    (fun i j k ha hi hj => congrArg (Sigma.mk k) (he i j k ha hi hj))
    (hc.2 j i k hs hk)
  have hv : locals j k = locals i k := eq_of_heq (Sigma.mk.inj hl).2
  simp only [glued,hj,Option.bind_some]
  exact hv

omit [DecidableEq Cell] in
theorem covered_cells_enumerate (r : RawCover Index Cell) (hc : CoverCheck r) (k : Cell) :
    k ∈ r.indices.flatMap r.scopes := by
  obtain ⟨i,hi,hk⟩ := hc.1 k
  exact List.mem_flatMap.mpr ⟨i,hi,hk⟩

theorem glued_unique (r : RawCover Index Cell) (locals : Index → Assignment Cell Value)
    (hc : CoverCheck r) (he : EdgeCompatible r locals) (other : Assignment Cell Value)
    (hr : ∀ i k, k ∈ r.scopes i → other k = locals i k) : other = glued r locals := by
  funext k
  obtain ⟨i,_,hk⟩ := hc.1 k
  exact (hr i k hk).trans (glued_restricts r locals hc he i k hk).symm

omit [DecidableEq Cell] in
theorem restrictions_imply_compatible (r : RawCover Index Cell)
    (locals : Index → Assignment Cell Value) (global : Assignment Cell Value)
    (hr : ∀ i k, k ∈ r.scopes i → global k = locals i k) : EdgeCompatible r locals := by
  intro i j k _ hi hj
  exact (hr i k hi).symm.trans (hr j k hj)

theorem glued_complete (r : RawCover Index Cell) (locals : Index → Assignment Cell Value)
    (hc : CoverCheck r) (he : EdgeCompatible r locals)
    (hl : ∀ i, Complete (r.scopes i) (locals i)) : Complete (r.indices.flatMap r.scopes) (glued r locals) := by
  intro k _
  obtain ⟨i,hi,hk⟩ := hc.1 k
  rw [glued_restricts r locals hc he i k hk]
  exact hl i k hk

omit [DecidableEq Cell] in
theorem incompatible_overlap_rejected (r : RawCover Index Cell)
    (locals : Index → Assignment Cell Value) {i j : Index} {k : Cell}
    (ha : r.adjacent i j = true) (hi : k ∈ r.scopes i) (hj : k ∈ r.scopes j)
    (hne : locals i k ≠ locals j k) : ¬ EdgeCompatible r locals := fun h => hne (h i j k ha hi hj)

omit [DecidableEq Cell] in
theorem uncovered_cell_rejected (r : RawCover Index Cell) (k : Cell)
    (h : ∀ i ∈ r.indices, k ∉ r.scopes i) : ¬ CoverCheck r := by
  intro hc
  obtain ⟨i,hi,hk⟩ := hc.1 k
  exact h i hi hk
omit [DecidableEq Cell] in
theorem disconnected_cover_rejected (r : RawCover Index Cell) {i j : Index} {k : Cell}
    (hi : k ∈ r.scopes i) (hj : k ∈ r.scopes j) (hne : i ≠ j)
    (h : ∀ a b, k ∈ r.scopes a → k ∈ r.scopes b → r.adjacent a b = true → a = b) :
    ¬ CoverCheck r := by
  intro hc
  have path := hc.2 i j k hi hj
  have path_eq : ∀ {a b}, CSTTT.PackageTheory.ScopedReach
      (fun a b => r.adjacent a b = true) (fun c k => k ∈ r.scopes c) k a b → a = b := by
    intro a b hp
    induction hp with
    | refl _ _ => rfl
    | step ha hb hab tail ih => exact (h _ _ ha hb hab).trans ih
  exact hne (path_eq path)
end Cover

/-- Reindexing is a raw typed map. Shared source cells are read once through
one immutable namespace, even when multiple target views refer to them. -/
structure TypedReindex (SC TC : Type) (SV : SC → Type) (TV : TC → Type) where
  source : TC → SC
  translate : (t : TC) → SV (source t) → TV t

def TypedReindex.pullback {SC TC : Type} {SV : SC → Type} {TV : TC → Type}
    (r : TypedReindex SC TC SV TV) (a : Assignment SC SV) : Assignment TC TV :=
  fun t => (a (r.source t)).map (r.translate t)

theorem reindex_missing {SC TC : Type} {SV : SC → Type} {TV : TC → Type}
    (r : TypedReindex SC TC SV TV) (a : Assignment SC SV) (t : TC)
    (h : a (r.source t) = none) : r.pullback a t = none := by
  simp [TypedReindex.pullback,h]

/-- Sequencing is defined, and its execution equation propagates absence.
This is the primitive closure law needed by the forward TTH-07 sketch. -/
def sequenceLanguage {SC MC TC : Type} {SV : SC → Type} {MV : MC → Type} {TV : TC → Type}
    (a : TranslationLanguage SC MC SV MV) (b : TranslationLanguage MC TC MV TV) :
    TranslationLanguage SC TC SV TV :=
  ⟨(fun s t => Sigma (fun m => a.Instruction s m × b.Instruction m t)),
    fun instructions v => (a.execute instructions.2.1 v).bind (b.execute instructions.2.2)⟩

theorem sequence_execution {SC MC TC : Type} {SV : SC → Type} {MV : MC → Type} {TV : TC → Type}
    (a : TranslationLanguage SC MC SV MV) (b : TranslationLanguage MC TC MV TV)
    {s : SC} {m : MC} {t : TC} (f : a.Instruction s m) (g : b.Instruction m t) (v : SV s) :
    (sequenceLanguage a b).execute ⟨m,f,g⟩ v = (a.execute f v).bind (b.execute g) := rfl
end CSTTT.TargetTheory.GenericHandoff
