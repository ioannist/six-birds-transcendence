import CSTTT.POS04.Assigned.Substrate

/-! Assignment-sensitive C1–C3. Authority: M3_model_spec.md:17–19,30–31.
The only fallbacks are totalization of failed decodes; Complete gates reject
all missing inputs. No imported verdict decides acceptance. C1 reconstruction
anchors the assigned rows/C/U to the exact T1 object before transporting its
universal uniqueness theorem. C2 and C3 run their raw algorithms on decoded data.
-/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit

structure Inputs where
  rows : KState → Action → List (Ambient × Nat)
  positions : KState → Nat
  hazards : Ambient → Bool
  lower : LowerRule
  policy : KState → Action
  prototypes : List KState
  publishedP : I → I → Nat
  publishedC : I → J → Nat
  publishedU : J → I → Nat
  publishedM : KState → Nat
  audit : AuditParameters

def inputs (d : Assignment) (tag : Tag) : Inputs :=
  ⟨(d (.rows tag)).getD (canonicalValue (.rows tag)),
   (d .positions).getD (canonicalValue .positions),
   (d .hazards).getD (canonicalValue .hazards),
   (d (.lower tag)).getD (canonicalValue (.lower tag)),
   (d .policy).getD (canonicalValue .policy),
   (d .prototypes).getD (canonicalValue .prototypes),
   (d .publishedP).getD (canonicalValue .publishedP),
   (d .publishedC).getD (canonicalValue .publishedC),
   (d .publishedU).getD (canonicalValue .publishedU),
   (d .publishedM).getD (canonicalValue .publishedM),
   (d .audit).getD (canonicalValue .audit)⟩

def clauseInputs (a : Assignment) (tag : Tag) (c : Clause) : Inputs :=
  inputs (decode (clauseScope tag c) a) tag

theorem inputs_locality {a b : Assignment} {tag : Tag} {c : Clause}
    (h : Agrees (clauseScope tag c) a b) :
    clauseInputs a tag c = clauseInputs b tag c := by
  unfold clauseInputs
  rw [decoder_locality h]

def predictive (d : Inputs) (s : KState) : Nat × List (List Bool) :=
  (d.positions s, actions.map fun a =>
    (d.rows s a).map fun e => d.hazards e.1)

def lower (d : Inputs) (s : KState) : Nat × Option KState :=
  (d.positions s, if d.lower = .stateLabel then some s else none)

def C2Rule (d : Inputs) : Prop :=
  lower d .p1w0 = lower d .p1w1 ∧ predictive d .p1w0 ≠ predictive d .p1w1

def seed (d : Inputs) (s : KState) : Nat :=
  if d.lower = .stateLabel then (index s).val else d.positions s

def mass (d : Inputs) (classes : KState → Nat) (s : KState)
    (a : Action) (block : Nat) : Nat :=
  (d.rows s a).foldl (fun total e =>
    if blockOf classes e.1 = block then total + e.2 else total) 0

def signature (d : Inputs) (classes : KState → Nat) (s : KState) :
    Nat × List (List Nat) :=
  (classes s, actions.map fun a => (List.range 12).map fun b => mass d classes s a b)

def step (d : Inputs) (classes : KState → Nat) (s : KState) : Nat :=
  ((kernel.map (signature d classes)).eraseDups).idxOf (signature d classes s)
def first (d : Inputs) := step d (seed d)
def second (d : Inputs) := step d (first d)

def C3Rule (d : Inputs) : Prop :=
  classCount (seed d) = 6 ∧ classCount (first d) = 7 ∧
  classCount (second d) = 7 ∧ samePartition (first d) (second d) ∧
  samePartition (second d) (predictive d)

def classOrder (d : Inputs) := d.prototypes.map (predictive d)
def fiberSize (d : Inputs) (s : KState) :=
  (kernel.filter fun t => predictive d s == predictive d t).length

def rawC (d : Inputs) (i : I) (k : J) : Nat :=
  if predictive d (stateAt i) = (classOrder d).getD k.val (0,[]) then 1 else 0

def rawU (d : Inputs) (k : J) (j : I) : Nat :=
  if predictive d (stateAt j) = (classOrder d).getD k.val (0,[]) then
    2 / fiberSize d (stateAt j) else 0

def rowP (d : Inputs) (i j : I) : Nat :=
  rowWeight (d.rows (stateAt i) (d.policy (stateAt i))) (stateAt j)

/-- Raw column order, support coverage, and reconstruction equations.
The imported P/C/U cells are comparison tables, not class labels used as M. -/
def TablesReconstructed (d : Inputs) : Prop :=
  indices = List.finRange 10 ∧ d.prototypes.length = 7 ∧
  ((List.finRange 7).all fun k =>
    ((indices.filter fun i => d.publishedC i k == 1).head?) ==
      some (index (d.prototypes.getD k.val .p0w0))) = true ∧
  (classOrder d).Nodup ∧
  (kernel.all fun s => decide (predictive d s ∈ classOrder d)) = true ∧
  (∀ s t : KState,
    rowWeight (d.rows s (d.policy s)) t = d.publishedP (index s) (index t)) ∧
  (indices.all fun i => (List.finRange 7).all fun k =>
    rawC d i k == d.publishedC i k) = true ∧
  ((List.finRange 7).all fun k => indices.all fun j =>
    rawU d k j == d.publishedU k j) = true ∧
  (∀ i j : I, sum7 (fun k => rawC d i k * rawU d k j) =
    sum7 (fun k => d.publishedC i k * d.publishedU k j))

/-- The exact epsilon and tau are the T1 protocol, not tunable thresholds.
An arbitrary raw assignment is admitted only after these equations are checked. -/
def T1Anchors (d : Inputs) : Prop :=
  d.audit = ⟨c1Tau,c1Epsilon,c1RetentionThreshold⟩ ∧
  d.publishedP = pNum ∧ d.publishedC = cIndicator ∧ d.publishedU = uPrototypeNum

def computedP (d : Inputs) : ScaledMatrix := ⟨4,rowP d⟩
def computedPeps (d : Inputs) : ScaledMatrix :=
  ⟨320,fun i j => 75 * rowP d i j + 2⟩
def computedCU (d : Inputs) : ScaledMatrix :=
  ⟨2,fun i j => sum7 (fun k => rawC d i k * rawU d k j)⟩
def computedE (d : Inputs) := product (product (computedPeps d) (computedPeps d)) (computedCU d)
def computedEzero (d : Inputs) := product (product (computedP d) (computedP d)) (computedCU d)

/-- Audit of the computed matrix, including quantification over *all*
probability fixed distributions. This is not a stored candidate verdict. -/
def C1Audit (d : Inputs) : Prop :=
  IsProbability pi ∧ IsFixed (computedE d) pi ∧
  (∀ μ : I → Rat, IsProbability μ → IsFixed (computedE d) μ → μ = pi) ∧
  pi ≠ uniform ∧ coreMass pi = 77/80 ∧ coreMass pi ≥ d.audit.retention ∧
  tvFromCoreUniform pi = 3/80 ∧ defect (computedE d) = 78795/524288 ∧
  defect (computedEzero d) = 1/8

/-- Entries really are positive finite support, with the declared four-unit
scale. Empty rows are forbidden actions, as in T1; nonempty rows sum to four. -/
def RowsValid (d : Inputs) : Prop :=
  (kernel.all fun s => actions.all fun a =>
    let row := d.rows s a
    let total := row.foldl (fun n e => n + e.2) 0
    row.all (fun e => decide (e.2 > 0 ∧ e.1 ∈ ambientStates)) &&
    (total == 0 || total == 4)) = true

def Ready (a : Assignment) (tag : Tag) (c : Clause) : Prop :=
  Complete (clauseScope tag c) a ∧ RowsValid (clauseInputs a tag c)

def C1Gate (a : Assignment) (tag : Tag) : Prop :=
  Ready a tag .c1 ∧
  T1Anchors (clauseInputs a tag .c1) ∧ TablesReconstructed (clauseInputs a tag .c1)
def C1Accept (a : Assignment) (tag : Tag) : Prop :=
  C1Gate a tag ∧ C1Audit (clauseInputs a tag .c1)
def MLinked (d : Inputs) : Prop :=
  d.publishedM = (fun s => mClass (index s)) ∧
  samePartition (predictive d) d.publishedM

def C2Gate (a : Assignment) (tag : Tag) : Prop :=
  Ready a tag .c2 ∧ MLinked (clauseInputs a tag .c2)
def C2Accept (a : Assignment) (tag : Tag) : Prop :=
  C2Gate a tag ∧ C2Rule (clauseInputs a tag .c2)
def C3Gate (a : Assignment) (tag : Tag) : Prop :=
  Ready a tag .c3 ∧ MLinked (clauseInputs a tag .c3)
def C3Accept (a : Assignment) (tag : Tag) : Prop :=
  C3Gate a tag ∧ C3Rule (clauseInputs a tag .c3)

theorem complete_locality {a b : Assignment} {scope : List Cell}
    (h : Agrees scope a b) : Complete scope a ↔ Complete scope b := by
  unfold Complete
  constructor <;> intro hc k hk
  · rw [← h k hk]; exact hc k hk
  · rw [h k hk]; exact hc k hk

theorem ready_locality {a b : Assignment} {tag : Tag} {c : Clause}
    (h : Agrees (clauseScope tag c) a b) : Ready a tag c ↔ Ready b tag c := by
  unfold Ready
  rw [complete_locality h,inputs_locality h]

theorem c1_gate_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c1) a b) : C1Gate a tag ↔ C1Gate b tag := by
  unfold C1Gate
  rw [ready_locality h,inputs_locality h]
theorem c1_acceptance_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c1) a b) : C1Accept a tag ↔ C1Accept b tag := by
  unfold C1Accept
  rw [c1_gate_locality h,inputs_locality h]
theorem c2_gate_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c2) a b) : C2Gate a tag ↔ C2Gate b tag :=
  by
    unfold C2Gate
    rw [ready_locality h,inputs_locality h]
theorem c2_acceptance_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c2) a b) : C2Accept a tag ↔ C2Accept b tag := by
  unfold C2Accept
  rw [c2_gate_locality h,inputs_locality h]
theorem c3_gate_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c3) a b) : C3Gate a tag ↔ C3Gate b tag :=
  by
    unfold C3Gate
    rw [ready_locality h,inputs_locality h]
theorem c3_acceptance_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c3) a b) : C3Accept a tag ↔ C3Accept b tag := by
  unfold C3Accept
  rw [c3_gate_locality h,inputs_locality h]

/-- Reconstruction is a mathematical bridge to the existing T1 audit. It
identifies the *computed* matrices, not just a displayed candidate distribution. -/
theorem reconstructed_matrices (d : Inputs) (ha : T1Anchors d)
    (hr : TablesReconstructed d) :
    computedP d = P ∧ computedPeps d = Peps ∧ computedCU d = CU := by
  have hp : rowP d = pNum := by
    funext i j
    have h := hr.2.2.2.2.2.1 (stateAt i) (stateAt j)
    simpa [rowP, index_stateAt, ha.2.1] using h
  have hcu : (fun i j => sum7 (fun k => rawC d i k * rawU d k j)) = CU.num := by
    funext i j
    rw [hr.2.2.2.2.2.2.2.2 i j, ha.2.2.1, ha.2.2.2]
    exact declared_cu_is_t1 i j
  exact ⟨by simp [computedP,P,hp], by simp [computedPeps,Peps,hp],
    by simpa [computedCU, CU] using congrArg (ScaledMatrix.mk 2) hcu⟩

theorem c1_audit_from_reconstruction (d : Inputs) (ha : T1Anchors d)
    (hr : TablesReconstructed d) : C1Audit d := by
  rcases reconstructed_matrices d ha hr with ⟨hp,hpe,hcu⟩
  have he : computedE d = E2eps := by
    simp [computedE,hpe,hcu,E2eps,Peps2]
  have hz : computedEzero d = E2zero := by
    simp [computedEzero,hp,hcu,E2zero,P2]
  have ht : d.audit.retention = 3/4 := by
    rw [ha.1]; rfl
  rw [C1Audit,he,hz,ht]
  exact ⟨pi_probability,pi_fixed,pi_unique,pi_nonuniform,pi_core_mass,
    pi_core_retention,pi_tv_from_core_uniform,e2eps_defect,e2zero_defect⟩

theorem c1_accept_iff_gate (a : Assignment) (tag : Tag) :
    C1Accept a tag ↔ C1Gate a tag := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h,c1_audit_from_reconstruction _ h.2.1 h.2.2⟩

end CSTTT.POS04.Assigned
