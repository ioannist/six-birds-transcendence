import CSTTT.FullNative.ObjecthoodExecution
import CSTTT.FullNative.HistoryFactor
import CSTTT.FullNative.ViabilityFactor
import CSTTT.FullNative.InternalizedCredit
import CSTTT.FullNative.JointClaims
import CSTTT.FullNative.ClockClosure

/-! G27a: the original prose design contract on preregistered FULL-NATIVE-01.
The raw boundary has only a world and a resident address. In particular it has
no clause, predictor, operator, issuer, certificate or viability input.
This is not acceptance at the rejected G15a Frame/MemoryFrames dispatcher.
C1 includes the period-two obstruction rather than asserting false uniqueness.
C4 uses CURRENT on inside support; C7 emissions start after actions. -/
namespace CSTTT.FullNative.SharedPackage
open AccountExecution PhysicalExecution SnapshotExecution
open TargetTheory.GenericHandoff FixedPointVerifier
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

structure Raw where
  world : World
  owner : Owner

def execution (p : Raw) : Option Execution := do
  let resident ← p.world.carriers p.owner
  if resident.owner=p.owner then some ⟨p.world.accounts,resident⟩ else none

def credit (x : Execution) : Credit.CreditVerdict :=
  match x.resident.installed with
  | none => .rejected
  | some d => Credit.receiptCredit x.accounts x.resident.owner d x.resident.receipts

theorem world_rows_project (p : Raw) (x : Execution) (read : execution p=some x)
    (h : sector x) (a : Bool) :
    (nativeRows renewable p.world p.owner a).map
      (fun e => (execution ⟨e.1,p.owner⟩,e.2))=
    (rawRows renewable x a).map (fun e => (some e.1,e.2)) := by
  cases present : p.world.carriers p.owner with
  | none => simp [execution,present] at read
  | some resident =>
    by_cases owner : resident.owner=p.owner
    · have equal : x=⟨p.world.accounts,resident⟩ := by
        simpa [execution,present,owner] using read.symm
      subst x
      simp only [nativeRows,present,owner,if_true,List.map_map]
      apply List.map_congr_left
      intro e edge
      have issuedOwner : e.1.resident.owner=p.owner := by
        rw [sector_rows _ h a] at edge
        obtain ⟨f,_,eq⟩ := List.mem_map.mp edge
        have state := (congrArg Prod.fst eq).symm
        rw [state]
        exact owner
      simp [execution,mount,putOwner,issuedOwner]
    · simp [execution,present,owner] at read

/-- Raw admission is an installed/owned/charged inside resident with a computed
directional receipt audit. It is not eight independently supplied witnesses. -/
def Ready (x : Execution) : Prop :=
  sector x ∧ x.resident.current.outside=false ∧ credit x=.self

def C1 (x : Execution) : Prop :=
  Objecthood.actualP x=Objecthood.P x.resident.current ∧
  (∀ perturb squared,
    Probability states (Objecthood.stationary perturb) ∧
    Fixed states (Objecthood.closure perturb squared) (Objecthood.stationary perturb) ∧
    Objecthood.stationary perturb≠(fun _ => (1:Rat)/32) ∧
    (15:Rat)/16 ≤ mass Objecthood.core (Objecthood.stationary perturb) ∧
    Objecthood.stationaryTV perturb=(if perturb then 319/5536 else 1/22) ∧
    Objecthood.defect perturb squared=(if perturb then
      (if squared then 30675375/268435456 else 465/512)
      else (if squared then 195/2048 else 1))) ∧
  (∀ perturb squared, perturb=true ∨ squared=false → ∀ v,
    Probability states v → Fixed states (Objecthood.closure perturb squared) v →
    v=Objecthood.stationary perturb) ∧
  (Probability states (Objecthood.phaseLaw false) ∧
   Probability states (Objecthood.phaseLaw true) ∧
   Fixed states (Objecthood.closure false true) (Objecthood.phaseLaw false) ∧
   Fixed states (Objecthood.closure false true) (Objecthood.phaseLaw true) ∧
   Objecthood.phaseLaw false≠Objecthood.phaseLaw true)

def C2 (x : Execution) : Prop :=
  (∀ right, (Binding.splitExecution x right,weight x.resident.current false right)∈
    rawRows renewable x false) ∧
  Binding.actualCurrent (Binding.splitExecution x false)=
    Binding.actualCurrent (Binding.splitExecution x true) ∧
  (frame (Binding.splitExecution x false)).context=(frame (Binding.splitExecution x true)).context ∧
  classes model (Binding.splitExecution x false).resident.current≠
    classes model (Binding.splitExecution x true).resident.current

def C3 (x : Execution) : Prop :=
  (ProfileRules.count (profile model) (ProfileRules.seed (profile model))=9 ∧
   ProfileRules.count (profile model) (classes model)=16 ∧
   ProfileRules.count (profile model) (ProfileRules.second (profile model))=16) ∧
  (∀ n, ProfileRules.iterate (profile model) (1+n)=classFormula) ∧
  (∀ y, sector y →
    ((∀ word trace, WeightedFuture.law (normalizedRows renewable)
      (fun z => FullInterface.observe (frame z)) x word trace=
      WeightedFuture.law (normalizedRows renewable)
      (fun z => FullInterface.observe (frame z)) y word trace) ↔
    FullInterface.code (frame x)=FullInterface.code (frame y)))

def C4 (x : Execution) : Prop := x.resident.current.outside=false ∧
  (∀ (V : Type) (f : Execution → V), Binding.ActualAdmissible f → ∀ y z,
    sector y → sector z → y.resident.current.outside=false →
    z.resident.current.outside=false → f y=f z) ∧
  (¬ ∃ g : Nat × Nat × Nat → Nat, ∀ y,
    Reachable renewable y → y.resident.current.outside=false →
    classes model y.resident.current=g (Binding.actualCurrent y))

/-- The nine-state control is its own independently frozen actual execution,
not a reclassification of this package's asymmetric 32-state process. -/
def ControlAudit : Prop :=
  Credit.bridgeCredit Credit.scheduledCycleWorld 1=some .other ∧
  Credit.localCredit Credit.scheduledCycleWorld 1=some .rejected ∧
  Credit.localCredit Credit.flatCycleWorld 0=some .neutral ∧
  Credit.localCredit Credit.mixedCycleWorld 1=some .rejected ∧
  (∀ (f : Internalized.Flavor) (o : Owner),
    Internalized.pathCredit f (Internalized.root f o) (Internalized.cycleEnd f o)=some .neutral ∧
    Internalized.pathCredit f (Internalized.root f o) (Internalized.holonomyEnd f o)=some .neutral ∧
    Internalized.holonomyReadout f (Internalized.root f o)=some ((Internalized.parameter f)^2/144)) ∧
  (∀ (f : Internalized.Flavor) (r y : Internalized.Execution),
    Internalized.LawGate f r → Internalized.Closure renewable r y → y.receipts≠[] →
    Internalized.pathCredit f r y=some .neutral) ∧
  (∀ (f : Internalized.Flavor) (r y : Internalized.Execution),
    Internalized.LawGate f r → Internalized.Closure renewable r y →
    Internalized.receiptProduct Internalized.Receipt.weight y.receipts.reverse=
      Internalized.receiptProduct (fun receipt => Internalized.part f receipt.channel receipt.after receipt.before)
        y.receipts)

def C5 (x : Execution) : Prop := credit x=.self ∧ ControlAudit

def ClockAudit (x : Execution) : Prop :=
  (∀ word, ∃ y, ClockClosure.Route x word y) ∧
  (∀ y word, ClockClosure.Route x word y →
    (frame y).context.order=(frame x).context.order+word.length ∧
    (frame y).context.localRecords=(frame x).context.localRecords+word.length ∧
    y.resident.current.phase=ClockClosure.tickAfter word x.resident.current.phase ∧
    y.resident.owner=x.resident.owner ∧ y.resident.token=x.resident.token ∧
    y.resident.rootedRoute=x.resident.rootedRoute ∧
    y.accounts.portCursor x.resident.token=x.accounts.portCursor x.resident.token+word.length) ∧
  (∀ n, ∃ y, ClockClosure.Route x (List.replicate n false) y ∧ y.resident.current.outside=false)

def C6 (x : Execution) : Prop := credit x=.self ∧ ClockAudit x ∧
  (∀ y z, sector y → ∀ a n, (z,n)∈rawRows renewable y a →
    (frame z).context.order=(frame y).context.order+1 ∧
    (frame z).context.localRecords=(frame y).context.localRecords+1 ∧
    z.resident.current.phase= !y.resident.current.phase ∧
    z.accounts.portCursor y.resident.token=y.accounts.portCursor y.resident.token+1 ∧
    (z.resident.receipts.head?).map Receipt.issuer=some (.localGenerator y.resident.owner))

def C7 (x : Execution) : Prop :=
  (∀ y z, sector y → sector z → ∀ right word outputs,
    Binding.emittedLaw (normalizedRows renewable) (fun e => Binding.branch right e.resident.current)
      y word outputs=
    Binding.emittedLaw (normalizedRows renewable) (fun e => Binding.branch right e.resident.current)
      z word outputs) ∧
  (∀ right word outputs,
    Binding.emittedLaw (normalizedRows renewable) (fun y => Binding.branch right y.resident.current)
      (Binding.splitExecution x false) word outputs=
    Binding.emittedLaw (normalizedRows renewable) (fun y => Binding.branch right y.resident.current)
      (Binding.splitExecution x true) word outputs) ∧
  Binding.emittedLaw (normalizedRows renewable) (fun y => Binding.joint y.resident.current)
    (Binding.splitExecution x false) [false] [0]≠
  Binding.emittedLaw (normalizedRows renewable) (fun y => Binding.joint y.resident.current)
    (Binding.splitExecution x true) [false] [0] ∧
  (∀ y, sector y → FullInterface.code (frame x)=FullInterface.code (frame y) →
    ∀ word outputs, Binding.emittedLaw (normalizedRows renewable)
      (fun z => Binding.joint z.resident.current) x word outputs=
    Binding.emittedLaw (normalizedRows renewable)
      (fun z => Binding.joint z.resident.current) y word outputs)

def C8 (x : Execution) : Prop := Viability.core (Viability.quote x)=true ∧
  Viability.HistoryControlled true (Viability.historyCore true) ∧
  (∀ V : Viability.History true → Prop, Viability.HistoryControlled true V →
    ∀ h, V h → Viability.historyCore true h) ∧
  (∀ V : Viability.History false → Prop, Viability.HistoryControlled false V → ∀ h, ¬V h) ∧
  (∀ h : Viability.History false, Viability.historyCore false h →
    ∃ a y n, ∃ edge : (y,n)∈rawRows absentSupply h.1 a,
      (∀ b, rawRows absentSupply y b=[]) ∧ ¬Viability.historyCore false (Viability.extend h a y n edge)) ∧
  (∀ renew q,
    (∃ h : Viability.History renew,
      (∃ V : Viability.History renew → Prop, Viability.HistoryControlled renew V ∧ V h) ∧
      Viability.quote h.1=q) ↔ (renew=true ∧ Viability.core q=true))

inductive Clause where | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 deriving DecidableEq, Repr

def check (x : Execution) : Clause → Prop
  | .c1 => C1 x | .c2 => C2 x | .c3 => C3 x | .c4 => C4 x
  | .c5 => C5 x | .c6 => C6 x | .c7 => C7 x | .c8 => C8 x

/-- These are theorem outputs indexed by a single execution, not raw inputs. -/
structure Certificate (x : Execution) : Prop where
  c1 : C1 x
  c2 : C2 x
  c3 : C3 x
  c4 : C4 x
  c5 : C5 x
  c6 : C6 x
  c7 : C7 x
  c8 : C8 x

def Accept (p : Raw) : Prop := ∃ x, execution p=some x ∧ Ready x ∧ Certificate x
def clause (p : Raw) (c : Clause) : Prop := ∃ x, execution p=some x ∧ Ready x ∧ check x c

theorem control_audit : ControlAudit :=
  ⟨Credit.scheduled_actual_credit.1,Credit.scheduled_actual_credit.2,
    Credit.flat_actual_credit,Credit.actual_mixed_issuers_reject.1,
    Internalized.actual_cycle_neutral_and_holonomy,Internalized.actual_path_credit_neutral,
    fun f r y gate reach => (Internalized.actual_all_path_symmetry f r y gate reach).2.1⟩

theorem computed_c1 (x : Execution) (h : sector x) : C1 x := by
  refine ⟨Objecthood.actual_matrix x h,?_,?_,Objecthood.squared_unperturbed_nonunique⟩
  · intro perturb squared
    exact ⟨Objecthood.stationary_probability perturb,Objecthood.stationary_closure perturb squared,
      Objecthood.stationary_nonuniform perturb,(Objecthood.retention perturb).2,
      Objecthood.exact_stationaryTV perturb,Objecthood.exact_defect perturb squared⟩
  · intro perturb squared valid v prob fixed
    rcases valid with rfl | rfl
    · exact Objecthood.perturbed_stationary_unique squared v prob fixed
    · cases perturb
      · exact Objecthood.baseline_closure_unique v prob fixed
      · exact Objecthood.perturbed_stationary_unique false v prob fixed

theorem actual_branchwise_universal (y z : Execution) (hy : sector y) (hz : sector z)
    (right : Bool) (word : List Bool) (outputs : List Nat) :
    Binding.emittedLaw (normalizedRows renewable) (fun e => Binding.branch right e.resident.current)
      y word outputs=
    Binding.emittedLaw (normalizedRows renewable) (fun e => Binding.branch right e.resident.current)
      z word outputs := by
  rw [Binding.actual_emitted_law _ y hy,Binding.actual_emitted_law _ z hz,
    Binding.branch_all_wordsR,Binding.branch_all_wordsR]

theorem computed_certificate (x : Execution) (h : Ready x) : Certificate x := by
  refine ⟨computed_c1 x h.1,?_,?_,?_,⟨h.2.2,control_audit⟩,
    ⟨h.2.2,⟨ClockClosure.every_word_continues x h.1,
      fun y word path => ClockClosure.route_registers path h.1,
      ClockClosure.maintained_words_continue x h.1 h.2.1⟩,Credit.actual_clock_step⟩,?_,?_⟩
  · exact ⟨Binding.actual_split_supported x h.1,Binding.actual_split_current x h.1,
      Binding.actual_split_context x h.1,
      (Binding.split_promotion x.resident.current).2⟩
  · exact ⟨profile_trajectory,stable_profile_forever,fun y hy => actual_full_future_exact x y h.1 hy⟩
  · exact ⟨h.2.1,fun V f hf y z hy hz iy iz => Binding.actual_non_exposure f hf y z hy hz iy iz,
      Binding.no_historical_predictor_factor⟩
  · exact ⟨actual_branchwise_universal,(Binding.actual_split_binding x h.1).1,
      (Binding.actual_split_binding x h.1).2,
      fun y hy same word outputs => full_history_binding x y h.1 hy same word outputs⟩
  · refine ⟨?_,Viability.history_core_greatest.1,Viability.history_core_greatest.2,
      Viability.history_underfund_greatest_empty,Viability.history_absent_first_step_and_stop,
      Viability.greatest_viability_projection_exact⟩
    simp [Viability.core,Viability.quote,h.2.1,h.1.2.2]

theorem accept_from_raw (p : Raw) (x : Execution) (read : execution p=some x) (ready : Ready x) :
    Accept p := ⟨x,read,ready,computed_certificate x ready⟩

theorem certificate_checks (x : Execution) (h : Certificate x) (c : Clause) : check x c := by
  cases c
  · exact h.c1
  · exact h.c2
  · exact h.c3
  · exact h.c4
  · exact h.c5
  · exact h.c6
  · exact h.c7
  · exact h.c8

theorem accepts_all_clauses (p : Raw) (h : Accept p) (c : Clause) : clause p c := by
  obtain ⟨x,read,ready,cert⟩ := h
  exact ⟨x,read,ready,certificate_checks x cert c⟩

theorem no_independent_clause_inputs (p q : Raw) (same : execution p=execution q) (c : Clause) :
    clause p c ↔ clause q c := by unfold clause; rw [same]

theorem no_independent_certificate_input (p q : Raw) (same : execution p=execution q) :
    Accept p ↔ Accept q := by unfold Accept; rw [same]

theorem missing_resident_rejected (p : Raw) (missing : p.world.carriers p.owner=none) :
    ¬Accept p ∧ ∀ c, ¬clause p c := by
  simp [Accept,clause,execution,missing]

theorem misaddressed_resident_rejected (p : Raw) (resident : Local)
    (read : p.world.carriers p.owner=some resident) (wrong : resident.owner≠p.owner) :
    ¬Accept p ∧ ∀ c, ¬clause p c := by
  simp [Accept,clause,execution,read,wrong]

theorem raw_gate_rejected (p : Raw) (x : Execution) (read : execution p=some x)
    (bad : ¬Ready x) : ¬Accept p ∧ ∀ c, ¬clause p c := by
  constructor
  · rintro ⟨y,hy,ready,_⟩
    have equal := Option.some.inj (read.symm.trans hy)
    exact bad (equal ▸ ready)
  · intro c
    rintro ⟨y,hy,ready,_⟩
    have equal := Option.some.inj (read.symm.trans hy)
    exact bad (equal ▸ ready)

theorem missing_program_rejected (p : Raw) (x : Execution) (read : execution p=some x)
    (missing : x.resident.installed=none) : ¬Accept p ∧ ∀ c, ¬clause p c := by
  apply raw_gate_rejected p x read
  intro ready
  have installed := ready.1.1
  rw [missing] at installed
  contradiction

theorem missing_account_rejected (p : Raw) (x : Execution) (read : execution p=some x)
    (missing : x.accounts.allocation x.resident.token≠some (.localGenerator x.resident.owner)) :
    ¬Accept p ∧ ∀ c, ¬clause p c :=
  raw_gate_rejected p x read (fun ready => missing ready.1.2.1)

theorem depleted_account_rejected (p : Raw) (x : Execution) (read : execution p=some x)
    (missing : x.accounts.charge x.resident.token=false) : ¬Accept p ∧ ∀ c, ¬clause p c := by
  apply raw_gate_rejected p x read
  intro ready
  have charged := ready.1.2.2
  rw [missing] at charged
  contradiction

theorem accepted_history_viable (p : Raw) (accepted : Accept p) :
    ∃ h : Viability.History true, execution p=some h.1 ∧
      (∃ V : Viability.History true → Prop, Viability.HistoryControlled true V ∧ V h) := by
  obtain ⟨x,read,ready,cert⟩ := accepted
  let history : Viability.History true := ⟨x,.root x ⟨ready.1.1,ready.1.2.1⟩⟩
  refine ⟨history,read,?_⟩
  apply (Viability.history_viable_iff true history).mpr
  exact ⟨rfl,cert.c8.1⟩

end CSTTT.FullNative.SharedPackage
