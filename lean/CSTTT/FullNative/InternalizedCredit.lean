import CSTTT.FullNative.InternalizedExecution
import CSTTT.FullNative.DriveClock

namespace CSTTT.FullNative.Internalized
open AccountExecution
open CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeGeneratorCreditPrototype
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def receiptOK (f : Flavor) (x : Execution) (r : Receipt) : Bool := decide
  (r.issuer=dispatchActor x r.channel ∧ r.token=dispatchToken x r.channel ∧
    x.accounts.allocation r.token=some r.issuer ∧ r.serial%4=r.token.val ∧
    r.weight=part f r.channel r.before r.after ∧ 0<r.weight ∧ r.energy=some ())
def consecutive : List Receipt → Bool
  | [] => true
  | [_] => true
  | r::s::rest => decide (r.before=s.after) && consecutive (s::rest)
def receiptAudit (f : Flavor) (x : Execution) : Bool :=
  !x.receipts.isEmpty && x.receipts.all (receiptOK f x) && consecutive x.receipts &&
    decide (x.receipts.head?.map Receipt.after=some x.current)

theorem receipt_ok_retained (f : Flavor) (x : Execution) (c : Channel)
    (t : State) (w : Rat) (r : Receipt) :
    receiptOK f (advance renewable x c t w) r=receiptOK f x r := rfl

theorem issued_receipt_ok (f : Flavor) (x : Execution) (sector : Sector x)
    (c : Channel) (t : State) (w : Rat) (law : w=part f c x.current t) (positive : 0<w) :
    receiptOK f x (issue renewable x c t w)=true := by
  have bound := (dispatchToken x c).isLt
  have serial : (4*x.accounts.portCursor (dispatchToken x c)+(dispatchToken x c).val)%4=
      (dispatchToken x c).val := by omega
  have allocated : x.accounts.allocation (dispatchToken x c)=some (dispatchActor x c) := by
    cases c
    · exact sector.2.1
    · exact sector.2.2.1
  have positivePart : 0<part f c x.current t := by rwa [←law]
  simp [receiptOK,issue,serial,allocated,law,positivePart,renewable]

theorem closure_receipt_integrity (f : Flavor) (r x : Execution) (gate : LawGate f r)
    (reach : Closure renewable r x) :
    x.receipts.all (receiptOK f x)=true ∧ consecutive x.receipts=true ∧
    (∀ head, x.receipts.head?=some head → head.after=x.current) := by
  induction reach with
  | root => simp [gate.1,consecutive]
  | @step x y w reach edge ih =>
    obtain ⟨sector,d,installed,law⟩ := gate.2 x reach
    obtain ⟨e,c,t,hp,_,_,_,positive,rfl,_⟩ := supported_step _ _ _ _ edge
    have equal : e=d := Option.some.inj (hp.symm.trans installed)
    subst e
    have ok := issued_receipt_ok f x sector c t (d.weights c x.current t) (law c t) positive
    refine ⟨?_,?_,?_⟩
    · change (receiptOK f x (issue renewable x c t (d.weights c x.current t)) &&
        x.receipts.all (receiptOK f x))=true
      rw [ok,ih.1]
      rfl
    · cases hs : x.receipts with
      | nil => simp [advance,hs,consecutive]
      | cons head rest =>
        have ends := ih.2.2 head (by simp [hs])
        simpa [advance,consecutive,issue,hs,ends] using ih.2.1
    · intro head equal
      have same : issue renewable x c t (d.weights c x.current t)=head := Option.some.inj equal
      rw [←same]
      rfl

theorem actual_receipt_audit (f : Flavor) (r x : Execution) (gate : LawGate f r)
    (reach : Closure renewable r x) (nonempty : x.receipts≠[]) : receiptAudit f x=true := by
  obtain ⟨all,chain,head⟩ := closure_receipt_integrity f r x gate reach
  cases hs : x.receipts with
  | nil => exact (nonempty hs).elim
  | cons first rest =>
    have ends := head first (by simp [hs])
    unfold receiptAudit
    rw [all,chain]
    simp [hs,ends]

def edges (rs : List Receipt) : List (State × State) :=
  rs.reverse.map fun r => (r.before,r.after)
def receiptProduct (weight : Receipt → Rat) : List Receipt → Rat
  | [] => 1
  | r::rest => weight r * receiptProduct weight rest

theorem part_symmetric (f : Flavor) (c : Channel) (s t : State) : part f c s t=part f c t s := by
  cases c
  · exact content_channel_symmetric _ s t
  · exact clock_channel_symmetric s t

theorem receipt_product_append (weight : Receipt → Rat) (a b : List Receipt) :
    receiptProduct weight (a++b)=receiptProduct weight a * receiptProduct weight b := by
  induction a with
  | nil => simp [receiptProduct]
  | cons r rest ih => simp [receiptProduct,ih,Rat.mul_assoc]

theorem receipt_product_reverse (weight : Receipt → Rat) (rs : List Receipt) :
    receiptProduct weight rs.reverse=receiptProduct weight rs := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    simp [List.reverse_cons,receiptProduct,receipt_product_append,ih,Rat.mul_comm]

theorem audited_marked_path_symmetry (f : Flavor) (x : Execution)
    (valid : x.receipts.all (receiptOK f x)=true) :
    receiptProduct Receipt.weight x.receipts.reverse=
      receiptProduct (fun r => part f r.channel r.after r.before) x.receipts := by
  rw [receipt_product_reverse]
  have weights : ∀ r ∈ x.receipts, r.weight=part f r.channel r.after r.before := by
    intro r member
    have ok := List.all_eq_true.mp valid r member
    have parsed := of_decide_eq_true ok
    rw [parsed.2.2.2.2.1,part_symmetric]
  have helper : ∀ rs : List Receipt,
      (∀ r ∈ rs, r.weight=part f r.channel r.after r.before) →
      receiptProduct Receipt.weight rs=receiptProduct (fun r => part f r.channel r.after r.before) rs := by
    intro rs
    induction rs with
    | nil => intro _; rfl
    | cons r rest ih =>
      intro law
      simp only [receiptProduct]
      rw [law r (by simp),ih (fun s hs => law s (by simp [hs]))]
  exact helper x.receipts weights

noncomputable def pathCredit (f : Flavor) (r x : Execution) : Option Credit := by
  classical
  exact if LawGate f r ∧ Closure renewable r x ∧ receiptAudit f x=true then
    internalizedCredit (parameter f) (edges x.receipts) else none

theorem actual_path_credit_neutral (f : Flavor) (r x : Execution) (gate : LawGate f r)
    (reach : Closure renewable r x) (nonempty : x.receipts≠[]) : pathCredit f r x=some .neutral := by
  simp [pathCredit,gate,reach,actual_receipt_audit f r x gate reach nonempty,
    internalized_credit_neutral_all_paths]

theorem failed_gate_credit_rejected (f : Flavor) (r x : Execution) (bad : ¬ LawGate f r) :
    pathCredit f r x=none := by simp [pathCredit,bad]

theorem missing_receipts_credit_rejected (f : Flavor) (r x : Execution) (missing : x.receipts=[]) :
    pathCredit f r x=none := by simp [pathCredit,receiptAudit,missing]

theorem malformed_receipts_credit_rejected (f : Flavor) (r x : Execution)
    (bad : receiptAudit f x=false) : pathCredit f r x=none := by simp [pathCredit,bad]

theorem actual_all_path_symmetry (f : Flavor) (r x : Execution) (gate : LawGate f r)
    (reach : Closure renewable r x) :
    x.receipts.all (receiptOK f x)=true ∧
    receiptProduct Receipt.weight x.receipts.reverse=
      receiptProduct (fun r => part f r.channel r.after r.before) x.receipts ∧
    edgeProduct clockChannel (edges x.receipts)=
      edgeProduct clockChannel (reversedEdges (edges x.receipts)) ∧
    edgeProduct (contentChannel (parameter f)) (edges x.receipts)=
      edgeProduct (contentChannel (parameter f)) (reversedEdges (edges x.receipts)) ∧
    edgeProduct (liftP (parameter f)) (edges x.receipts)=
      edgeProduct (liftP (parameter f)) (reversedEdges (edges x.receipts)) := by
  have valid := (closure_receipt_integrity f r x gate reach).1
  have symmetric := internalized_all_path_products (parameter f) (edges x.receipts)
  exact ⟨valid,audited_marked_path_symmetry f x valid,symmetric.1,symmetric.2.1,symmetric.2.2⟩

inductive Command where
  | content
  | clock (phase : Tri)
  deriving DecidableEq, Repr
def commandMatches : Command → Channel → State → Bool
  | .content,c,_ => decide (c=.content)
  | .clock phase,c,t => decide (c=.clock ∧ t.2=phase)
def protocolRows (supply : Supply) (x : Execution) (cmd : Command) : List (Execution × Rat) :=
  (rawRows supply x).filter fun e =>
    e.1.receipts.head?.any (fun r => commandMatches cmd r.channel e.1.current)
def physicalProtocolRows (f : Flavor) (s : State) (cmd : Command) : List (State × Rat) :=
  ((physicalRows f s).filter fun e => commandMatches cmd e.1.1 e.1.2).map fun e => (e.1.2,e.2)
def protocolMass : Supply → Execution → List Command → State → Rat
  | _,x,[],t => if x.current=t then 1 else 0
  | supply,x,cmd::rest,t => (protocolRows supply x cmd).foldr
      (fun e acc => e.2*protocolMass supply e.1 rest t+acc) 0
def physicalProtocolMass : Flavor → State → List Command → State → Rat
  | _,s,[],t => if s=t then 1 else 0
  | f,s,cmd::rest,t => (physicalProtocolRows f s cmd).foldr
      (fun e acc => e.2*physicalProtocolMass f e.1 rest t+acc) 0
def protocolAB : List Command := [.content,.clock .b,.content,.clock .a]
def protocolBA : List Command := [.clock .b,.content,.clock .a,.content]

/- Protocol rows select supported labelled subevents without renormalization.
Both orders return the clock phase to a; content (a→c) distinguishes their
transport. This is protocol holonomy, not a directed cycle of the lift. -/
noncomputable def holonomyReadout (f : Flavor) (r : Execution) : Option Rat := by
  classical
  exact if LawGate f r then some (protocolMass renewable r protocolAB (.c,.a)-
    protocolMass renewable r protocolBA (.c,.a)) else none

theorem gated_protocol_projection (f : Flavor) (r x : Execution) (gate : LawGate f r)
    (reach : Closure renewable r x) (cmd : Command) :
    (protocolRows renewable x cmd).map (fun e => (e.1.current,e.2))=
      physicalProtocolRows f x.current cmd := by
  simp [protocolRows,gated_rows f r x gate reach,physicalProtocolRows,List.filter_map,
    List.map_map,advance,issue,Function.comp_def]

theorem actual_protocol_law (f : Flavor) (r x : Execution) (gate : LawGate f r)
    (reach : Closure renewable r x) (word : List Command) (t : State) :
    protocolMass renewable x word t=physicalProtocolMass f x.current word t := by
  induction word generalizing x with
  | nil => rfl
  | cons cmd rest ih =>
    simp only [protocolMass,physicalProtocolMass]
    rw [←gated_protocol_projection f r x gate reach cmd,List.foldr_map]
    have equal : ∀ rs : List (Execution × Rat),
        (∀ e ∈ rs, e∈protocolRows renewable x cmd) →
        rs.foldr (fun e acc => e.2*protocolMass renewable e.1 rest t+acc) 0=
        rs.foldr (fun e acc => e.2*physicalProtocolMass f e.1.current rest t+acc) 0 := by
      intro rs
      induction rs with
      | nil => intro _; rfl
      | cons e tail ht =>
        intro subset
        have raw : e∈rawRows renewable x := (List.mem_filter.mp (subset e (by simp))).1
        simp only [List.foldr_cons]
        rw [ih e.1 (Closure.step reach raw),ht (fun z hz => subset z (by simp [hz]))]
    exact equal _ (fun _ h => h)

theorem physical_protocol_holonomy (f : Flavor) :
    physicalProtocolMass f (.a,.a) protocolAB (.c,.a)=(parameter f)^2/144 ∧
    physicalProtocolMass f (.a,.a) protocolBA (.c,.a)=0 := by
  cases f <;> decide +kernel

theorem actual_protocol_holonomy (f : Flavor) (o : Owner) :
    protocolMass renewable (root f o) protocolAB (.c,.a)=(parameter f)^2/144 ∧
    protocolMass renewable (root f o) protocolBA (.c,.a)=0 := by
  rw [actual_protocol_law f _ _ (root_law_gate f o) .root,
    actual_protocol_law f _ _ (root_law_gate f o) .root]
  exact physical_protocol_holonomy f

theorem holonomy_readouts_exact (o : Owner) :
    holonomyReadout .source (root .source o)=some (1/324) ∧
    holonomyReadout .native (root .native o)=some (1/1024) := by
  have source := actual_protocol_holonomy .source o
  have native := actual_protocol_holonomy .native o
  simp [holonomyReadout,root_law_gate,source.1,source.2,native.1,native.2,parameter]
  decide +kernel

theorem failed_gate_holonomy_rejected (f : Flavor) (r : Execution) (bad : ¬ LawGate f r) :
    holonomyReadout f r=none := by simp [holonomyReadout,bad]

theorem holonomy_not_directional_credit (f : Flavor) (o : Owner) (x : Execution)
    (reach : Closure renewable (root f o) x) (nonempty : x.receipts≠[]) :
    pathCredit f (root f o) x=some .neutral ∧
    holonomyReadout f (root f o)=some ((parameter f)^2/144) := by
  refine ⟨actual_path_credit_neutral f _ x (root_law_gate f o) reach nonempty,?_⟩
  have h := actual_protocol_holonomy f o
  simp [holonomyReadout,root_law_gate,h.1,h.2,Rat.sub_eq_add_neg,
    (show -(0:Rat)=0 by decide +kernel),Rat.add_zero]

def select (supply : Supply) (x : Execution) (c : Channel) (target : State) : Option (Execution × Rat) :=
  (rawRows supply x).find? fun e =>
    e.1.receipts.head?.any (fun r => decide (r.channel=c ∧ e.1.current=target))
def runPlan : Supply → Execution → List (Channel × State) → Option Execution
  | _,x,[] => some x
  | supply,x,(c,t)::rest => (select supply x c t).bind fun e => runPlan supply e.1 rest
theorem run_plan_closure (supply : Supply) (r x y : Execution)
    (reach : Closure supply r x) (plan : List (Channel × State)) (success : runPlan supply x plan=some y) :
    Closure supply r y := by
  induction plan generalizing x with
  | nil =>
    have eq : x=y := Option.some.inj success
    exact eq ▸ reach
  | cons e rest ih =>
    cases hs : select supply x e.1 e.2 with
    | none => simp [runPlan,hs] at success
    | some z =>
      simp only [runPlan,hs,Option.bind_some] at success
      exact ih z.1 (Closure.step reach (List.mem_of_find?_eq_some hs)) success

def cyclePlan : List (Channel × State) :=
  [(.content,(.b,.a)),(.clock,(.b,.c)),(.content,(.a,.c)),(.clock,(.a,.a))]
def holonomyPlan : List (Channel × State) :=
  [(.content,(.b,.a)),(.clock,(.b,.b)),(.content,(.c,.b)),(.clock,(.c,.a))]
def cycleResult (f : Flavor) (o : Owner) : Option Execution := runPlan renewable (root f o) cyclePlan
def holonomyResult (f : Flavor) (o : Owner) : Option Execution := runPlan renewable (root f o) holonomyPlan

theorem plans_present (f : Flavor) (o : Owner) :
    (cycleResult f o).isSome=true ∧ (holonomyResult f o).isSome=true := by
  have cases : o=0 ∨ o=1 ∨ o=2 := by
    have bound:=o.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl | rfl | rfl <;> cases f <;> decide +kernel
def cycleEnd (f : Flavor) (o : Owner) : Execution := (cycleResult f o).get (plans_present f o).1
def holonomyEnd (f : Flavor) (o : Owner) : Execution := (holonomyResult f o).get (plans_present f o).2

theorem plan_histories_actual (f : Flavor) (o : Owner) :
    Closure renewable (root f o) (cycleEnd f o) ∧ Closure renewable (root f o) (holonomyEnd f o) := by
  constructor
  · apply run_plan_closure renewable (root f o) _ _ .root cyclePlan
    exact Option.eq_some_iff_get_eq.mpr ⟨(plans_present f o).1,rfl⟩
  · apply run_plan_closure renewable (root f o) _ _ .root holonomyPlan
    exact Option.eq_some_iff_get_eq.mpr ⟨(plans_present f o).2,rfl⟩

theorem plan_readouts (f : Flavor) (o : Owner) :
    (cycleEnd f o).current=(.a,.a) ∧ (holonomyEnd f o).current=(.c,.a) ∧
    (cycleEnd f o).receipts.length=4 ∧ (holonomyEnd f o).receipts.length=4 ∧
    (cycleEnd f o).accounts.portCursor (root f o).token=2 ∧
    (cycleEnd f o).accounts.portCursor 3=2 ∧
    receiptAudit f (cycleEnd f o)=true ∧ receiptAudit f (holonomyEnd f o)=true ∧
    edges (cycleEnd f o).receipts=liftedCycle := by
  have cases : o=0 ∨ o=1 ∨ o=2 := by
    have bound:=o.isLt
    simp only [Fin.ext_iff]
    omega
  rcases cases with rfl | rfl | rfl <;> cases f <;> decide +kernel

theorem actual_cycle_neutral_and_holonomy (f : Flavor) (o : Owner) :
    pathCredit f (root f o) (cycleEnd f o)=some .neutral ∧
    pathCredit f (root f o) (holonomyEnd f o)=some .neutral ∧
    holonomyReadout f (root f o)=some ((parameter f)^2/144) := by
  have cycleNonempty : (cycleEnd f o).receipts≠[] := by
    intro eq
    have count := (plan_readouts f o).2.2.1
    simp [eq] at count
  have protocolNonempty : (holonomyEnd f o).receipts≠[] := by
    intro eq
    have count := (plan_readouts f o).2.2.2.1
    simp [eq] at count
  exact ⟨actual_path_credit_neutral f _ _ (root_law_gate f o) (plan_histories_actual f o).1 cycleNonempty,
    (holonomy_not_directional_credit f o _ (plan_histories_actual f o).2 protocolNonempty)⟩

def closed (rs : List Receipt) : Bool := !rs.isEmpty &&
  decide (rs.head?.map Receipt.after=rs.getLast?.map Receipt.before)
noncomputable def cycleCredit (f : Flavor) (r x : Execution) : Option Credit :=
  if closed x.receipts then pathCredit f r x else none

theorem actual_closed_cycle_credit (f : Flavor) (o : Owner) :
    cycleCredit f (root f o) (cycleEnd f o)=some .neutral := by
  have closure : closed (cycleEnd f o).receipts=true := by
    have cases : o=0 ∨ o=1 ∨ o=2 := by
      have bound:=o.isLt
      simp only [Fin.ext_iff]
      omega
    rcases cases with rfl | rfl | rfl <;> cases f <;> decide +kernel
  simp [cycleCredit,closure,(actual_cycle_neutral_and_holonomy f o).1]

def reverseSchedule (p : Rat) (s t : Tri) : Rat :=
  (triStates.map fun mid => phaseKernel p .b s mid * phaseKernel p .a mid t).sum
theorem original_protocol_holonomy (f : Flavor) :
    scheduledP (parameter f) .a .c=(parameter f)^2 ∧
    reverseSchedule (parameter f) .a .c=0 := by cases f <;> decide +kernel

theorem comparison_with_g23 (f : Flavor) (o : Owner) :
    cycleCredit f (root f o) (cycleEnd f o)=some .neutral ∧
    CSTTT.FullNative.Credit.localCredit CSTTT.FullNative.Credit.sourceCycleWorld 0=some .self ∧
    CSTTT.FullNative.Credit.product CSTTT.FullNative.Credit.cycle≠
      CSTTT.FullNative.Credit.product CSTTT.FullNative.Credit.reversed :=
  ⟨actual_closed_cycle_credit f o,CSTTT.FullNative.Credit.source_actual_credit,
    CSTTT.FullNative.Credit.directionality.2.2⟩

def firstLogged : Execution := advance renewable (root .source 0) .content (.b,.a) (1/3)
def returnedLogged : Execution := advance renewable firstLogged .content (.a,.a) (1/3)

/-- Equal reverse weights do not roll back growing audit registers. The two
supported content moves return the physical state, but append two receipts and
consume two own packets. Literal reversibility of full logged executions is
false; this does not weaken the frozen all-path probability-product statement. -/
theorem logged_reverse_countertrace :
    (firstLogged,1/3)∈rawRows renewable (root .source 0) ∧
    (returnedLogged,1/3)∈rawRows renewable firstLogged ∧
    returnedLogged.current=(root .source 0).current ∧
    returnedLogged.accounts.portCursor 0=2 ∧ returnedLogged.receipts.length=2 ∧
    returnedLogged≠root .source 0 := by
  have first : (firstLogged,1/3)∈rawRows renewable (root .source 0) := by
    rw [funded_rows .source _ (roots_funded .source 0)]
    exact List.mem_map.mpr ⟨((.content,(.b,.a)),1/3),by decide +kernel,rfl⟩
  have funded : Funded .source firstLogged := funded_successor .source _ _ (roots_funded .source 0) _ first
  have second : (returnedLogged,1/3)∈rawRows renewable firstLogged := by
    rw [funded_rows .source _ funded]
    exact List.mem_map.mpr ⟨((.content,(.a,.a)),1/3),by decide +kernel,rfl⟩
  refine ⟨first,second,rfl,rfl,rfl,?_⟩
  intro eq
  have count := congrArg (fun x : Execution => x.receipts.length) eq
  change 2=0 at count
  contradiction

end CSTTT.FullNative.Internalized
