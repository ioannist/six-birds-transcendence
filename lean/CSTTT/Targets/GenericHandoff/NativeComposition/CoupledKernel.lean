import CSTTT.Targets.GenericHandoff.NativeComposition.FutureMass

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype
open RegisterInterpreter FixedPointVerifier
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
abbrev Kernel := Bool × Bool
def kernelStates : List Kernel := [(false,false),(false,true),(true,false),(true,true)]
def embed (s : Kernel) : Factor := (false,s)
def outside (s : Kernel) : Factor := (true,s)
def code (s : Kernel) : Nat := 2*bit s.1+bit s.2
-- These are native transition weights, frozen before any evaluation.
def diagonalWeight (s : Kernel) : Nat :=
  if s.1 then (if s.2 then 2 else 3) else (if s.2 then 3 else 1)
def rows (s : Factor) (action : Bool) : List (Factor × Nat) :=
  if s.1 then [(s,8)] else if action then [(outside s.2,8)] else
    [(embed (false,false),diagonalWeight s.2),
     (embed (false,true),4-diagonalWeight s.2),
     (embed (true,false),4-diagonalWeight s.2),
     (embed (true,true),diagonalWeight s.2)]
def input (owner : Owner) : Input :=
  {canonicalInput owner with temporal := {factorData owner with
    rows := rows,positions := fun _ => 0,hazards := Prod.fst,policy := fun _ => false,
    histories := fun s => [s,((rows s false).head!).1]}}
theorem selected_rows (owner : Owner) (s : Factor) (action : Bool) :
    (input owner).temporal.rows s action=rows s action := rfl

-- References to a concrete state are enumeration/certificate data, not M.
def exitBlock (o : Factor) : Nat := 4+code o.2
def destination (o : Factor) : Option Kernel := if o.1 then none else some o.2
def profile (i : Input) : ProfileRules.Raw Kernel Bool Factor :=
  ⟨kernelStates,[false,true],(fun s => i.temporal.rows (embed s)),
    (fun s => i.temporal.positions (embed s)),i.temporal.hazards,destination,exitBlock,
    false,[0,1,2,3,4,5,6,7],((false,false),(false,true)),(1,4,4),1⟩

theorem kernel_mem (s : Kernel) : s∈kernelStates := by
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> decide +kernel

theorem rows_positive_normalized (s : Factor) (action : Bool) :
    (∀ e∈rows s action, e.2>0 ∧ e.1∈factors) ∧
    ((rows s action).map Prod.snd).sum=8 := by
  rcases s with ⟨p,u,v⟩
  cases p <;> cases u <;> cases v <;> cases action <;> decide +kernel

theorem first_equation (owner : Owner) : ProfileRules.first (profile (input owner))=code := by
  funext s
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> decide +kernel +revert

theorem step_equation (owner : Owner) : ProfileRules.step (profile (input owner)) code=code := by
  funext s
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> decide +kernel +revert

theorem second_equation (owner : Owner) : ProfileRules.second (profile (input owner))=code := by
  change ProfileRules.step (profile (input owner)) (ProfileRules.first (profile (input owner)))=code
  rw [first_equation,step_equation]

theorem profile_trajectory (owner : Owner) :
    ProfileRules.count (profile (input owner)) (ProfileRules.seed (profile (input owner)))=1 ∧
    ProfileRules.count (profile (input owner)) (ProfileRules.first (profile (input owner)))=4 ∧
    ProfileRules.count (profile (input owner)) (ProfileRules.second (profile (input owner)))=4 := by
  rw [first_equation,second_equation]
  decide +kernel +revert

theorem profile_stable_forever (owner : Owner) (n : Nat) :
    ProfileRules.iterate (profile (input owner)) (1+n)=code := by
  induction n with
  | zero => exact first_equation owner
  | succ n ih =>
    change ProfileRules.step (profile (input owner)) (ProfileRules.iterate (profile (input owner)) (1+n))=code
    rw [ih,step_equation]

theorem code_exact (s t : Kernel) : code s=code t ↔ s=t := by
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> decide +kernel

-- Exact unnormalized masses. The common denominator is 8^word.length.
-- Both full future laws consume the actual selected native rows.
def exitMass (i : Input) : Factor → List Bool → Kernel → Nat
  | state,[],exit => if state.1 && decide (state.2=exit) then 1 else 0
  | state,action::rest,exit =>
    (i.temporal.rows state action).foldr
      (fun edge acc => edge.2*exitMass i edge.1 rest exit+acc) 0

theorem probe_exit_mass (owner : Owner) (s t : Kernel) :
    exitMass (input owner) (embed s) [true] t=if s=t then 8 else 0 := by
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> decide +kernel +revert

theorem full_exit_future_exact (owner : Owner) (s t : Kernel) :
    (∀ word exit,exitMass (input owner) (embed s) word exit=
      exitMass (input owner) (embed t) word exit) ↔ s=t := by
  constructor
  · intro equal
    have witness := equal [true] s
    rw [probe_exit_mass,probe_exit_mass] at witness
    by_cases same : t=s
    · exact same.symm
    · simp [same] at witness
  · rintro rfl word exit; rfl

theorem stable_partition_full_exit_future (owner : Owner) (s t : Kernel) :
    ProfileRules.second (profile (input owner)) s=ProfileRules.second (profile (input owner)) t ↔
      ∀ word exit,exitMass (input owner) (embed s) word exit=
        exitMass (input owner) (embed t) word exit := by
  rw [second_equation,code_exact,full_exit_future_exact]

-- Explicitly show why the old one-step hazard gate cannot certify this target.
theorem old_prediction_constant (owner : Owner) (s t : Kernel) :
    ProfileRules.predictive (profile (input owner)) s=
      ProfileRules.predictive (profile (input owner)) t := by
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> rfl

theorem old_linked_terminal_rejected (owner : Owner) :
    ¬ ProfileRules.SamePartition (ProfileRules.predictive (profile (input owner))) code := by
  intro linked
  have wrong := (linked (false,false) (false,true)).mp
    (old_prediction_constant owner (false,false) (false,true))
  have different : code (false,false)≠code (false,true) := by decide +kernel
  exact different wrong

-- Individual and paired branch emissions arise from the SAME native outcome.
def branchObserve (right : Bool) (o : Factor) : Nat :=
  if o.1 then 0 else bit (if right then o.2.2 else o.2.1)
def jointObserve (o : Factor) : Nat :=
  if o.1 then 4 else code o.2

def outputMass (i : Input) (observe : Factor → Nat) : Factor → List Bool → List Nat → Nat
  | _,[],[] => 1
  | _,[],_::_ => 0
  | _,_::_,[] => 0
  | state,action::rest,obs::observations =>
    (i.temporal.rows state action).foldr (fun edge acc =>
      (if observe edge.1=obs then edge.2*outputMass i observe edge.1 rest observations else 0)+acc) 0

theorem outside_branch_future_equal (owner : Owner) (right : Bool) (s t : Kernel)
    (word : List Bool) (observations : List Nat) :
    outputMass (input owner) (branchObserve right) (outside s) word observations=
      outputMass (input owner) (branchObserve right) (outside t) word observations := by
  induction word generalizing observations with
  | nil => cases observations <;> rfl
  | cons action rest ih =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      change (if 0=obs then 8*outputMass (input owner) (branchObserve right) (outside s) rest tail else 0)=
        (if 0=obs then 8*outputMass (input owner) (branchObserve right) (outside t) rest tail else 0)
      rw [ih tail]

theorem branch_all_future_equal (owner : Owner) (right : Bool) (s t : Kernel)
    (word : List Bool) (observations : List Nat) :
    outputMass (input owner) (branchObserve right) (embed s) word observations=
      outputMass (input owner) (branchObserve right) (embed t) word observations := by
  induction word generalizing s t observations with
  | nil => cases observations <;> rfl
  | cons action rest ih =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      cases action with
      | true =>
        change (if 0=obs then 8*outputMass (input owner) (branchObserve right) (outside s) rest tail else 0)=
          (if 0=obs then 8*outputMass (input owner) (branchObserve right) (outside t) rest tail else 0)
        rw [outside_branch_future_equal owner right s t rest tail]
      | false =>
        have constants (a : Kernel) :
            outputMass (input owner) (branchObserve right) (embed a) rest tail=
            outputMass (input owner) (branchObserve right) (embed (false,false)) rest tail :=
          ih a (false,false) tail
        simp only [outputMass,selected_rows]
        change ([(embed (false,false),diagonalWeight s),
          (embed (false,true),4-diagonalWeight s),
          (embed (true,false),4-diagonalWeight s),
          (embed (true,true),diagonalWeight s)].foldr _ 0)=
          ([(embed (false,false),diagonalWeight t),
          (embed (false,true),4-diagonalWeight t),
          (embed (true,false),4-diagonalWeight t),
          (embed (true,true),diagonalWeight t)].foldr _ 0)
        simp only [List.foldr_cons,List.foldr_nil,constants]
        rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
        cases u <;> cases v <;> cases a <;> cases b <;> cases right
        all_goals simp only [diagonalWeight,branchObserve,embed,bit,ite_true,ite_false,Bool.false_eq_true]
        all_goals by_cases h0 : 0=obs
        all_goals by_cases h1 : 1=obs
        all_goals first
          | (subst obs; simp <;> omega)
          | (simp only [h0,h1,ite_false] <;> omega)

theorem actual_joint_strict :
    outputMass (input false) jointObserve (embed (false,false)) [false] [0]=1 ∧
    outputMass (input false) jointObserve (embed (false,true)) [false] [0]=3 := by
  decide +kernel

def branchwiseEquivalent (i : Input) (s t : Kernel) : Prop :=
  ∀ right word observations,
    outputMass i (branchObserve right) (embed s) word observations=
      outputMass i (branchObserve right) (embed t) word observations
def jointEquivalent (i : Input) (s t : Kernel) : Prop :=
  ∀ word observations,outputMass i jointObserve (embed s) word observations=
    outputMass i jointObserve (embed t) word observations

theorem binding_split (owner : Owner) :
    branchwiseEquivalent (input owner) (false,false) (false,true) ∧
    ¬jointEquivalent (input owner) (false,false) (false,true) := by
  refine ⟨fun right word observations => branch_all_future_equal owner right _ _ word observations,?_⟩
  intro equal
  have bad := equal [false] [0]
  have different : outputMass (input owner) jointObserve (embed (false,false)) [false] [0]≠
      outputMass (input owner) jointObserve (embed (false,true)) [false] [0] := by
    cases owner <;> decide +kernel
  exact different bad

-- Current observations and connectors use the same rows as the future laws.
def current (i : Input) (s : Kernel) : List Nat :=
  let base := [i.temporal.positions (embed s),
   bit (!(i.temporal.rows (embed s) false).isEmpty),
   bit (!(i.temporal.rows (embed s) true).isEmpty)]
  if i.reveal then base++[ProfileRules.second (profile i) s] else base

theorem current_input_equation (owner : Owner) (s : Kernel) :
    current (input owner) s=[0,1,1] := by
  unfold current
  rw [show (input owner).reveal=false from rfl]
  simp only [Bool.false_eq_true,ite_false]
  change [0,bit (!(rows (embed s) false).isEmpty),bit (!(rows (embed s) true).isEmpty)]=[0,1,1]
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> decide +kernel

theorem actual_current_constant (owner : Owner) (s t : Kernel) :
    current (input owner) s=current (input owner) t := by
  rw [current_input_equation,current_input_equation]

theorem all_joint_decoders_constant (owner : Owner) {Y : Type}
    (decode : List Nat → Y) (s t : Kernel) :
    decode (current (input owner) s)=decode (current (input owner) t) := by
  rw [actual_current_constant owner s t]

theorem actual_maintenance_connector (owner : Owner) (s t : Kernel) :
    ∃ weight, (embed t,weight)∈(input owner).temporal.rows (embed s) false ∧ weight>0 := by
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b
  all_goals first
    | (exact ⟨1,by decide +kernel +revert,by decide +kernel⟩)
    | (exact ⟨2,by decide +kernel +revert,by decide +kernel⟩)
    | (exact ⟨3,by decide +kernel +revert,by decide +kernel⟩)

-- Multiscale C1 closure derives C/U from the computed full-exit partition.
-- The legacy ObjecthoodRules.classOf uses only the inadequate hazard list.
def P (i : Input) (s t : Kernel) : Rat :=
  ((i.temporal.rows (embed s) false).map fun edge =>
    if destination edge.1=some t then (edge.2:Rat) else 0).sum / 8
def classes (i : Input) := ProfileRules.second (profile i)
def fiber (i : Input) (s : Kernel) : List Kernel :=
  kernelStates.filter fun t => decide (classes i t=classes i s)
def C (i : Input) (s k : Kernel) : Rat := if classes i s=classes i k then 1 else 0
def U (i : Input) (k s : Kernel) : Rat :=
  if classes i s=classes i k then 1/(fiber i k).length else 0
def CU (i : Input) (s t : Kernel) : Rat :=
  (kernelStates.map fun k => C i s k*U i k t).sum

theorem computed_CU_identity (owner : Owner) : CU (input owner)=identity := by
  funext s t
  simp only [CU,C,U,fiber,classes,second_equation]
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> decide +kernel

def epsilon (perturb : Bool) : Rat := if perturb then 1/16 else 0
def perturbed (i : Input) (perturb : Bool) (s t : Kernel) : Rat :=
  (1-epsilon perturb)*P i s t+epsilon perturb/4
def closure (i : Input) (perturb squared : Bool) : Matrix Kernel :=
  ObjecthoodRules.product kernelStates
    (ObjecthoodRules.power kernelStates (perturbed i perturb) (if squared then 2 else 1)) (CU i)

def operationsZero : List (RowOperation Kernel) := [
  .add (false,true) (false,false) ((-3:Rat)/8),
  .add (true,false) (false,false) ((-3:Rat)/8),
  .add (true,true) (false,false) ((-1:Rat)/8),
  .scale (false,true) ((-4:Rat)/5),
  .add (false,false) (false,true) (-1:Rat),
  .add (true,false) (false,true) ((1:Rat)/4),
  .add (true,true) (false,true) ((-1:Rat)/4),
  .scale (true,false) ((-5:Rat)/6),
  .add (false,false) (true,false) ((-4:Rat)/5),
  .add (false,true) (true,false) ((-1:Rat)/5),
  .add (true,true) (true,false) ((-1:Rat)/5),
  .scale (true,true) ((-12:Rat)/11),
  .add (false,false) (true,true) ((-5:Rat)/6),
  .add (false,true) (true,true) ((-1:Rat)/12),
  .add (true,false) (true,true) ((-1:Rat)/12)]

def operationsZeroSquared : List (RowOperation Kernel) := [
  .add (false,true) (false,false) ((-11:Rat)/64),
  .add (true,false) (false,false) ((-11:Rat)/64),
  .add (true,true) (false,false) ((-21:Rat)/64),
  .scale (false,true) ((-32:Rat)/29),
  .add (false,false) (false,true) (-1:Rat),
  .add (true,false) (false,true) ((-3:Rat)/32),
  .add (true,true) (false,true) ((3:Rat)/32),
  .scale (true,false) ((-29:Rat)/26),
  .add (false,false) (true,false) ((-32:Rat)/29),
  .add (false,true) (true,false) ((3:Rat)/29),
  .add (true,true) (true,false) ((3:Rat)/29),
  .scale (true,true) ((-52:Rat)/55),
  .add (false,false) (true,true) ((-29:Rat)/26),
  .add (false,true) (true,true) ((3:Rat)/52),
  .add (true,false) (true,true) ((3:Rat)/52)]

def operationsPerturbed : List (RowOperation Kernel) := [
  .add (false,true) (false,false) ((-47:Rat)/128),
  .add (true,false) (false,false) ((-47:Rat)/128),
  .add (true,true) (false,false) ((-17:Rat)/128),
  .scale (false,true) ((-64:Rat)/79),
  .add (false,false) (false,true) (-1:Rat),
  .add (true,false) (false,true) ((15:Rat)/64),
  .add (true,true) (false,true) ((-15:Rat)/64),
  .scale (true,false) ((-79:Rat)/94),
  .add (false,false) (true,false) ((-64:Rat)/79),
  .add (false,true) (true,false) ((-15:Rat)/79),
  .add (true,true) (true,false) ((-15:Rat)/79),
  .scale (true,true) ((-188:Rat)/173),
  .add (false,false) (true,true) ((-79:Rat)/94),
  .add (false,true) (true,true) ((-15:Rat)/188),
  .add (true,false) (true,true) ((-15:Rat)/188)]

def operationsPerturbedSquared : List (RowOperation Kernel) := [
  .add (false,true) (false,false) ((-2941:Rat)/16384),
  .add (true,false) (false,false) ((-2941:Rat)/16384),
  .add (true,true) (false,false) ((-5251:Rat)/16384),
  .scale (false,true) ((-8192:Rat)/7517),
  .add (false,false) (false,true) (-1:Rat),
  .add (true,false) (false,true) ((-675:Rat)/8192),
  .add (true,true) (false,true) ((675:Rat)/8192),
  .scale (true,false) ((-7517:Rat)/6842),
  .add (false,false) (true,false) ((-8192:Rat)/7517),
  .add (false,true) (true,false) ((675:Rat)/7517),
  .add (true,true) (true,false) ((675:Rat)/7517),
  .scale (true,true) ((-13684:Rat)/14359),
  .add (false,false) (true,true) ((-7517:Rat)/6842),
  .add (false,true) (true,true) ((675:Rat)/13684),
  .add (true,false) (true,true) ((675:Rat)/13684)]

def operations (perturb squared : Bool) : List (RowOperation Kernel) :=
  if perturb then (if squared then operationsPerturbedSquared else operationsPerturbed)
  else (if squared then operationsZeroSquared else operationsZero)
def candidate (i : Input) (perturb squared : Bool) : Vector Kernel :=
  FixedPointVerifier.candidate (closure i perturb squared) (false,false) (operations perturb squared)
def expected (perturb : Bool) (s : Kernel) : Rat :=
  if s.1=s.2 then (if perturb then 47/173 else 3/11)
  else (if perturb then 79/346 else 5/22)

-- Closed verification matrices are abbreviations of the SAME native P.
def verifiedMatrix (perturb squared : Bool) : Matrix Kernel :=
  ObjecthoodRules.power kernelStates (perturbed (input false) perturb) (if squared then 2 else 1)

theorem closure_equation (owner : Owner) (perturb squared : Bool) :
    closure (input owner) perturb squared=verifiedMatrix perturb squared := by
  unfold closure
  rw [computed_CU_identity]
  funext s t
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> cases perturb <;> cases squared
  all_goals decide +kernel +revert

theorem all_four_verifiers_pass (owner : Owner) (perturb squared : Bool) :
    check kernelStates (closure (input owner) perturb squared) (false,false)
      (operations perturb squared)=true := by
  rw [closure_equation]
  cases perturb <;> cases squared <;> decide +kernel

theorem candidate_equation (owner : Owner) (perturb squared : Bool) :
    candidate (input owner) perturb squared=expected perturb := by
  unfold candidate
  rw [closure_equation]
  funext s
  rcases s with ⟨u,v⟩
  cases u <;> cases v <;> cases perturb <;> cases squared <;> decide +kernel

theorem all_four_probability_fixed_unique (owner : Owner) (perturb squared : Bool) :
    Probability kernelStates (candidate (input owner) perturb squared) ∧
    Fixed kernelStates (closure (input owner) perturb squared)
      (candidate (input owner) perturb squared) ∧
    (∀ x,Probability kernelStates x → Fixed kernelStates (closure (input owner) perturb squared) x →
      x=candidate (input owner) perturb squared) :=
  check_sound kernelStates kernel_mem _ _ _ (all_four_verifiers_pass owner perturb squared)

theorem all_four_nonuniform (owner : Owner) (perturb squared : Bool) :
    candidate (input owner) perturb squared≠(fun _ => (1:Rat)/4) := by
  rw [candidate_equation]
  intro equal
  have wrong := congrFun equal (false,false)
  cases perturb with
  | false => exact (by decide +kernel : expected false (false,false)≠(1:Rat)/4) wrong
  | true => exact (by decide +kernel : expected true (false,false)≠(1:Rat)/4) wrong

-- A genuine cycle product is computed from native transition probabilities.
def forward (i : Input) : Rat :=
  P i (false,false) (false,true)*P i (false,true) (true,true)*P i (true,true) (false,false)
def reverse (i : Input) : Rat :=
  P i (false,true) (false,false)*P i (true,true) (false,true)*P i (false,false) (true,true)
theorem actual_cycle_directionality (owner : Owner) :
    forward (input owner)=9/256 ∧ reverse (input owner)=3/256 ∧
    forward (input owner)≠reverse (input owner) := by
  cases owner <;> decide +kernel


-- Funded greatest viability is recomputed from the same maintenance rows.
def viabilitySchema (owner : Owner) : OperationalViability.Schema Kernel Bool Factor Owner :=
  ⟨kernelStates,[false,true],destination,8,owner,⟨1,1,1⟩,
    (fun s t => ((rows (embed s) false).map fun edge =>
      if destination edge.1=some t then edge.2 else 0).sum)⟩
def viabilityData (i : Input) : OperationalViability.Raw Kernel Bool Factor Owner :=
  ⟨(fun s => i.temporal.rows (embed s)),(fun s => i.temporal.policy (embed s)),
    i.temporal.resource,i.temporal.ledger⟩
theorem viability_domain (owner : Owner) : OperationalViability.DomainCheck (viabilitySchema owner) := by
  refine ⟨by decide +kernel +revert,kernel_mem,by decide +kernel +revert,?_,by decide +kernel +revert,by decide +kernel +revert⟩
  intro action; cases action <;> decide +kernel +revert

theorem kernel_viable (owner : Owner) : ViableSet.Viable
    (OperationalViability.retain (viabilitySchema owner) (viabilityData (input owner))) kernelStates := by
  intro s member
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> decide +kernel +revert

theorem greatest_kernel_contains (owner : Owner) (s : Kernel) :
    s∈OperationalViability.greatest (viabilitySchema owner) (viabilityData (input owner)) :=
  OperationalViability.greatest_contains _ _ kernel_mem kernelStates (kernel_viable owner) (kernel_mem s)

theorem actual_viability (owner : Owner) : OperationalViability.Accept
    (viabilitySchema owner) (viabilityData (input owner)) := by
  refine ⟨viability_domain owner,?_,by decide +kernel +revert,?_,?_⟩
  · intro empty
    have member := greatest_kernel_contains owner (false,false)
    simp [empty] at member
  · simp [OperationalViability.LedgerCheck,OperationalViability.budgetAfter,
      viabilityData,input,canonicalInput,factorData,viabilitySchema]
  · intro s hs t ht
    rfl

def unfunded (i : Input) : Input :=
  {i with temporal := {i.temporal with resource := {i.temporal.resource with rechargeAvailable := false}}}
theorem unfunded_greatest_empty (owner : Owner) :
    OperationalViability.greatest (viabilitySchema owner) (viabilityData (unfunded (input owner)))=[] := by
  apply OperationalViability.unavailable_empty _ _ kernel_mem
  simp [OperationalViability.available,viabilityData,unfunded]

-- Flat ablation changes only the correlation in actual native maintenance rows.
def flatRows (s : Factor) (action : Bool) : List (Factor × Nat) :=
  if s.1 then [(s,8)] else if action then [(outside s.2,8)] else
    [(embed (false,false),2),(embed (false,true),2),(embed (true,false),2),(embed (true,true),2)]
def flatten (i : Input) : Input :=
  {i with temporal := {i.temporal with rows := flatRows}}

theorem flat_rows_positive_normalized (s : Factor) (action : Bool) :
    (∀ e∈flatRows s action,e.2>0 ∧ e.1∈factors) ∧
    ((flatRows s action).map Prod.snd).sum=8 := by
  rcases s with ⟨p,u,v⟩
  cases p <;> cases u <;> cases v <;> cases action <;> decide +kernel

theorem flat_outside_future_equal (i : Input) (observe : Factor → Nat)
    (constant : ∀ s t : Kernel,observe (outside s)=observe (outside t))
    (s t : Kernel) (word : List Bool) (observations : List Nat) :
    outputMass (flatten i) observe (outside s) word observations=
      outputMass (flatten i) observe (outside t) word observations := by
  induction word generalizing observations with
  | nil => cases observations <;> rfl
  | cons action rest ih =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      change (if observe (outside s)=obs then 8*outputMass (flatten i) observe (outside s) rest tail else 0)=
        (if observe (outside t)=obs then 8*outputMass (flatten i) observe (outside t) rest tail else 0)
      rw [constant s t,ih tail]

theorem flat_joint_all_future_equal (i : Input) (s t : Kernel)
    (word : List Bool) (observations : List Nat) :
    outputMass (flatten i) jointObserve (embed s) word observations=
      outputMass (flatten i) jointObserve (embed t) word observations := by
  cases word with
  | nil => cases observations <;> rfl
  | cons action rest =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      cases action with
      | false => rfl
      | true =>
        change (if 4=obs then 8*outputMass (flatten i) jointObserve (outside s) rest tail else 0)=
          (if 4=obs then 8*outputMass (flatten i) jointObserve (outside t) rest tail else 0)
        rw [flat_outside_future_equal i jointObserve (fun _ _ => rfl) s t rest tail]

theorem flat_joint_no_strict_pair (i : Input) :
    ¬∃ s t,branchwiseEquivalent (flatten i) s t ∧ ¬jointEquivalent (flatten i) s t := by
  rintro ⟨s,t,_,different⟩
  exact different (flat_joint_all_future_equal i s t)

theorem flat_cycle_collapses (i : Input) : forward (flatten i)=reverse (flatten i) := by
  simp [forward,reverse,P,flatten,flatRows,embed,destination] <;> decide +kernel

theorem outside_flat_mass_matches (owner : Owner) (observe : Factor → Nat) (s : Kernel)
    (word : List Bool) (observations : List Nat) :
    outputMass (flatten (input owner)) observe (outside s) word observations=
      outputMass (input owner) observe (outside s) word observations := by
  induction word generalizing observations with
  | nil => cases observations <;> rfl
  | cons action rest ih =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      change (if observe (outside s)=obs then
        8*outputMass (flatten (input owner)) observe (outside s) rest tail else 0)=
        (if observe (outside s)=obs then 8*outputMass (input owner) observe (outside s) rest tail else 0)
      rw [ih tail]

theorem flat_branch_preserves_all_future (owner : Owner) (right : Bool) (s : Kernel)
    (word : List Bool) (observations : List Nat) :
    outputMass (flatten (input owner)) (branchObserve right) (embed s) word observations=
      outputMass (input owner) (branchObserve right) (embed s) word observations := by
  induction word generalizing s observations with
  | nil => cases observations <;> rfl
  | cons action rest ih =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      cases action with
      | true =>
        change (if 0=obs then 8*outputMass (flatten (input owner)) (branchObserve right) (outside s) rest tail else 0)=
          (if 0=obs then 8*outputMass (input owner) (branchObserve right) (outside s) rest tail else 0)
        rw [outside_flat_mass_matches owner (branchObserve right) s rest tail]
      | false =>
        simp only [outputMass]
        change ([(embed (false,false),2),(embed (false,true),2),
          (embed (true,false),2),(embed (true,true),2)].foldr _ 0)=
          ([(embed (false,false),diagonalWeight s),
          (embed (false,true),4-diagonalWeight s),
          (embed (true,false),4-diagonalWeight s),
          (embed (true,true),diagonalWeight s)].foldr _ 0)
        simp only [List.foldr_cons,List.foldr_nil,ih]
        have constants (a : Kernel) :
            outputMass (input owner) (branchObserve right) (embed a) rest tail=
            outputMass (input owner) (branchObserve right) (embed (false,false)) rest tail :=
          branch_all_future_equal owner right a (false,false) rest tail
        simp only [constants]
        rcases s with ⟨u,v⟩
        cases u <;> cases v <;> cases right
        all_goals simp only [diagonalWeight,branchObserve,embed,bit,ite_true,ite_false,Bool.false_eq_true]
        all_goals by_cases h0 : 0=obs
        all_goals by_cases h1 : 1=obs
        all_goals first
          | (subst obs; simp <;> omega)
          | (simp only [h0,h1,ite_false] <;> omega)

def expose (i : Input) : Input := {i with reveal := true}
theorem exposed_current_nonconstant (owner : Owner) :
    current (expose (input owner)) (false,false)≠current (expose (input owner)) (false,true) := by
  cases owner <;> decide +kernel

-- These predicates are readouts of actual data. They are never primitive fields.
def CurrentPrivacy (i : Input) : Prop := ∀ s t : Kernel,current i s=current i t
noncomputable def privacyBit (i : Input) : Bool := by
  classical
  exact decide (CurrentPrivacy i)
noncomputable def bindingBit (i : Input) : Bool := by
  classical
  exact decide (∃ s t,branchwiseEquivalent i s t ∧ ¬jointEquivalent i s t)
noncomputable def directionBit (i : Input) : Bool := by
  classical
  exact decide (forward i≠reverse i)

theorem actual_privacy_bit (owner : Owner) : privacyBit (input owner)=true := by
  classical
  exact decide_eq_true (actual_current_constant owner)
theorem actual_binding_bit (owner : Owner) : bindingBit (input owner)=true := by
  classical
  exact decide_eq_true (show ∃ s t,branchwiseEquivalent (input owner) s t ∧
    ¬jointEquivalent (input owner) s t from ⟨_,_,binding_split owner⟩)
theorem flat_actual_binding_bit (i : Input) : bindingBit (flatten i)=false := by
  classical
  exact decide_eq_false (flat_joint_no_strict_pair i)
theorem actual_direction_bit (owner : Owner) : directionBit (input owner)=true := by
  classical
  exact decide_eq_true (actual_cycle_directionality owner).2.2
theorem flat_actual_direction_bit (i : Input) : directionBit (flatten i)=false := by
  classical
  exact decide_eq_false (not_not_intro (flat_cycle_collapses i))

theorem exposed_actual_privacy_bit (owner : Owner) : privacyBit (expose (input owner))=false := by
  classical
  apply decide_eq_false
  intro constant
  exact exposed_current_nonconstant owner (constant (false,false) (false,true))

def selected (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) : Option Input :=
  (a cell).map (MemoryFrames.selectInput copy)
noncomputable def readout (bitReadout : Input → Bool) (cell : Owner) (copy : Bool)
    (a : Assignment Owner MemoryValue) : Option Bool := (selected cell copy a).map bitReadout

theorem readout_some_exact (bitReadout : Input → Bool) (cell : Owner) (copy : Bool)
    (a : Assignment Owner MemoryValue) (value : Bool) :
    readout bitReadout cell copy a=some value ↔ ∃ pair,a cell=some pair ∧
      bitReadout (MemoryFrames.selectInput copy pair)=value := by
  cases h : a cell <;> simp [readout,selected,h]
theorem readout_none_exact (bitReadout : Input → Bool) (cell : Owner) (copy : Bool)
    (a : Assignment Owner MemoryValue) : readout bitReadout cell copy a=none ↔ a cell=none := by
  cases h : a cell <;> simp [readout,selected,h]

-- SAME-input return: full exit quotient, C4 current privacy, full-word C7,
-- multiscale C1 uniqueness, actual native directionality and funded viability.
-- This is not a claim that the remaining C5 lift/C6 clock/source package is done.
theorem same_native_row_return (owner : Owner) :
    (∀ s t,ProfileRules.second (profile (input owner)) s=ProfileRules.second (profile (input owner)) t ↔
      ∀ word exit,exitMass (input owner) (embed s) word exit=exitMass (input owner) (embed t) word exit) ∧
    CurrentPrivacy (input owner) ∧
    (∃ s t,branchwiseEquivalent (input owner) s t ∧ ¬jointEquivalent (input owner) s t) ∧
    (∀ perturb squared,Probability kernelStates (candidate (input owner) perturb squared) ∧
      Fixed kernelStates (closure (input owner) perturb squared) (candidate (input owner) perturb squared) ∧
      (∀ x,Probability kernelStates x → Fixed kernelStates (closure (input owner) perturb squared) x →
        x=candidate (input owner) perturb squared)) ∧
    forward (input owner)≠reverse (input owner) ∧
    OperationalViability.Accept (viabilitySchema owner) (viabilityData (input owner)) :=
  ⟨stable_partition_full_exit_future owner,actual_current_constant owner,⟨_,_,binding_split owner⟩,
    all_four_probability_fixed_unique owner,(actual_cycle_directionality owner).2.2,actual_viability owner⟩

-- Exact fixed-point perturbation and idempotence bookkeeping at both stagings.
def stationaryTV (i : Input) : Rat :=
  ((kernelStates.map fun s => ObjecthoodRules.absRat
    (candidate i true false s-candidate i false false s)).sum)/2

theorem perturbation_TV_exact (owner : Owner) : stationaryTV (input owner)=4/1903 := by
  unfold stationaryTV
  rw [candidate_equation,candidate_equation]
  decide +kernel

def idempotenceDefect (matrix : Matrix Kernel) : Rat :=
  (kernelStates.map fun s =>
    ((kernelStates.map fun t => ObjecthoodRules.absRat
      (ObjecthoodRules.product kernelStates matrix matrix s t-matrix s t)).sum)/2).foldl max 0

def expectedDefect (perturb squared : Bool) : Rat :=
  if perturb then (if squared then 11485125/134217728 else 3075/8192)
  else (if squared then 195/2048 else 13/32)

theorem all_four_idempotence_defects (owner : Owner) (perturb squared : Bool) :
    idempotenceDefect (closure (input owner) perturb squared)=expectedDefect perturb squared := by
  rw [closure_equation]
  cases perturb <;> cases squared <;> decide +kernel

theorem maintained_core_retention (owner : Owner) (perturb squared : Bool) :
    (kernelStates.map (candidate (input owner) perturb squared)).sum=1 :=
  (all_four_probability_fixed_unique owner perturb squared).1.2

-- Raw copied-source transport holds for EVERY partial assignment and bit readout.
theorem selected_copied_source (a : Assignment Owner MemoryValue) (owner : Owner) :
    selected (swapOwner owner) true (memoryImage a)=selected owner false a := by
  cases owner <;> simp only [selected,memoryImage,swapOwner,Option.map_map]
  all_goals rfl

theorem copied_source_readout_exact (bitReadout : Input → Bool)
    (a : Assignment Owner MemoryValue) (owner : Owner) :
    readout bitReadout (swapOwner owner) true (memoryImage a)=readout bitReadout owner false a := by
  simp only [readout,selected_copied_source]

def assignment : Assignment Owner MemoryValue := fun owner => some (input owner,input owner)
def flatAssignment : Assignment Owner MemoryValue :=
  fun owner => some (flatten (input owner),input owner)
def exposedAssignment : Assignment Owner MemoryValue :=
  fun owner => some (expose (input owner),input owner)

theorem concrete_positive_readouts (owner : Owner) :
    readout privacyBit owner false assignment=some true ∧
    readout bindingBit owner false assignment=some true ∧
    readout directionBit owner false assignment=some true := by
  simp only [readout,selected,assignment,Option.map_some,MemoryFrames.selectInput]
  exact ⟨congrArg some (actual_privacy_bit owner),congrArg some (actual_binding_bit owner),
    congrArg some (actual_direction_bit owner)⟩

theorem concrete_flat_readouts (owner : Owner) :
    readout bindingBit owner false flatAssignment=some false ∧
    readout directionBit owner false flatAssignment=some false ∧
    readout bindingBit owner true flatAssignment=some true := by
  simp only [readout,selected,flatAssignment,Option.map_some,MemoryFrames.selectInput,ite_true]
  exact ⟨congrArg some (flat_actual_binding_bit (input owner)),
    congrArg some (flat_actual_direction_bit (input owner)),congrArg some (actual_binding_bit owner)⟩

theorem concrete_exposed_readouts (owner : Owner) :
    readout privacyBit owner false exposedAssignment=some false ∧
    readout privacyBit owner true exposedAssignment=some true := by
  simp only [readout,selected,exposedAssignment,Option.map_some,MemoryFrames.selectInput,ite_true]
  exact ⟨congrArg some (exposed_actual_privacy_bit owner),congrArg some (actual_privacy_bit owner)⟩

-- Full histories of the declared current channels, not merely a static split.
def factorCurrent (i : Input) (state : Factor) : List Nat :=
  [i.temporal.positions state,
    bit (!(i.temporal.rows state false).isEmpty),bit (!(i.temporal.rows state true).isEmpty)]

theorem factor_current_constant (owner : Owner) (state : Factor) :
    factorCurrent (input owner) state=[0,1,1] := by
  rcases state with ⟨p,u,v⟩
  cases p <;> cases u <;> cases v <;> rfl

theorem output_mass_native_rule (i : Input) (observe : Factor → Nat)
    (state : Factor) (word : List Bool) (observations : List Nat) :
    outputMass i observe state word observations=
      NativeObservedFutureRulesPrototype.mass i.temporal.rows observe state word observations := by
  induction word generalizing state observations with
  | nil => cases observations <;> rfl
  | cons action rest ih =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      simp only [outputMass,NativeObservedFutureRulesPrototype.mass,ih]

theorem full_public_history_exact (owner : Owner) (decode : List Nat → Nat)
    (state : Factor) (word : List Bool) (observations : List Nat) :
    outputMass (input owner) (fun outcome => decode (factorCurrent (input owner) outcome))
      state word observations=
      if observations=List.replicate word.length (decode [0,1,1]) then 8^word.length else 0 := by
  rw [output_mass_native_rule]
  apply NativeObservedFutureRulesPrototype.constant_observation_exact
  · intro s a
    exact (rows_positive_normalized s a).2
  · intro outcome
    rw [factor_current_constant]

theorem full_public_history_all_initial (owner : Owner) (decode : List Nat → Nat)
    (s t : Factor) (word : List Bool) (observations : List Nat) :
    outputMass (input owner) (fun outcome => decode (factorCurrent (input owner) outcome)) s word observations=
      outputMass (input owner) (fun outcome => decode (factorCurrent (input owner) outcome)) t word observations := by
  rw [full_public_history_exact,full_public_history_exact]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype
open RegisterInterpreter FixedPointVerifier
set_option autoImplicit false

-- A joint observation which is literally the pair of the TWO branch emissions.
-- The earlier jointObserve also retained a dead-exit marker; this readout does not.
def pairedObserve (outcome : Factor) : Nat :=
  2*branchObserve false outcome+branchObserve true outcome

theorem paired_observe_inside (s : Kernel) : pairedObserve (embed s)=code s := by
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> rfl

theorem paired_observe_outside (s : Kernel) : pairedObserve (outside s)=0 := rfl

def pairedEquivalent (i : Input) (s t : Kernel) : Prop :=
  ∀ word observations,outputMass i pairedObserve (embed s) word observations=
    outputMass i pairedObserve (embed t) word observations

theorem actual_paired_strict (owner : Owner) :
    outputMass (input owner) pairedObserve (embed (false,false)) [false] [0]=1 ∧
    outputMass (input owner) pairedObserve (embed (false,true)) [false] [0]=3 := by
  cases owner <;> decide +kernel

theorem paired_binding_split (owner : Owner) :
    branchwiseEquivalent (input owner) (false,false) (false,true) ∧
    ¬pairedEquivalent (input owner) (false,false) (false,true) := by
  refine ⟨fun right word observations => branch_all_future_equal owner right _ _ word observations,?_⟩
  intro equal
  have bad := equal [false] [0]
  rw [(actual_paired_strict owner).1,(actual_paired_strict owner).2] at bad
  contradiction

theorem flat_paired_all_future_equal (i : Input) (s t : Kernel)
    (word : List Bool) (observations : List Nat) :
    outputMass (flatten i) pairedObserve (embed s) word observations=
      outputMass (flatten i) pairedObserve (embed t) word observations := by
  cases word with
  | nil => cases observations <;> rfl
  | cons action rest =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      cases action with
      | false => rfl
      | true =>
        change (if 0=obs then 8*outputMass (flatten i) pairedObserve (outside s) rest tail else 0)=
          (if 0=obs then 8*outputMass (flatten i) pairedObserve (outside t) rest tail else 0)
        rw [flat_outside_future_equal i pairedObserve (fun _ _ => rfl) s t rest tail]

theorem flat_paired_no_strict_pair (i : Input) :
    ¬∃ s t,branchwiseEquivalent (flatten i) s t ∧ ¬pairedEquivalent (flatten i) s t := by
  rintro ⟨s,t,_,different⟩
  exact different (flat_paired_all_future_equal i s t)

noncomputable def pairedBindingBit (i : Input) : Bool := by
  classical
  exact decide (∃ s t,branchwiseEquivalent i s t ∧ ¬pairedEquivalent i s t)

theorem actual_paired_binding_bit (owner : Owner) : pairedBindingBit (input owner)=true := by
  classical
  exact decide_eq_true (show ∃ s t,branchwiseEquivalent (input owner) s t ∧
    ¬pairedEquivalent (input owner) s t from ⟨_,_,paired_binding_split owner⟩)

theorem flat_actual_paired_binding_bit (i : Input) : pairedBindingBit (flatten i)=false := by
  classical
  exact decide_eq_false (flat_paired_no_strict_pair i)

theorem paired_readout_true_exact (cell : Owner) (copy : Bool)
    (a : Assignment Owner MemoryValue) :
    readout pairedBindingBit cell copy a=some true ↔
      ∃ pair,a cell=some pair ∧ ∃ s t,
        branchwiseEquivalent (MemoryFrames.selectInput copy pair) s t ∧
        ¬pairedEquivalent (MemoryFrames.selectInput copy pair) s t := by
  classical
  rw [readout_some_exact]
  simp only [pairedBindingBit,decide_eq_true_eq]

theorem paired_readout_false_exact (cell : Owner) (copy : Bool)
    (a : Assignment Owner MemoryValue) :
    readout pairedBindingBit cell copy a=some false ↔
      ∃ pair,a cell=some pair ∧ ¬∃ s t,
        branchwiseEquivalent (MemoryFrames.selectInput copy pair) s t ∧
        ¬pairedEquivalent (MemoryFrames.selectInput copy pair) s t := by
  classical
  rw [readout_some_exact]
  simp only [pairedBindingBit,decide_eq_false_iff_not]

theorem concrete_paired_readouts (owner : Owner) :
    readout pairedBindingBit owner false assignment=some true ∧
    readout pairedBindingBit owner false flatAssignment=some false ∧
    readout pairedBindingBit owner true flatAssignment=some true := by
  simp only [readout,selected,assignment,flatAssignment,Option.map_some,MemoryFrames.selectInput,ite_true]
  exact ⟨congrArg some (actual_paired_binding_bit owner),
    congrArg some (flat_actual_paired_binding_bit (input owner)),congrArg some (actual_paired_binding_bit owner)⟩

-- Explicit same-input stronger C7 return alongside the existing independent axes.
theorem same_native_paired_return (owner : Owner) :
    (∀ s t,ProfileRules.second (profile (input owner)) s=ProfileRules.second (profile (input owner)) t ↔
      ∀ word exit,exitMass (input owner) (embed s) word exit=exitMass (input owner) (embed t) word exit) ∧
    CurrentPrivacy (input owner) ∧
    (∃ s t,branchwiseEquivalent (input owner) s t ∧ ¬pairedEquivalent (input owner) s t) ∧
    (∀ perturb squared,Probability kernelStates (candidate (input owner) perturb squared) ∧
      Fixed kernelStates (closure (input owner) perturb squared) (candidate (input owner) perturb squared) ∧
      (∀ x,Probability kernelStates x → Fixed kernelStates (closure (input owner) perturb squared) x →
        x=candidate (input owner) perturb squared)) ∧
    forward (input owner)≠reverse (input owner) ∧
    OperationalViability.Accept (viabilitySchema owner) (viabilityData (input owner)) :=
  ⟨stable_partition_full_exit_future owner,actual_current_constant owner,⟨_,_,paired_binding_split owner⟩,
    all_four_probability_fixed_unique owner,(actual_cycle_directionality owner).2.2,actual_viability owner⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype
