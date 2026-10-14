import CSTTT.FullNative.JointFuture

namespace CSTTT.FullNative.JointClaims
open AccountExecution PhysicalExecution SnapshotExecution TemporalTransport JointFuture
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def contexts (w : World) : Option (FullInterface.Context × FullInterface.Context) :=
  (worldRuns w).map fun r => (r.1.context,r.2.context)
def elapsed (n : Nat) (c : FullInterface.Context) : FullInterface.Context :=
  {c with order:=c.order+n,localRecords:=c.localRecords+n}

theorem joint_step_contexts (w v : World) (h : Siblings w) (a b : Bool) (n : Nat)
    (edge : (v,n)∈jointRows renewable w a b) :
    contexts v=(contexts w).map fun cs => (elapsed 1 cs.1,elapsed 1 cs.2) := by
  obtain ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ := h
  rw [raw_joint_rows w p q hp hq po qo pt qt ps qs] at edge
  obtain ⟨l,_,member⟩ := List.mem_flatMap.mp edge
  obtain ⟨r,_,eq⟩ := List.mem_map.mp member
  have same : pairStep w p q a b l r=v := congrArg Prod.fst eq
  rw [←same]
  unfold contexts
  rw [pair_frames w p q pt qt ps qs]
  simp [worldRuns,hp,hq,elapsed,
    FullInterface.advance,FullInterface.advanceContext]

theorem joint_path_contexts (w final : World) (word : List (Bool × Bool)) (h : Siblings w)
    (path : JointContinuation w word final) :
    contexts final=(contexts w).map fun cs => (elapsed word.length cs.1,elapsed word.length cs.2) := by
  induction path with
  | nil => simp [elapsed]
  | @step w v final a b n rest edge positive path ih =>
    rw [ih (joint_preserves w h a b v n edge).1,joint_step_contexts w v h a b n edge,Option.map_map]
    simp [elapsed,Nat.add_comm,Nat.add_left_comm,Function.comp_def]

theorem copy_world_siblings : Siblings Credit.creditedTransferWorld := by
  exact ⟨(targetAtCopy false).resident,(targetAtCopy true).resident,rfl,rfl,rfl,rfl,rfl,rfl,
    (actual_copy_transport false).2.1,(actual_copy_transport true).2.1⟩

theorem copy_contexts : contexts Credit.creditedTransferWorld=some
    (⟨0,0,([anchor.state],[anchor.receipt]),true,1⟩,
     ⟨0,0,([anchor.state],[anchor.receipt]),true,2⟩) := by decide +kernel

theorem transported_copy_counts (final : World) (word : List (Bool × Bool))
    (path : JointContinuation Credit.creditedTransferWorld word final) :
    (contexts final).map (fun cs =>
      ((shiftContext anchor cs.1).order,(shiftContext anchor cs.1).localRecords,
       (shiftContext anchor cs.2).order,(shiftContext anchor cs.2).localRecords))=
      some (anchor.order+word.length,anchor.records+word.length,
        anchor.order+word.length,anchor.records+word.length) ∧
    (contexts final).map (fun cs => (cs.1.rootedRoute,cs.2.rootedRoute))=
      some (([anchor.state],[anchor.receipt]),([anchor.state],[anchor.receipt])) := by
  rw [joint_path_contexts _ _ _ copy_world_siblings path,copy_contexts]
  constructor <;> simp [shiftContext,elapsed]

theorem retained_epoch_after_joint_path (final : World) (word : List (Bool × Bool))
    (path : JointContinuation Credit.creditedTransferWorld word final) :
    (contexts final).map (fun cs => (retainedEpoch cs.1,retainedEpoch cs.2))=
      some (some (anchor.order,anchor.records),some (anchor.order,anchor.records)) := by
  rw [joint_path_contexts _ _ _ copy_world_siblings path,copy_contexts]
  have epoch : anchor.order=anchor.receipt/4+1 ∧ anchor.records=anchor.receipt/4+1 := by decide +kernel
  simp [elapsed,retainedEpoch,epoch.1,epoch.2]

theorem shared_root_conflict (final : World) (word : List (Bool × Bool))
    (path : JointContinuation Credit.creditedTransferWorld word final) (p q : Local)
    (hp : final.carriers 1=some p) (hq : final.carriers 2=some q)
    (l r : Nat) (left : p.rootedRoute.2=[l]) (right : q.rootedRoute.2=[r]) : l=r := by
  have roots := (transported_copy_counts final word path).2
  simp only [contexts,worldRuns,hp,hq] at roots
  have equal : (p.rootedRoute,q.rootedRoute)=
      (([anchor.state],[anchor.receipt]),([anchor.state],[anchor.receipt])) := Option.some.inj roots
  have first := congrArg (fun z => z.1.2) equal
  have second := congrArg (fun z => z.2.2) equal
  change p.rootedRoute.2=[anchor.receipt] at first
  change q.rootedRoute.2=[anchor.receipt] at second
  rw [left] at first
  rw [right] at second
  exact List.cons.inj (first.trans second.symm) |>.1

theorem duplicate_token_conflict (a : Accounts) (t : Token)
    (left : a.allocation t=some (.localGenerator 1))
    (right : a.allocation t=some (.localGenerator 2)) : False := by
  have impossible := allocation_exclusive a 1 2 t left right
  exact (by decide : (1:Owner)≠2) impossible

def correlatedOutcome (right : Bool) : World :=
  pairStep Credit.creditedBothWorld Credit.creditedFirstLocal Credit.creditedSecondLocal false false
    (Binding.splitState Credit.creditedFirstLocal.current right,weight Credit.creditedFirstLocal.current false right)
    (Binding.splitState Credit.creditedSecondLocal.current right,weight Credit.creditedSecondLocal.current false right)

theorem correlated_outcome_historical (right : Bool) : Historical (correlatedOutcome right) ∧
    Siblings (correlatedOutcome right) := by
  have left := (Binding.split_supported Credit.creditedFirstLocal.current right).1
  have rightEdge := (Binding.split_supported Credit.creditedSecondLocal.current right).1
  constructor
  · exact historical_gluing _ Credit.credited_both_historical _ _ rfl rfl rfl rfl rfl rfl
      ⟨rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl⟩ false false _ _ left rightEdge
  · exact (simultaneous_successors _ _ _ rfl rfl rfl rfl rfl rfl
      ⟨rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl⟩ false false _ _ left rightEdge).2.2.2

def correlatedEvent (w : World) : Bool :=
  [false,true].any fun right => decide
    ((w.carriers 1).map Local.current=some (Binding.splitState Credit.creditedFirstLocal.current right) ∧
     (w.carriers 2).map Local.current=some (Binding.splitState Credit.creditedSecondLocal.current right))
def eventRows : List (World × Rat) :=
  (normalizedJointRows Credit.creditedBothWorld (false,false)).filter fun e => correlatedEvent e.1
def eventMass : Rat := (eventRows.map Prod.snd).sum

theorem actual_conditioning_weights : (eventRows.map Prod.snd)=[1/256,9/256] ∧ eventMass=5/128 := by
  decide +kernel

def branchLaw (right : Bool) (w : World) (word : List Bool) (trace : List Observation) : Option Rat :=
  (w.carriers (branchOwner right)).map fun p =>
    WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (shiftRun anchor (frame x)))
      ⟨w.accounts,p⟩ word trace

/-- Actual conditioning on the two listed positive raw outcomes. This defines
a readout of existing rows, not a replacement transition or new raw model. -/
def conditionedJoint (word : List (Bool × Bool)) (trace : List (Observation × Observation)) : Option Rat :=
  if 0<eventMass then some (eventRows.foldr (fun e acc => e.2*jointLaw anchor e.1 word trace+acc) 0/eventMass)
  else none
def conditionedBranch (right : Bool) (word : List Bool) (trace : List Observation) : Option Rat :=
  if 0<eventMass then
    (eventRows.foldr (fun e acc => do
      let value ← branchLaw right e.1 word trace
      let rest ← acc
      pure (e.2*value+rest)) (some 0)).map (·/eventMass)
  else none

theorem correlated_observation_present (right : Bool) :
    (worldObservation anchor (correlatedOutcome right)).isSome=true := by cases right <;> decide +kernel
def correlatedObservation (right : Bool) : Observation × Observation :=
  (worldObservation anchor (correlatedOutcome right)).get (correlated_observation_present right)

theorem conditioning_factorization_countertrace :
    conditionedJoint [] [correlatedObservation false]=some (1/10) ∧
    conditionedBranch false [] [(correlatedObservation false).1]=some (1/10) ∧
    conditionedBranch true [] [(correlatedObservation false).2]=some (1/10) ∧
    (1/10:Rat)≠(1/10:Rat)*(1/10:Rat) := by decide +kernel

theorem source_copy_joint_transport (word : List (Bool × Bool)) (trace : List (Observation × Observation)) :
    jointLaw anchor Credit.creditedTransferWorld word trace=
      WeightedFuture.law FullInterface.rows FullInterface.observe
        (rebase (targetAtCopy false).resident.owner (targetAtCopy false).resident.rootedRoute (frame sourceAtCopy))
        (word.map Prod.fst) (trace.map Prod.fst) *
      WeightedFuture.law FullInterface.rows FullInterface.observe
        (rebase (targetAtCopy true).resident.owner (targetAtCopy true).resident.rootedRoute (frame sourceAtCopy))
        (word.map Prod.snd) (trace.map Prod.snd) := by
  rw [actual_branch_factorization anchor Credit.creditedTransferWorld (targetAtCopy false).resident
    (targetAtCopy true).resident rfl rfl rfl rfl rfl rfl
    (actual_copy_transport false).2.1 (actual_copy_transport true).2.1]
  change WeightedFuture.law (normalizedRows renewable)
    (fun x => FullInterface.observe (shiftRun anchor (frame x))) (targetAtCopy false)
    (word.map Prod.fst) (trace.map Prod.fst) *
    WeightedFuture.law (normalizedRows renewable)
    (fun x => FullInterface.observe (shiftRun anchor (frame x))) (targetAtCopy true)
    (word.map Prod.snd) (trace.map Prod.snd)=_
  rw [actual_transported_future false,actual_transported_future true]

theorem credited_joint_factorization (word : List (Bool × Bool)) (trace : List (Observation × Observation)) :
    jointLaw anchor Credit.creditedBothWorld word trace=
      WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (shiftRun anchor (frame x)))
        ⟨Credit.creditedBothWorld.accounts,Credit.creditedFirstLocal⟩ (word.map Prod.fst) (trace.map Prod.fst) *
      WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (shiftRun anchor (frame x)))
        ⟨Credit.creditedBothWorld.accounts,Credit.creditedSecondLocal⟩ (word.map Prod.snd) (trace.map Prod.snd) :=
  actual_branch_factorization anchor _ _ _ rfl rfl rfl rfl rfl rfl ⟨rfl,rfl,rfl⟩ ⟨rfl,rfl,rfl⟩ word trace

theorem credited_contexts : contexts Credit.creditedBothWorld=some
    (⟨6,6,([anchor.state],[anchor.receipt]),true,1⟩,
     ⟨6,6,([anchor.state],[anchor.receipt]),true,2⟩) := by decide +kernel

theorem credited_transported_counts (final : World) (word : List (Bool × Bool))
    (path : JointContinuation Credit.creditedBothWorld word final) :
    (contexts final).map (fun cs =>
      ((shiftContext anchor cs.1).order,(shiftContext anchor cs.2).order))=
      some (12+word.length,12+word.length) := by
  rw [joint_path_contexts _ _ _ Credit.credited_both_siblings path,credited_contexts]
  have epoch : anchor.order=6 := by decide +kernel
  simp [shiftContext,elapsed,epoch]
  omega

def branchProduct (w : World) (word : List (Bool × Bool)) (trace : List (Observation × Observation)) : Option Rat :=
  (worldRuns w).map fun rs =>
    WeightedFuture.law FullInterface.rows (fun r => FullInterface.observe (shiftRun anchor r))
      rs.1 (word.map Prod.fst) (trace.map Prod.fst) *
    WeightedFuture.law FullInterface.rows (fun r => FullInterface.observe (shiftRun anchor r))
      rs.2 (word.map Prod.snd) (trace.map Prod.snd)

theorem branch_product_value (w : World) (h : Siblings w) (word : List (Bool × Bool))
    (trace : List (Observation × Observation)) : branchProduct w word trace=some (jointLaw anchor w word trace) := by
  obtain ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ := h
  unfold branchProduct
  simp only [worldRuns,hp,hq]
  change some (_*_)=some (jointLaw anchor w word trace)
  exact congrArg some (world_joint_factorization anchor w p q ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ hp hq word trace).symm

def conditionedProducts (word : List (Bool × Bool)) (trace : List (Observation × Observation)) : Option Rat :=
  if 0<eventMass then
    (eventRows.foldr (fun e acc => do
      let value ← branchProduct e.1 word trace
      let rest ← acc
      pure (e.2*value+rest)) (some 0)).map (·/eventMass)
  else none

/-- After conditioning, average the products using the actual shared coupling;
the product of averaged branch laws is false in the preceding countertrace. -/
theorem conditioned_joint_sum_of_products (word : List (Bool × Bool)) (trace : List (Observation × Observation)) :
    conditionedJoint word trace=conditionedProducts word trace := by
  have every : ∀ e∈eventRows, branchProduct e.1 word trace=some (jointLaw anchor e.1 word trace) := by
    intro e member
    have raw := (List.mem_filter.mp member).1
    exact branch_product_value e.1 (normalized_siblings_preserved _ Credit.credited_both_siblings _ e raw) word trace
  have fold : ∀ rs : List (World × Rat),
      (∀ e∈rs, branchProduct e.1 word trace=some (jointLaw anchor e.1 word trace)) →
      rs.foldr (fun e acc => do
        let value ← branchProduct e.1 word trace
        let rest ← acc
        pure (e.2*value+rest)) (some 0)=
      some (rs.foldr (fun e acc => e.2*jointLaw anchor e.1 word trace+acc) 0) := by
    intro rs
    induction rs with
    | nil => intro _; rfl
    | cons e rest ih =>
      intro valid
      simp only [List.foldr_cons]
      rw [valid e (by simp),ih (fun z hz => valid z (by simp [hz]))]
      rfl
  simp only [conditionedJoint,conditionedProducts,fold eventRows every,Option.map_some]

end CSTTT.FullNative.JointClaims
