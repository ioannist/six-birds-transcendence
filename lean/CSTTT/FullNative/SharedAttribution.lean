import CSTTT.FullNative.PublicShadow
import CSTTT.Fallback.OperationalTrace

/-! G29: a read-only provenance decoder on G27's actual source checkpoint and
two withdrawn targets. This adds no operation, installed program or raw input.
The event node is addressed above the three carrier addresses. A path is
strict operational ancestry, not reflexive or numerical identity. -/
namespace CSTTT.FullNative.SharedAttribution
open AccountExecution PhysicalExecution SnapshotExecution SharedPackage OriginalPackage
open CSTTT.FallbackTheory.OperationalTrace
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def receiptNode (r : Receipt) : Nat := 3+4*r.serial+r.token.val

/-- All inputs are read from the complete shared raw executions. A missing
carrier, program, account, receipt or matching retained root yields no edge. -/
def retainedEdges (source target : Raw) : List (Nat × Nat) :=
  match execution source,execution target with
  | some s,some t =>
    match s.resident.installed,s.resident.receipts.head? with
    | some d,some r =>
      if enabled s.accounts s.resident.owner s.resident.token=true ∧
        r.issuer=.localGenerator s.resident.owner ∧ r.token=s.resident.token ∧
        r.after=s.resident.current ∧ (r.after,r.weight)∈d.rows r.before r.action ∧
        t.resident.rootedRoute=([r.after],[r.serial]) then
        [(source.owner.val,receiptNode r),(receiptNode r,target.owner.val)]
      else []
    | _,_ => []
  | _,_ => []

def edges : List (Nat × Nat) :=
  retainedEdges sourceRaw (targetRaw false) ++ retainedEdges sourceRaw (targetRaw true)
def ancestry : Nat → Nat → Prop := Path edges
def emptyTarget (address : Nat) : Prop :=
  ∃ o : Owner, o.val=address ∧ (targetRaw false).world.carriers o=none

theorem actual_edges : edges=[(0,83),(83,1),(0,83),(83,2)] := by decide +kernel

theorem edge_provenance (right : Bool) :
    (targetExecution right).resident.installed=TemporalTransport.sourceAtCopy.resident.installed ∧
    (TemporalTransport.writtenSnapshot right).map (fun s => s.receipt)=
      TemporalTransport.sourceAtCopy.resident.receipts.head? ∧
    (targetExecution right).resident.rootedRoute=([TemporalTransport.anchor.state],[TemporalTransport.anchor.receipt]) ∧
    TemporalTransport.consumedAnchor=some ⟨6,6,20,FullInterface.rootState⟩ := by
  have h := program_and_provenance_coherence right
  exact ⟨h.1,h.2.2.2.2,h.2.1,h.2.2.2.1⟩

theorem missing_source_edges (s t : Raw) (missing : execution s=none) : retainedEdges s t=[] := by
  simp [retainedEdges,missing]
theorem missing_target_edges (s t : Raw) (missing : execution t=none) : retainedEdges s t=[] := by
  simp [retainedEdges,missing]
theorem decoder_extensional (s t u v : Raw)
    (source : execution s=execution u) (target : execution t=execution v)
    (sourceAddress : s.owner=u.owner) (targetAddress : t.owner=v.owner) :
    retainedEdges s t=retainedEdges u v := by
  simp only [retainedEdges,source,target,sourceAddress,targetAddress]

theorem source_to_both_targets : ancestry 0 1 ∧ ancestry 0 2 := by
  have first : Path edges 0 83 := Path.one (by simp [actual_edges])
  exact ⟨Path.extend first (by simp [actual_edges]),Path.extend first (by simp [actual_edges])⟩

theorem ancestry_least (r : Nat → Nat → Prop)
    (contains : ∀ x y, (x,y)∈edges → r x y)
    (transitive : ∀ x y z, r x y → r y z → r x z) :
    ∀ x y, ancestry x y → r x y := path_least edges r contains transitive

theorem ancestry_no_ex_nihilo (x y : Nat) (h : ancestry x y) :
    (x,y)∈edges ∨ ∃ p, ancestry x p ∧ (p,y)∈edges := path_no_ex_nihilo edges x y h

theorem path_first {es : List (Nat × Nat)} {x z : Nat} (h : Path es x z) :
    ∃ y, (x,y)∈es := by
  induction h with
  | one member => exact ⟨_,member⟩
  | extend _ _ ih => exact ih

theorem target_is_not_source (right : Bool) (endpoint : Nat) :
    ¬ancestry (TemporalTransport.branchOwner right).val endpoint := by
  intro h
  obtain ⟨y,member⟩ := path_first h
  rw [actual_edges] at member
  cases right <;> simp [TemporalTransport.branchOwner] at member

theorem no_incoming_source (root : Nat) : ¬ancestry root 0 := by
  exact no_incoming_excludes edges 0 (by intro p; simp [actual_edges]) root

theorem original_target_role_countertrace (fused : Nat) (notEmpty : ¬emptyTarget fused) :
    ¬CSTTT.Prospects.FallbackFissionFusionEmpty Nat ancestry 0 1 2 fused emptyTarget := by
  rintro ⟨_,_,merger | empty⟩
  · exact target_is_not_source false fused merger.1
  · exact notEmpty empty

theorem withdrawn_address_empty : emptyTarget 0 :=
  ⟨0,rfl,single_historical_chain.2.2.2.2.2.2.2.1⟩

/-- Only the original disjunctive schema's EMPTY arm. It supplies no positive
guarded fusion and is deliberately not advertised as the full TTF-04 return. -/
theorem original_empty_arm :
    CSTTT.Prospects.FallbackFissionFusionEmpty Nat ancestry 0 1 2 0 emptyTarget :=
  ⟨source_to_both_targets.1,source_to_both_targets.2,Or.inr withdrawn_address_empty⟩

theorem occupied_target_not_empty : ¬emptyTarget 1 := by
  rintro ⟨o,eq,missing⟩
  have same : o=(1 : Owner) := Fin.ext eq
  subst o
  have present := PublicShadow.decoded_resident (targetRaw false) (targetExecution false) (target_read false)
  change (targetRaw false).world.carriers 1=some (targetExecution false).resident at present
  rw [present] at missing
  contradiction

theorem actual_nonempty_request_rejected :
    ¬CSTTT.Prospects.FallbackFissionFusionEmpty Nat ancestry 0 1 2 1 emptyTarget :=
  original_target_role_countertrace 1 occupied_target_not_empty

/-- The original operational fusion needs BOTH parents retired and an active
fresh output. This is a readout of actual carrier cells, not joint-law equality. -/
def FusionRealized (w : World) : Prop :=
  w.carriers 1=none ∧ w.carriers 2=none ∧ ∃ o : Owner, w.carriers o≠none

theorem siblings_are_not_fusion (w : World) (h : Siblings w) : ¬FusionRealized w := by
  obtain ⟨p,q,hp,hq,rest⟩ := h
  rintro ⟨gone,_,_⟩
  rw [hp] at gone
  contradiction

theorem all_joint_paths_have_no_merger (word : List (Bool × Bool)) (w : World)
    (path : JointContinuation (targetRaw false).world word w) :
    Siblings w ∧ ¬FusionRealized w ∧ w.carriers 0=none ∧ w.bridge=none := by
  have h := joint_path_preserves _ _ _ Credit.credited_both_siblings path
  have external := congrArg (fun e => (e.1,e.2.1)) h.2
  change (w.carriers 0,w.bridge)=
    ((targetRaw false).world.carriers 0,(targetRaw false).world.bridge) at external
  rw [single_historical_chain.2.2.2.2.2.2.2.1,
    single_historical_chain.2.2.2.2.2.2.2.2] at external
  exact ⟨h.1,siblings_are_not_fusion w h.1,(Prod.mk.inj external).1,(Prod.mk.inj external).2⟩

theorem no_fused_source_rows (word : List (Bool × Bool)) (w : World)
    (path : JointContinuation (targetRaw false).world word w) (a : Bool) :
    nativeRows renewable w 0 a=[] :=
  missing_local_generator _ _ _ _ (all_joint_paths_have_no_merger word w path).2.2.1

end CSTTT.FullNative.SharedAttribution
