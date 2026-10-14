import CSTTT.FullNative.PhysicalExecution

namespace CSTTT.FullNative.SnapshotExecution
open AccountExecution PhysicalExecution
set_option autoImplicit false

def putOwner {X : Type} (f : Owner → X) (o : Owner) (x : X) : Owner → X :=
  fun p => if p=o then x else f p

def hardwareToken (o : Owner) : Token := ⟨o.val,Nat.lt_trans o.isLt (by decide)⟩

structure Snapshot where
  sourceOwner : Owner
  sourceToken : Token
  state : State
  program : Model
  receipt : Receipt

structure World where
  accounts : Accounts
  carriers : Owner → Option Local
  slots : Owner → Option Snapshot
  bridge : Option Model

def initialWorld : World :=
  ⟨initial,(fun o => if o=0 then some source.resident else none),(fun _ => none),some model⟩

def mount (w : World) (o : Owner) (x : Execution) : World :=
  {w with
    accounts := x.accounts
    carriers := putOwner w.carriers o (some x.resident)}

def nativeRows (supply : Supply) (w : World) (o : Owner) (a : Bool) : List (World × Nat) :=
  match w.carriers o with
  | none => []
  | some p => if p.owner=o then
      (rawRows supply ⟨w.accounts,p⟩ a).map fun e => (mount w o e.1,e.2)
    else []

def reserveSiblings (w : World) : Option World :=
  (allocateSiblings w.accounts).map fun accounts => {w with accounts := accounts}

def writeSnapshot (w : World) (target : Owner) : Option World :=
  if target=0 then none else
  match w.carriers 0 with
  | none => none
  | some p =>
    match p.installed,p.receipts.head? with
    | some d,some r =>
      if p.owner=0 ∧ enabled w.accounts p.owner p.token = true ∧
        r.after=p.current ∧ r.issuer = .localGenerator p.owner ∧ r.token=p.token ∧
        (r.after,r.weight) ∈ d.rows r.before r.action then
        some {w with slots := (putOwner w.slots target
          (some ⟨p.owner,p.token,p.current,d,r⟩))}
      else none
    | _,_ => none

def activate (w : World) (target : Owner) : Option World :=
  if target=0 then none else
  match w.slots target,w.carriers target with
  | some s,none =>
    if enabled w.accounts target (hardwareToken target) then
      some {w with
        carriers := putOwner w.carriers target
          (some ⟨target,hardwareToken target,some s.program,s.state,[],
            ([s.state],[s.receipt.serial]),0⟩)
        slots := putOwner w.slots target none}
    else none
  | _,_ => none

def withdraw (w : World) : World :=
  {w with
    carriers := putOwner w.carriers 0 none
    bridge := none
    slots := (fun _ => none)}

def destroySource (w : World) : World :=
  {w with carriers := putOwner w.carriers 0 none}

def jointRows (supply : Supply) (w : World) (a b : Bool) : List (World × Nat) :=
  (nativeRows supply w 1 a).flatMap fun first =>
    (nativeRows supply first.1 2 b).map fun second => (second.1,first.2*second.2)

theorem missing_source (w : World) (o : Owner) (h : w.carriers 0 = none) :
    writeSnapshot w o = none := by
  simp [writeSnapshot,h]

theorem missing_slot (w : World) (o : Owner) (h : w.slots o = none) :
    activate w o = none := by
  simp [activate,h]

theorem missing_local_generator (supply : Supply) (w : World) (o : Owner) (a : Bool)
    (missing : w.carriers o = none) : nativeRows supply w o a = [] := by
  simp [nativeRows,missing]

theorem activation_consumes_snapshot (w w' : World) (o : Owner)
    (success : activate w o = some w') : w'.slots o = none ∧
      ∃ s, w.slots o = some s ∧ w'.carriers o =
        some ⟨o,hardwareToken o,some s.program,s.state,[],([s.state],[s.receipt.serial]),0⟩ := by
  unfold activate at success
  split at success
  · contradiction
  · split at success
    · rename_i unused slots s hs hp
      split at success
      · have eq := Option.some.inj success
        rw [← eq]
        exact ⟨by simp [putOwner],s,hs,by simp [putOwner]⟩
      · contradiction
    · contradiction

theorem activation_once (w w' : World) (o : Owner) (success : activate w o = some w') :
    activate w' o = none := missing_slot w' o (activation_consumes_snapshot w w' o success).1

theorem withdrawn_source_bridge (w : World) :
    (withdraw w).carriers 0 = none ∧ (withdraw w).bridge = none ∧
      (∀ o, (withdraw w).slots o = none) := by
  exact ⟨by simp [withdraw,putOwner],rfl,fun _ => rfl⟩

def afterSource : World := mount initialWorld 0 replicaLeft
def reservedAccounts : Accounts :=
  {replicaLeft.accounts with
    allocation := (put (put replicaLeft.accounts.allocation 1 (some (.localGenerator 1)))
      2 (some (.localGenerator 2)))}
def reserved : World := {afterSource with accounts := reservedAccounts}

def sourceSnapshot : Snapshot :=
  ⟨0,0,FullInterface.replicaLeft,model,issued renewable source false FullInterface.replicaLeft 1⟩
def firstWritten : World :=
  {reserved with slots := putOwner reserved.slots 1 (some sourceSnapshot)}
def bothWritten : World :=
  {firstWritten with slots := putOwner firstWritten.slots 2 (some sourceSnapshot)}
def activatedLocal (owner : Owner) : Local :=
  ⟨owner,hardwareToken owner,some sourceSnapshot.program,sourceSnapshot.state,[],
    ([sourceSnapshot.state],[sourceSnapshot.receipt.serial]),0⟩
def firstActivated : World :=
  {bothWritten with
    carriers := putOwner bothWritten.carriers 1 (some (activatedLocal 1))
    slots := putOwner bothWritten.slots 1 none}
def bothActivated : World :=
  {firstActivated with
    carriers := putOwner firstActivated.carriers 2 (some (activatedLocal 2))
    slots := putOwner firstActivated.slots 2 none}
def autonomousSiblings : World := withdraw bothActivated

theorem source_step_supported : (afterSource,1) ∈ nativeRows renewable initialWorld 0 false := by
  simp only [nativeRows,initialWorld,if_true,source]
  change (afterSource,1) ∈ (rawRows renewable PhysicalExecution.source false).map _
  apply List.mem_map.mpr
  exact ⟨(replicaLeft,1),by
    rw [sector_rows _ source_sector]
    simp [replicaLeft,source,FullNative.rows,kernels,bits,weight,diagonal,
      FullInterface.rootState,FullInterface.replicaLeft],rfl⟩

theorem reserve_step : reserveSiblings afterSource = some reserved := by
  have h : afterSource.accounts.allocation 1 = none ∧
      afterSource.accounts.allocation 2 = none ∧
      afterSource.accounts.charge 1 = true ∧ afterSource.accounts.charge 2 = true ∧
      (∀ t : Token, afterSource.accounts.allocation t ≠ some (.localGenerator 1) ∧
        afterSource.accounts.allocation t ≠ some (.localGenerator 2)) := by
    refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro t
    have ht : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by
      have hlt := t.isLt
      simp only [Fin.ext_iff]
      omega
    rcases ht with rfl | rfl | rfl | rfl <;> decide +kernel
  unfold reserveSiblings allocateSiblings
  rw [if_pos h]
  rfl

theorem write_first_step : writeSnapshot reserved 1 = some firstWritten := by rfl
theorem write_second_step : writeSnapshot firstWritten 2 = some bothWritten := by rfl
theorem activate_first_step : activate bothWritten 1 = some firstActivated := by rfl
theorem activate_second_step : activate firstActivated 2 = some bothActivated := by rfl

theorem literal_snapshot_dependency :
    sourceSnapshot.state = replicaLeft.resident.current ∧
    sourceSnapshot.receipt = (issued renewable source false FullInterface.replicaLeft 1) ∧
    sourceSnapshot.program = model ∧
    (autonomousSiblings.carriers 1).map Local.current = some sourceSnapshot.state ∧
    (autonomousSiblings.carriers 2).map Local.current = some sourceSnapshot.state := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem siblings_actual_sectors :
    sector ⟨autonomousSiblings.accounts,activatedLocal 1⟩ ∧
    sector ⟨autonomousSiblings.accounts,activatedLocal 2⟩ := by
  exact ⟨⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩⟩

theorem withdrawn_generators :
    autonomousSiblings.carriers 0 = none ∧ autonomousSiblings.bridge = none ∧
    autonomousSiblings.carriers 1 = some (activatedLocal 1) ∧
    autonomousSiblings.carriers 2 = some (activatedLocal 2) ∧
    (∀ o, autonomousSiblings.slots o = none) := by
  exact ⟨rfl,rfl,rfl,rfl,fun _ => rfl⟩

inductive Historical : World → Prop where
  | initial : Historical initialWorld
  | native {w v : World} {o : Owner} {a : Bool} {n : Nat} :
      Historical w → (v,n) ∈ nativeRows renewable w o a → Historical v
  | reserve {w v : World} : Historical w → reserveSiblings w = some v → Historical v
  | write {w v : World} {o : Owner} : Historical w → writeSnapshot w o = some v → Historical v
  | activation {w v : World} {o : Owner} : Historical w → activate w o = some v → Historical v
  | cut {w : World} : Historical w → Historical (withdraw w)
  | destruction {w : World} : Historical w → Historical (destroySource w)

theorem actual_snapshot_history : Historical autonomousSiblings := by
  apply Historical.cut
  apply Historical.activation (o := 2) _ activate_second_step
  apply Historical.activation (o := 1) _ activate_first_step
  apply Historical.write (o := 2) _ write_second_step
  apply Historical.write (o := 1) _ write_first_step
  apply Historical.reserve _ reserve_step
  exact Historical.native (o := 0) (a := false) (n := 1) .initial source_step_supported

def Siblings (w : World) : Prop :=
  ∃ p q, w.carriers 1 = some p ∧ w.carriers 2 = some q ∧
    p.owner=1 ∧ q.owner=2 ∧ p.token=1 ∧ q.token=2 ∧
    sector ⟨w.accounts,p⟩ ∧ sector ⟨w.accounts,q⟩

theorem autonomous_siblings : Siblings autonomousSiblings := by
  exact ⟨activatedLocal 1,activatedLocal 2,rfl,rfl,rfl,rfl,rfl,rfl,
    siblings_actual_sectors.1,siblings_actual_sectors.2⟩

theorem mount_other (w : World) (x : Execution) (o p : Owner) (different : p≠o) :
    (mount w o x).carriers p = w.carriers p := by
  simp [mount,putOwner,different]

def stepLocal (w : World) (o : Owner) (p : Local) (a : Bool) (s : State) (n : Nat) : World :=
  mount w o (advance renewable ⟨w.accounts,p⟩ a s n)

theorem separate_local_steps (w : World) (p q : Local) (a b : Bool)
    (s t : State) (n m : Nat) (hp : p.token=1) (hq : q.token=2) :
    stepLocal (stepLocal w 1 p a s n) 2 q b t m =
      stepLocal (stepLocal w 2 q b t m) 1 p a s n := by
  have hacc := independent_transactions renewable w.accounts 1 2 (by decide)
  have hcursor1 := other_cursor renewable w.accounts 2 1 (by decide)
  have hcursor2 := other_cursor renewable w.accounts 1 2 (by decide)
  cases w with
  | mk accounts carriers slots bridge =>
    simp only [stepLocal,mount,advance,issued,hp,hq] at *
    rw [hacc,hcursor1,hcursor2]
    congr 1
    funext o
    by_cases h1 : o=1 <;> by_cases h2 : o=2 <;>
      simp_all [putOwner]

theorem physical_row_exists (s : State) (a : Bool) :
    ∃ t n, (t,n) ∈ FullNative.rows s a ∧ n>0 := by
  have h := rows_positive_normalized s a
  cases he : FullNative.rows s a with
  | nil => simp [he] at h
  | cons e rest =>
    have hm : e ∈ FullNative.rows s a := by simp [he]
    exact ⟨e.1,e.2,by simp,(h.1 e hm).1⟩

theorem sibling_step_preserves (w : World) (h : Siblings w) (o : Owner) (a : Bool)
    (which : o=1 ∨ o=2) (v : World) (n : Nat)
    (edge : (v,n) ∈ nativeRows renewable w o a) : Siblings v := by
  obtain ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ := h
  rcases which with rfl | rfl
  · simp only [nativeRows,hp,po,if_true,sector_rows _ ps,List.map_map,
      Function.comp_def,List.mem_map] at edge
    obtain ⟨e,_,he⟩ := edge
    have hv : stepLocal w 1 p a e.1 e.2 = v := congrArg Prod.fst he
    rw [← hv]
    have hc : (stepLocal w 1 p a e.1 e.2).carriers 2 = some q := by
      simpa [stepLocal,hq] using
        mount_other w (advance renewable ⟨w.accounts,p⟩ a e.1 e.2) 1 2 (by decide)
    refine ⟨(advance renewable ⟨w.accounts,p⟩ a e.1 e.2).resident,q,
      by simp [stepLocal,mount,putOwner],hc,
      po,qo,pt,qt,sector_preserved _ ps _ _ _,?_⟩
    refine ⟨qs.1,qs.2.1,?_⟩
    change (transact renewable w.accounts p.token).charge q.token = true
    rw [pt,qt,other_charge renewable w.accounts 1 2 (by decide)]
    simpa [qt] using qs.2.2
  · simp only [nativeRows,hq,qo,if_true,sector_rows _ qs,List.map_map,
      Function.comp_def,List.mem_map] at edge
    obtain ⟨e,_,he⟩ := edge
    have hv : stepLocal w 2 q a e.1 e.2 = v := congrArg Prod.fst he
    rw [← hv]
    have hc : (stepLocal w 2 q a e.1 e.2).carriers 1 = some p := by
      simpa [stepLocal,hp] using
        mount_other w (advance renewable ⟨w.accounts,q⟩ a e.1 e.2) 2 1 (by decide)
    refine ⟨p,(advance renewable ⟨w.accounts,q⟩ a e.1 e.2).resident,hc,
      by simp [stepLocal,mount,putOwner],po,qo,pt,qt,?_,sector_preserved _ qs _ _ _⟩
    refine ⟨ps.1,ps.2.1,?_⟩
    change (transact renewable w.accounts q.token).charge p.token = true
    rw [qt,pt,other_charge renewable w.accounts 2 1 (by decide)]
    simpa [pt] using ps.2.2

theorem sibling_step_exists (w : World) (h : Siblings w) (o : Owner) (a : Bool)
    (which : o=1 ∨ o=2) : ∃ v n, (v,n) ∈ nativeRows renewable w o a ∧ n>0 := by
  obtain ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ := h
  rcases which with rfl | rfl
  · obtain ⟨s,n,edge,pos⟩ := physical_row_exists p.current a
    refine ⟨stepLocal w 1 p a s n,n,?_,pos⟩
    simp only [nativeRows,hp,po,if_true,sector_rows _ ps,List.map_map,Function.comp_def]
    exact List.mem_map.mpr ⟨(s,n),edge,rfl⟩
  · obtain ⟨s,n,edge,pos⟩ := physical_row_exists q.current a
    refine ⟨stepLocal w 2 q a s n,n,?_,pos⟩
    simp only [nativeRows,hq,qo,if_true,sector_rows _ qs,List.map_map,Function.comp_def]
    exact List.mem_map.mpr ⟨(s,n),edge,rfl⟩

theorem joint_step_exists (w : World) (h : Siblings w) (a b : Bool) :
    ∃ v n, (v,n) ∈ jointRows renewable w a b ∧ n>0 ∧ Siblings v := by
  obtain ⟨first,n,edge1,pos1⟩ := sibling_step_exists w h 1 a (Or.inl rfl)
  have hfirst := sibling_step_preserves w h 1 a (Or.inl rfl) first n edge1
  obtain ⟨second,m,edge2,pos2⟩ := sibling_step_exists first hfirst 2 b (Or.inr rfl)
  refine ⟨second,n*m,?_,Nat.mul_pos pos1 pos2,
    sibling_step_preserves first hfirst 2 b (Or.inr rfl) second m edge2⟩
  exact List.mem_flatMap.mpr ⟨(first,n),edge1,List.mem_map.mpr ⟨(second,m),edge2,rfl⟩⟩

inductive JointContinuation : World → List (Bool × Bool) → World → Prop where
  | nil (w : World) : JointContinuation w [] w
  | step {w v final : World} {a b : Bool} {n : Nat} {rest : List (Bool × Bool)} :
      (v,n) ∈ jointRows renewable w a b → n>0 →
      JointContinuation v rest final → JointContinuation w ((a,b)::rest) final

theorem joint_all_words (w : World) (h : Siblings w) (word : List (Bool × Bool)) :
    ∃ final, JointContinuation w word final ∧ Siblings final := by
  induction word generalizing w with
  | nil => exact ⟨w,.nil w,h⟩
  | cons actions rest ih =>
    obtain ⟨v,n,edge,pos,hv⟩ := joint_step_exists w h actions.1 actions.2
    obtain ⟨final,path,hfinal⟩ := ih v hv
    exact ⟨final,.step edge pos path,hfinal⟩

theorem withdrawal_mount (w : World) (o : Owner) (x : Execution) (different : o≠0) :
    withdraw (mount w o x) = mount (withdraw w) o x := by
  simp only [withdraw,mount]
  congr 1
  funext p
  by_cases hp0 : p=0 <;> by_cases hpo : p=o <;> simp_all [putOwner]

/-- Removing all external generator/access cells and snapshot slots commutes
with every target row. The target operator has no later source or bridge read. -/
theorem withdrawal_rows (supply : Supply) (w : World) (o : Owner) (a : Bool)
    (different : o≠0) :
    nativeRows supply (withdraw w) o a =
      (nativeRows supply w o a).map fun e => (withdraw e.1,e.2) := by
  have carrier : (withdraw w).carriers o = w.carriers o := by
    simp [withdraw,putOwner,different]
  simp only [nativeRows,carrier]
  cases hp : w.carriers o with
  | none => rfl
  | some p =>
    by_cases owner : p.owner=o
    · simp only [owner,if_true,List.map_map,Function.comp_def]
      simp only [withdrawal_mount w o _ different]
      rfl
    · simp [owner]

theorem missing_joint_second (supply : Supply) (w : World) (a b : Bool)
    (missing : w.carriers 2 = none) : jointRows supply w a b = [] := by
  unfold jointRows
  apply List.flatMap_eq_nil_iff.mpr
  intro e he
  unfold nativeRows at he
  split at he
  · simp at he
  · split at he
    · obtain ⟨x,_,hx⟩ := List.mem_map.mp he
      have eq : mount w 1 x.1 = e.1 := congrArg Prod.fst hx
      rw [← eq]
      have hm : (mount w 1 x.1).carriers 2 = none := by
        simpa [missing] using mount_other w x.1 1 2 (by decide)
      simp [missing_local_generator supply _ 2 b hm]
    · simp at he

theorem joint_history (w final : World) (word : List (Bool × Bool))
    (start : Historical w) (path : JointContinuation w word final) : Historical final := by
  induction path with
  | nil => exact start
  | @step w v final a b n rest edge positive path ih =>
    obtain ⟨first,hfirst,second⟩ := List.mem_flatMap.mp edge
    obtain ⟨last,hlast,eq⟩ := List.mem_map.mp second
    have hv : last.1 = v := congrArg Prod.fst eq
    apply ih
    rw [← hv]
    exact Historical.native (Historical.native start hfirst) hlast

theorem actual_joint_continuation (word : List (Bool × Bool)) :
    ∃ final, JointContinuation autonomousSiblings word final ∧
      Siblings final ∧ Historical final := by
  obtain ⟨final,path,siblings⟩ := joint_all_words autonomousSiblings autonomous_siblings word
  exact ⟨final,path,siblings,joint_history _ _ _ actual_snapshot_history path⟩

def externalView (w : World) :
    Option Local × Option Model × (Owner → Option Snapshot) × Bool × Bool × Nat × Nat :=
  (w.carriers 0,w.bridge,w.slots,w.accounts.charge 0,w.accounts.charge 3,
    w.accounts.portCursor 0,w.accounts.portCursor 3)

theorem sibling_external_unchanged (w : World) (h : Siblings w) (o : Owner) (a : Bool)
    (which : o=1 ∨ o=2) (v : World) (n : Nat)
    (edge : (v,n) ∈ nativeRows renewable w o a) : externalView v = externalView w := by
  obtain ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ := h
  rcases which with rfl | rfl
  · simp only [nativeRows,hp,po,if_true,sector_rows _ ps,List.map_map,
      Function.comp_def,List.mem_map] at edge
    obtain ⟨e,_,he⟩ := edge
    have hv : stepLocal w 1 p a e.1 e.2 = v := congrArg Prod.fst he
    rw [← hv]
    simp [externalView,stepLocal,mount,advance,transact,debit,putOwner,put,pt]
  · simp only [nativeRows,hq,qo,if_true,sector_rows _ qs,List.map_map,
      Function.comp_def,List.mem_map] at edge
    obtain ⟨e,_,he⟩ := edge
    have hv : stepLocal w 2 q a e.1 e.2 = v := congrArg Prod.fst he
    rw [← hv]
    simp [externalView,stepLocal,mount,advance,transact,debit,putOwner,put,qt]

theorem joint_preserves (w : World) (h : Siblings w) (a b : Bool) (v : World) (n : Nat)
    (edge : (v,n) ∈ jointRows renewable w a b) :
    Siblings v ∧ externalView v = externalView w := by
  obtain ⟨first,hfirst,second⟩ := List.mem_flatMap.mp edge
  obtain ⟨last,hlast,eq⟩ := List.mem_map.mp second
  have hv : last.1 = v := congrArg Prod.fst eq
  rw [← hv]
  have hf := sibling_step_preserves w h 1 a (Or.inl rfl) first.1 first.2 hfirst
  exact ⟨sibling_step_preserves first.1 hf 2 b (Or.inr rfl) last.1 last.2 hlast,
    (sibling_external_unchanged first.1 hf 2 b (Or.inr rfl) _ _ hlast).trans
      (sibling_external_unchanged w h 1 a (Or.inl rfl) _ _ hfirst)⟩

theorem joint_path_preserves (w final : World) (word : List (Bool × Bool))
    (h : Siblings w) (path : JointContinuation w word final) :
    Siblings final ∧ externalView final = externalView w := by
  induction path with
  | nil => exact ⟨h,rfl⟩
  | @step w v final a b n rest edge positive path ih =>
    have hv := joint_preserves w h a b v n edge
    have hf := ih hv.1
    exact ⟨hf.1,hf.2.trans hv.2⟩

theorem actual_joint_all_words (word : List (Bool × Bool)) :
    ∃ final, JointContinuation autonomousSiblings word final ∧
      Siblings final ∧ Historical final ∧ externalView final = externalView autonomousSiblings := by
  obtain ⟨final,path,siblings,history⟩ := actual_joint_continuation word
  exact ⟨final,path,siblings,history,
    (joint_path_preserves _ _ _ autonomous_siblings path).2⟩

def singleActivated : World :=
  {firstWritten with
    carriers := putOwner firstWritten.carriers 1 (some (activatedLocal 1))
    slots := putOwner firstWritten.slots 1 none}

theorem destructive_write_consume :
    (destroySource firstWritten).carriers 0 = none ∧
    (destroySource firstWritten).slots 1 = some sourceSnapshot ∧
    activate (destroySource firstWritten) 1 = some (destroySource singleActivated) := by
  refine ⟨rfl,rfl,?_⟩
  change some {firstWritten with
    carriers := putOwner (putOwner firstWritten.carriers 0 none) 1 (some (activatedLocal 1))
    slots := putOwner firstWritten.slots 1 none} = some (destroySource singleActivated)
  simp only [destroySource,singleActivated]
  congr 2
  funext o
  by_cases h0 : o=0 <;> by_cases h1 : o=1 <;> simp_all [putOwner]

theorem destructive_historical : Historical (withdraw (destroySource singleActivated)) := by
  apply Historical.cut
  apply Historical.activation (o := 1) _ destructive_write_consume.2.2
  apply Historical.destruction
  apply Historical.write (o := 1) _ write_first_step
  apply Historical.reserve _ reserve_step
  exact Historical.native (o := 0) (a := false) (n := 1) .initial source_step_supported

end CSTTT.FullNative.SnapshotExecution
