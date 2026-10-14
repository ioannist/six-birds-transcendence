import CSTTT.FullNative.TemporalTransport

namespace CSTTT.FullNative.JointFuture
open AccountExecution PhysicalExecution SnapshotExecution TemporalTransport
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem foldr_congr_on {X Y : Type} (xs : List X) (f g : X → Y → Y) (z : Y)
    (equal : ∀ e ∈ xs, ∀ acc, f e acc=g e acc) : xs.foldr f z=xs.foldr g z := by
  induction xs with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.foldr_cons]
    rw [equal e (by simp),ih (fun t ht => equal t (by simp [ht]))]

theorem foldr_scale {X : Type} (xs : List X) (f : X → Rat) (c : Rat) :
    xs.foldr (fun e acc => c*f e+acc) 0=c*xs.foldr (fun e acc => f e+acc) 0 := by
  induction xs with
  | nil => simp [Rat.mul_zero]
  | cons e rest ih => simp only [List.foldr_cons,ih,Rat.mul_add]

theorem foldr_offset {X : Type} (xs : List X) (f : X → Rat) (c : Rat) :
    xs.foldr (fun e acc => f e+acc) c=xs.foldr (fun e acc => f e+acc) 0+c := by
  induction xs with
  | nil => simp [Rat.zero_add]
  | cons e rest ih => simp only [List.foldr_cons,ih,Rat.add_assoc]

theorem double_product {X Y : Type} (xs : List X) (ys : List Y) (f : X → Rat) (g : Y → Rat) :
    xs.foldr (fun x acc => ys.foldr (fun y acc => f x*g y+acc) 0+acc) 0=
      xs.foldr (fun x acc => f x+acc) 0 * ys.foldr (fun y acc => g y+acc) 0 := by
  induction xs with
  | nil => simp [Rat.zero_mul]
  | cons e rest ih =>
    rw [List.foldr_cons,List.foldr_cons,foldr_scale,ih,Rat.add_mul]

theorem mul_cross (a b c d : Rat) : (a*b)*(c*d)=(a*c)*(b*d) := by
  rw [Rat.mul_assoc a b (c*d),←Rat.mul_assoc b c d,Rat.mul_comm b c,
    Rat.mul_assoc c b d,←Rat.mul_assoc a c (b*d)]

theorem cartesian_product {X Y : Type} (xs : List X) (ys : List Y) (f : X → Rat) (g : Y → Rat) :
    xs.foldr (fun x acc => ys.foldr (fun y acc => f x*g y+acc) acc) 0=
      xs.foldr (fun x acc => f x+acc) 0 * ys.foldr (fun y acc => g y+acc) 0 := by
  calc
    _=xs.foldr (fun x acc => ys.foldr (fun y acc => f x*g y+acc) 0+acc) 0 := by
      apply foldr_congr_on
      intro x _ acc
      exact foldr_offset ys _ acc
    _=_ := double_product xs ys f g

def productRows {S T A B : Type} (left : S → A → List (S × Rat))
    (right : T → B → List (T × Rat)) (s : S × T) (a : A × B) : List ((S × T) × Rat) :=
  (left s.1 a.1).flatMap fun l => (right s.2 a.2).map fun r => ((l.1,r.1),l.2*r.2)

theorem product_future_law {S T A B V W : Type} [DecidableEq V] [DecidableEq W]
    (left : S → A → List (S × Rat)) (right : T → B → List (T × Rat))
    (ol : S → V) (orr : T → W) (s : S × T) (word : List (A × B)) (trace : List (V × W)) :
    WeightedFuture.law (productRows left right) (fun s => (ol s.1,orr s.2)) s word trace=
      WeightedFuture.law left ol s.1 (word.map Prod.fst) (trace.map Prod.fst) *
      WeightedFuture.law right orr s.2 (word.map Prod.snd) (trace.map Prod.snd) := by
  induction word generalizing s trace with
  | nil =>
    cases trace with
    | nil => simp [WeightedFuture.law]
    | cons v tail =>
      cases tail with
      | nil =>
        by_cases hl : v.1=ol s.1 <;> by_cases hr : v.2=orr s.2 <;>
          simp [WeightedFuture.law,Prod.ext_iff,hl,hr]
      | cons w rest => simp [WeightedFuture.law]
  | cons a rest ih =>
    cases trace with
    | nil => simp [WeightedFuture.law]
    | cons v tail =>
      by_cases hl : v.1=ol s.1 <;> by_cases hr : v.2=orr s.2
      · simp only [WeightedFuture.law,List.map_cons,if_true,
          show v=(ol s.1,orr s.2) from Prod.ext hl hr,productRows,
          List.foldr_flatMap,List.foldr_map]
        simp only [ih]
        let f := fun l : S × Rat => l.2*WeightedFuture.law left ol l.1 (rest.map Prod.fst) (tail.map Prod.fst)
        let g := fun r : T × Rat => r.2*WeightedFuture.law right orr r.1 (rest.map Prod.snd) (tail.map Prod.snd)
        calc
          _=(left s.1 a.1).foldr (fun l acc =>
              (right s.2 a.2).foldr (fun r acc => f l*g r+acc) acc) 0 := by
            apply foldr_congr_on
            intro l _ acc
            apply foldr_congr_on
            intro r _ acc
            rw [mul_cross]
          _=_ := cartesian_product _ _ f g
      · simp [WeightedFuture.law,Prod.ext_iff,hl,hr,Rat.mul_zero]
      · simp [WeightedFuture.law,Prod.ext_iff,hl,hr]
      · simp [WeightedFuture.law,Prod.ext_iff,hl,hr]

theorem invariant_projection_law {S Q A V : Type} [DecidableEq V]
    (rs : S → A → List (S × Rat)) (qs : Q → A → List (Q × Rat))
    (project : S → Q) (ob : Q → V) (good : S → Prop)
    (aligned : ∀ s, good s → ∀ a, (rs s a).map (fun e => (project e.1,e.2))=qs (project s) a)
    (preserved : ∀ s, good s → ∀ a e, e∈rs s a → good e.1)
    (s : S) (hs : good s) (word : List A) (trace : List V) :
    WeightedFuture.law rs (fun s => ob (project s)) s word trace=
      WeightedFuture.law qs ob (project s) word trace := by
  induction word generalizing s trace with
  | nil => rfl
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons v tail =>
      simp only [WeightedFuture.law]
      by_cases same : v=ob (project s)
      · simp only [same,if_true]
        rw [←aligned s hs a,List.foldr_map]
        apply foldr_congr_on
        intro e member acc
        rw [ih e.1 (preserved s hs a e member) tail]
      · simp [same]

theorem normalized_product_weight (n m : Nat) :
    ((n*m:Nat):Rat)/256=((n:Rat)/16)*((m:Rat)/16) := by
  simp only [Rat.natCast_mul,Rat.div_def]
  rw [show (256:Rat)⁻¹=(16:Rat)⁻¹*(16:Rat)⁻¹ by decide +kernel,mul_cross]

def normalizedJointRows (w : World) (acts : Bool × Bool) : List (World × Rat) :=
  (jointRows renewable w acts.1 acts.2).map fun e => (e.1,(e.2:Rat)/256)
def worldRuns (w : World) : Option (FullInterface.Run × FullInterface.Run) := do
  let p ← w.carriers 1
  let q ← w.carriers 2
  pure (frame ⟨w.accounts,p⟩,frame ⟨w.accounts,q⟩)
def runProductRows := productRows FullInterface.rows FullInterface.rows
def optionalRows (rs : Option (FullInterface.Run × FullInterface.Run)) (a : Bool × Bool) :
    List (Option (FullInterface.Run × FullInterface.Run) × Rat) :=
  match rs with
  | none => []
  | some r => (runProductRows r a).map fun e => (some e.1,e.2)
def pairObservation (epoch : Anchor) (r : FullInterface.Run × FullInterface.Run) : Observation × Observation :=
  (FullInterface.observe (shiftRun epoch r.1),FullInterface.observe (shiftRun epoch r.2))
def worldObservation (epoch : Anchor) (w : World) : Option (Observation × Observation) :=
  (worldRuns w).map (pairObservation epoch)
def jointLaw (epoch : Anchor) (w : World) (word : List (Bool × Bool))
    (trace : List (Observation × Observation)) : Rat :=
  WeightedFuture.law normalizedJointRows (worldObservation epoch) w word (trace.map some)

def pairStep (w : World) (p q : Local) (a b : Bool) (l r : State × Nat) : World :=
  stepLocal (stepLocal w 1 p a l.1 l.2) 2 q b r.1 r.2

theorem other_sector (w : World) (p q : Local) (h : sector ⟨w.accounts,q⟩)
    (pt : p.token=1) (qt : q.token=2) (a : Bool) (s : State) (n : Nat) :
    sector ⟨(stepLocal w 1 p a s n).accounts,q⟩ := by
  refine ⟨h.1,h.2.1,?_⟩
  change (transact renewable w.accounts p.token).charge q.token=true
  rw [pt,qt,other_charge renewable w.accounts 1 2 (by decide)]
  simpa [qt] using h.2.2

theorem raw_joint_rows (w : World) (p q : Local)
    (hp : w.carriers 1=some p) (hq : w.carriers 2=some q)
    (po : p.owner=1) (qo : q.owner=2) (pt : p.token=1) (qt : q.token=2)
    (ps : sector ⟨w.accounts,p⟩) (qs : sector ⟨w.accounts,q⟩) (a b : Bool) :
    jointRows renewable w a b=(rows p.current a).flatMap fun l =>
      (rows q.current b).map fun r => (pairStep w p q a b l r,l.2*r.2) := by
  simp only [jointRows,nativeRows,hp,po,if_true,sector_rows _ ps,List.flatMap_map]
  apply congrArg (fun f => (rows p.current a).flatMap f)
  funext l
  have cell : (stepLocal w 1 p a l.1 l.2).carriers 2=some q := by
    simpa [hq] using mount_other w (advance renewable ⟨w.accounts,p⟩ a l.1 l.2) 1 2 (by decide)
  change ((nativeRows renewable (stepLocal w 1 p a l.1 l.2) 2 b).map _) = _
  simp only [nativeRows,cell,qo,if_true,sector_rows _ (other_sector w p q qs pt qt a l.1 l.2)]
  simp [pairStep,stepLocal,List.map_map,Function.comp_def]

theorem pair_frames (w : World) (p q : Local) (pt : p.token=1) (qt : q.token=2)
    (ps : sector ⟨w.accounts,p⟩) (qs : sector ⟨w.accounts,q⟩)
    (a b : Bool) (l r : State × Nat) :
    worldRuns (pairStep w p q a b l r)=some
      (FullInterface.advance (frame ⟨w.accounts,p⟩) l.1,
       FullInterface.advance (frame ⟨w.accounts,q⟩) r.1) := by
  have pc : w.accounts.charge 1=true := by simpa [pt] using ps.2.2
  have qc : w.accounts.charge 2=true := by simpa [qt] using qs.2.2
  simp [worldRuns,pairStep,stepLocal,mount,putOwner,frame,advance,transact,debit,put,
    FullInterface.advance,FullInterface.advanceContext,pt,qt,pc,qc,renewable,Nat.add_assoc]

theorem normalized_joint_projection (w : World) (siblings : Siblings w) (a : Bool × Bool) :
    (normalizedJointRows w a).map (fun e => (worldRuns e.1,e.2))=optionalRows (worldRuns w) a := by
  obtain ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ := siblings
  have pc : w.accounts.charge p.token=true := ps.2.2
  have qc : w.accounts.charge q.token=true := qs.2.2
  simp only [normalizedJointRows,raw_joint_rows w p q hp hq po qo pt qt ps qs,
    List.map_flatMap,List.map_map,Function.comp_def,pair_frames w p q pt qt ps qs,
    normalized_product_weight]
  simp [optionalRows,worldRuns,hp,hq,runProductRows,productRows,FullInterface.rows,
    pc,qc,rationalRows,model,List.map_flatMap,List.flatMap_map,List.map_map,
    Function.comp_def,frame]

theorem normalized_siblings_preserved (w : World) (siblings : Siblings w) (a : Bool × Bool)
    (e : World × Rat) (member : e∈normalizedJointRows w a) : Siblings e.1 := by
  obtain ⟨raw,member,eq⟩ := List.mem_map.mp member
  have same : raw.1=e.1 := congrArg Prod.fst eq
  rw [←same]
  exact (joint_preserves w siblings a.1 a.2 raw.1 raw.2 member).1

theorem optional_product_law (epoch : Anchor) (r : FullInterface.Run × FullInterface.Run)
    (word : List (Bool × Bool)) (trace : List (Observation × Observation)) :
    WeightedFuture.law optionalRows (fun r => r.map (pairObservation epoch)) (some r) word (trace.map some)=
      WeightedFuture.law runProductRows (pairObservation epoch) r word trace := by
  induction word generalizing r trace with
  | nil => cases trace <;> simp [WeightedFuture.law]
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons v tail =>
      simp only [WeightedFuture.law,List.map_cons,Option.map_some,Option.some.injEq]
      by_cases same : v=pairObservation epoch r
      · simp only [same,if_true,optionalRows,List.foldr_map]
        congr 1
        funext e acc
        rw [ih]
      · simp [same]

theorem world_joint_factorization (epoch : Anchor) (w : World) (p q : Local)
    (siblings : Siblings w) (hp : w.carriers 1=some p) (hq : w.carriers 2=some q)
    (word : List (Bool × Bool)) (trace : List (Observation × Observation)) :
    jointLaw epoch w word trace=
      WeightedFuture.law FullInterface.rows (fun r => FullInterface.observe (shiftRun epoch r))
        (frame ⟨w.accounts,p⟩) (word.map Prod.fst) (trace.map Prod.fst) *
      WeightedFuture.law FullInterface.rows (fun r => FullInterface.observe (shiftRun epoch r))
        (frame ⟨w.accounts,q⟩) (word.map Prod.snd) (trace.map Prod.snd) := by
  unfold jointLaw worldObservation
  rw [invariant_projection_law normalizedJointRows optionalRows worldRuns
    (fun r => r.map (pairObservation epoch)) Siblings normalized_joint_projection normalized_siblings_preserved
    w siblings]
  simp only [worldRuns,hp,hq]
  change WeightedFuture.law optionalRows (fun r => r.map (pairObservation epoch))
    (some (frame ⟨w.accounts,p⟩,frame ⟨w.accounts,q⟩)) word (trace.map some)=_
  rw [optional_product_law]
  exact product_future_law FullInterface.rows FullInterface.rows
    (fun r => FullInterface.observe (shiftRun epoch r)) (fun r => FullInterface.observe (shiftRun epoch r))
    (frame ⟨w.accounts,p⟩,frame ⟨w.accounts,q⟩) word trace

theorem actual_branch_factorization (epoch : Anchor) (w : World) (p q : Local)
    (hp : w.carriers 1=some p) (hq : w.carriers 2=some q)
    (po : p.owner=1) (qo : q.owner=2) (pt : p.token=1) (qt : q.token=2)
    (ps : sector ⟨w.accounts,p⟩) (qs : sector ⟨w.accounts,q⟩)
    (word : List (Bool × Bool)) (trace : List (Observation × Observation)) :
    jointLaw epoch w word trace=
      WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (shiftRun epoch (frame x)))
        ⟨w.accounts,p⟩ (word.map Prod.fst) (trace.map Prod.fst) *
      WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (shiftRun epoch (frame x)))
        ⟨w.accounts,q⟩ (word.map Prod.snd) (trace.map Prod.snd) := by
  rw [actual_frame_law (fun r => FullInterface.observe (shiftRun epoch r)) _ ps,
    actual_frame_law (fun r => FullInterface.observe (shiftRun epoch r)) _ qs]
  exact world_joint_factorization epoch w p q ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ hp hq word trace

theorem simultaneous_successors (w : World) (p q : Local)
    (hp : w.carriers 1=some p) (hq : w.carriers 2=some q)
    (po : p.owner=1) (qo : q.owner=2) (pt : p.token=1) (qt : q.token=2)
    (ps : sector ⟨w.accounts,p⟩) (qs : sector ⟨w.accounts,q⟩)
    (a b : Bool) (l r : State × Nat) (hl : l∈rows p.current a) (hr : r∈rows q.current b) :
    (pairStep w p q a b l r,l.2*r.2)∈jointRows renewable w a b ∧
    (pairStep w p q a b l r).carriers 1=some (advance renewable ⟨w.accounts,p⟩ a l.1 l.2).resident ∧
    (pairStep w p q a b l r).carriers 2=some (advance renewable ⟨w.accounts,q⟩ b r.1 r.2).resident ∧
    Siblings (pairStep w p q a b l r) := by
  have edge : (pairStep w p q a b l r,l.2*r.2)∈jointRows renewable w a b := by
    rw [raw_joint_rows w p q hp hq po qo pt qt ps qs]
    exact List.mem_flatMap.mpr ⟨l,hl,List.mem_map.mpr ⟨r,hr,rfl⟩⟩
  refine ⟨edge,?_,?_,(joint_preserves w ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ a b _ _ edge).1⟩
  · simp [pairStep,stepLocal,mount,putOwner]
  · simp [pairStep,stepLocal,mount,putOwner,advance,issued,transact,debit,put,pt,qt,renewable]

theorem historical_gluing (w : World) (history : Historical w) (p q : Local)
    (hp : w.carriers 1=some p) (hq : w.carriers 2=some q)
    (po : p.owner=1) (qo : q.owner=2) (pt : p.token=1) (qt : q.token=2)
    (ps : sector ⟨w.accounts,p⟩) (qs : sector ⟨w.accounts,q⟩)
    (a b : Bool) (l r : State × Nat) (hl : l∈rows p.current a) (hr : r∈rows q.current b) :
    Historical (pairStep w p q a b l r) := by
  have edge := (simultaneous_successors w p q hp hq po qo pt qt ps qs a b l r hl hr).1
  have positive := Nat.mul_pos ((rows_positive_normalized _ _).1 l hl).1 ((rows_positive_normalized _ _).1 r hr).1
  exact joint_history w _ [(a,b)] history (.step edge positive (.nil _))

theorem rectangular_trace_gluing (epoch : Anchor) (w : World) (p q : Local)
    (siblings : Siblings w) (hp : w.carriers 1=some p) (hq : w.carriers 2=some q)
    (word : List (Bool × Bool)) (trace : List (Observation × Observation))
    (left : 0<WeightedFuture.law FullInterface.rows (fun r => FullInterface.observe (shiftRun epoch r))
      (frame ⟨w.accounts,p⟩) (word.map Prod.fst) (trace.map Prod.fst))
    (right : 0<WeightedFuture.law FullInterface.rows (fun r => FullInterface.observe (shiftRun epoch r))
      (frame ⟨w.accounts,q⟩) (word.map Prod.snd) (trace.map Prod.snd)) : 0<jointLaw epoch w word trace := by
  rw [world_joint_factorization epoch w p q siblings hp hq]
  exact Rat.mul_pos left right

theorem physical_rows_mass (s : State) (act : Bool) :
    ((rationalRows model s act).map Prod.snd).sum=1 := by
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases act <;> decide +kernel

theorem run_rows_mass (r : FullInterface.Run) (charged : r.context.charge=true) (a : Bool) :
    ((FullInterface.rows r a).map Prod.snd).sum=1 := by
  simpa [FullInterface.rows,charged,List.map_map,Function.comp_def] using physical_rows_mass r.current a

theorem product_rows_mass (r s : FullInterface.Run) (rc : r.context.charge=true)
    (sc : s.context.charge=true) (a : Bool × Bool) :
    ((runProductRows (r,s) a).map Prod.snd).sum=1 := by
  simp only [runProductRows,productRows,List.sum,List.foldr_map,List.foldr_flatMap]
  rw [cartesian_product]
  have left := run_rows_mass r rc a.1
  have right := run_rows_mass s sc a.2
  simp only [List.sum,List.foldr_map] at left right
  rw [left,right]
  decide +kernel

theorem normalized_joint_mass (w : World) (h : Siblings w) (a : Bool × Bool) :
    ((normalizedJointRows w a).map Prod.snd).sum=1 := by
  have projected := congrArg (fun rs => (rs.map Prod.snd).sum) (normalized_joint_projection w h a)
  obtain ⟨p,q,hp,hq,po,qo,pt,qt,ps,qs⟩ := h
  have reduced : ((normalizedJointRows w a).map Prod.snd).sum=
      ((runProductRows (frame ⟨w.accounts,p⟩,frame ⟨w.accounts,q⟩) a).map Prod.snd).sum := by
    simpa [optionalRows,worldRuns,hp,hq,List.map_map,Function.comp_def] using projected
  rw [reduced]
  exact product_rows_mass _ _ ps.2.2 qs.2.2 a

end CSTTT.FullNative.JointFuture
