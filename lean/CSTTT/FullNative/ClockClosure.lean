import CSTTT.FullNative.HistoryFactor
import CSTTT.FullNative.DriveClock

/-! G27: funded temporal progress for whole actual paths, not profile guards.
Renewable ports are consumed by native advances. Physical returns do not
return the execution, because its locally generated registers increase. -/
namespace CSTTT.FullNative.ClockClosure
open AccountExecution PhysicalExecution
set_option autoImplicit false

inductive Route : Execution → List Bool → Execution → Prop where
  | nil (x : Execution) : Route x [] x
  | cons {x y z : Execution} {a : Bool} {n : Nat} {word : List Bool}
      (edge : (y,n)∈rawRows renewable x a) (rest : Route y word z) : Route x (a::word) z

def tickAfter : List Bool → Bool → Bool
  | [],tick => tick
  | _::word,tick => tickAfter word (!tick)

theorem route_sector {x y : Execution} {word : List Bool} (path : Route x word y)
    (h : sector x) : sector y := by
  induction path with
  | nil => exact h
  | @cons x y z a n word edge rest ih =>
    have hy : sector y := by
      rw [sector_rows x h a] at edge
      obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
      have equal : y=advance renewable x a e.1 e.2 := (congrArg Prod.fst eq).symm
      rw [equal]
      exact sector_preserved x h a e.1 e.2
    exact ih hy

theorem route_registers {x y : Execution} {word : List Bool} (path : Route x word y)
    (h : sector x) :
    (frame y).context.order=(frame x).context.order+word.length ∧
    (frame y).context.localRecords=(frame x).context.localRecords+word.length ∧
    y.resident.current.phase=tickAfter word x.resident.current.phase ∧
    y.resident.owner=x.resident.owner ∧ y.resident.token=x.resident.token ∧
    y.resident.rootedRoute=x.resident.rootedRoute ∧
    y.accounts.portCursor x.resident.token=x.accounts.portCursor x.resident.token+word.length := by
  induction path with
  | nil => simp [tickAfter]
  | @cons x y z a n word edge rest ih =>
    have hy := route_sector (Route.cons edge (Route.nil y)) h
    have step := Credit.actual_clock_step x y h a n edge
    have same : y.resident.owner=x.resident.owner ∧ y.resident.token=x.resident.token ∧
        y.resident.rootedRoute=x.resident.rootedRoute := by
      rw [sector_rows x h a] at edge
      obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
      have equal : y=advance renewable x a e.1 e.2 := (congrArg Prod.fst eq).symm
      rw [equal]
      exact ⟨rfl,rfl,rfl⟩
    obtain ⟨order,records,phase,owner,token,root,cursor⟩ := ih hy
    refine ⟨?_,?_,?_,owner.trans same.1,token.trans same.2.1,root.trans same.2.2,?_⟩
    · rw [order,step.1,List.length_cons]; omega
    · rw [records,step.2.1,List.length_cons]; omega
    · rw [phase,step.2.2.1]; rfl
    · rw [←same.2.1,cursor,same.2.1,step.2.2.2.1,List.length_cons]; omega

theorem funded_row_nonempty (x : Execution) (h : sector x) (a : Bool) :
    rawRows renewable x a≠[] := by
  intro empty
  have mass := enabled_row_mass x h a
  simp [empty] at mass

theorem every_word_continues (x : Execution) (h : sector x) (word : List Bool) :
    ∃ y, Route x word y := by
  induction word generalizing x with
  | nil => exact ⟨x,.nil x⟩
  | cons a word ih =>
    have present := funded_row_nonempty x h a
    cases eq : rawRows renewable x a with
    | nil => exact (present eq).elim
    | cons e es =>
      have edge : (e.1,e.2)∈rawRows renewable x a := by rw [eq]; exact List.mem_cons_self
      have sector := route_sector (Route.cons edge (Route.nil e.1)) h
      obtain ⟨y,path⟩ := ih e.1 sector
      exact ⟨y,.cons edge path⟩

theorem maintained_words_continue (x : Execution) (h : sector x)
    (inside : x.resident.current.outside=false) (n : Nat) :
    ∃ y, Route x (List.replicate n false) y ∧ y.resident.current.outside=false := by
  induction n generalizing x with
  | zero => exact ⟨x,.nil x,inside⟩
  | succ n ih =>
    have edge := Binding.actual_split_supported x h false
    have sector := Binding.actual_split_sectors x h false
    obtain ⟨y,path,safe⟩ := ih (Binding.splitExecution x false) sector rfl
    exact ⟨y,.cons edge path,safe⟩

def firstReturn (x : Execution) : Execution :=
  advance renewable x false {x.resident.current with outside:=false,phase:= !x.resident.current.phase}
    (weight x.resident.current x.resident.current.u x.resident.current.v)
def secondReturn (x : Execution) : Execution := firstReturn (firstReturn x)

theorem physical_return_countertrace (x : Execution) (h : sector x)
    (inside : x.resident.current.outside=false) :
    Route x [false,false] (secondReturn x) ∧
    (secondReturn x).resident.current=x.resident.current ∧
    (frame (secondReturn x)).context.order=(frame x).context.order+2 ∧
    secondReturn x≠x := by
  have supported (s : State) :
      ({s with outside:=false,phase:= !s.phase},weight s s.u s.v)∈rows s false := by
    cases s with
    | mk p u v r phase =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel
  have edge (z : Execution) (hz : sector z) :
      (firstReturn z,weight z.resident.current z.resident.current.u z.resident.current.v)∈
      rawRows renewable z false := by
    rw [sector_rows z hz false]
    exact List.mem_map.mpr ⟨_,supported z.resident.current,rfl⟩
  have first := edge x h
  have sector := route_sector (Route.cons first (Route.nil _)) h
  have path : Route x [false,false] (secondReturn x) :=
    .cons first (.cons (edge _ sector) (.nil _))
  have order := (route_registers path h).1
  refine ⟨path,?_,order,?_⟩
  · cases x with
    | mk accounts resident =>
      cases resident with
      | mk owner token installed state receipts route base =>
        cases state with
        | mk p u v r phase =>
          simp only at inside
          subst p
          cases phase <;> rfl
  · intro equal
    rw [equal] at order
    simp at order

def orderBound : List Execution → Nat
  | [] => 0
  | x::xs => max (frame x).context.order (orderBound xs)

theorem order_bounded (xs : List Execution) (x : Execution) (member : x∈xs) :
    (frame x).context.order≤orderBound xs := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih tail) (Nat.le_max_right _ _)

/-- Physical stationarity cannot be repackaged as a finite maintained history
carrier: every nonempty finite funded support has a supported native exit. -/
theorem no_finite_closed_history_carrier (xs : List Execution) (present : xs≠[])
    (funded : ∀ x∈xs, sector x)
    (closed : ∀ x∈xs, ∀ y n, (y,n)∈rawRows renewable x false → y∈xs) : False := by
  obtain ⟨x,member⟩ := List.exists_mem_of_ne_nil xs present
  have paths (n : Nat) : ∃ y, y∈xs ∧ Route x (List.replicate n false) y := by
    induction n with
    | zero => exact ⟨x,member,.nil x⟩
    | succ n ih =>
      obtain ⟨y,mem,path⟩ := ih
      let z := Binding.splitExecution y false
      have edge := Binding.actual_split_supported y (funded y mem) false
      have append {r s t : Execution} {word : List Bool} (past : Route r word s)
          {weight : Nat} (next : (t,weight)∈rawRows renewable s false) : Route r (word++[false]) t := by
        induction past with
        | nil => exact .cons next (.nil t)
        | cons first rest ih => exact .cons first (ih next)
      refine ⟨z,closed y mem z _ edge,?_⟩
      have same : List.replicate n false++[false]=List.replicate (n+1) false := by
        simpa using (List.replicate_append_replicate (n:=n) (m:=1) (a:=false))
      rw [←same]
      exact append path edge
  obtain ⟨y,mem,path⟩ := paths (orderBound xs+1)
  have lower := (route_registers path (funded x member)).1
  have upper := order_bounded xs y mem
  simp only [List.length_replicate] at lower
  omega

end CSTTT.FullNative.ClockClosure
