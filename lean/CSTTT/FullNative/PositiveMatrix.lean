import CSTTT.Targets.GenericHandoff.ObjecthoodRules
namespace CSTTT.FullNative.PositiveMatrix
open CSTTT.TargetTheory.GenericHandoff.FixedPointVerifier
set_option autoImplicit false
variable {X : Type}

theorem mass_scale (xs : List X) (r : Rat) (f : X → Rat) :
    mass xs (fun x => r*f x) = r*mass xs f := by
  induction xs with
  | nil => simp [mass] <;> grind
  | cons x xs ih => simp only [mass,List.map_cons,List.sum_cons] at *; grind

theorem nonpositive_sum (xs : List X) (f : X → Rat) (h : ∀ x ∈ xs, f x ≤ 0) :
    mass xs f ≤ 0 := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [mass,List.map_cons,List.sum_cons] at *
    grind

theorem zero_sum_nonpositive (xs : List X) (f : X → Rat)
    (h : ∀ x ∈ xs, f x ≤ 0) (zero : mass xs f = 0) : ∀ x ∈ xs, f x = 0 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy := h y (by simp)
    have hys : ∀ x ∈ ys, f x ≤ 0 := by intro x hx; exact h x (by simp [hx])
    have hs := nonpositive_sum ys f hys
    have hz : f y=0 ∧ mass ys f=0 := by
      change f y+mass ys f=0 at zero
      grind
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hz.1
    · exact ih hys hz.2 x hx

theorem finite_maximum (xs : List X) (nonempty : xs≠[]) (f : X → Rat) :
    ∃ t ∈ xs, ∀ s ∈ xs, f s≤f t := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    by_cases empty : ys=[]
    · subst ys
      refine ⟨y,by simp,?_⟩
      intro s hs
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      subst s
      exact Rat.le_refl
    · obtain ⟨t,ht,dom⟩ := ih empty
      rcases (Rat.le_total (a := f y) (b := f t)) with h | h
      · refine ⟨t,by simp [ht],?_⟩
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact h
        · exact dom s hs
      · refine ⟨y,by simp,?_⟩
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact Rat.le_refl
        · exact Rat.le_trans (dom s hs) h

theorem positive_stationary_unique (xs : List X) (nonempty : xs≠[])
    (cover : ∀ x, x∈xs) (P : Matrix X) (π x : Vector X)
    (positive : ∀ s t, 0<P s t) (πpositive : ∀ s, 0<π s)
    (πmass : mass xs π=1) (xmass : mass xs x=1)
    (πfixed : Fixed xs P π) (xfixed : Fixed xs P x) : x=π := by
  obtain ⟨t,ht,dom⟩ := finite_maximum xs nonempty (fun s => x s/π s)
  let r := x t/π t
  have rt : x t/π t=r := rfl
  have dominates : ∀ s, x s/π s ≤ r := by
    intro s
    exact dom s (cover s)
  let δ := fun s => x s-r*π s
  have nonpos : ∀ s, δ s≤0 := by
    intro s
    have h := Rat.mul_le_mul_of_nonneg_right (dominates s) (Rat.le_of_lt (πpositive s))
    rw [Rat.div_mul_cancel (Rat.ne_of_gt (πpositive s))] at h
    change x s-r*π s≤0
    grind
  have atmax : δ t=0 := by
    have h := congrArg (fun q => q*π t) rt
    dsimp only at h
    rw [Rat.div_mul_cancel (Rat.ne_of_gt (πpositive t))] at h
    change x t-r*π t=0
    grind
  have δfixed : mass xs (fun s => δ s*P s t)=δ t := by
    have hp := πfixed t
    have hx := xfixed t
    have sub := dot_sub xs (fun s => x s) (fun s => r*π s) (fun s => P s t)
    have scale := dot_scale xs r π (fun s => P s t)
    have hp' : mass xs (fun s => π s*P s t)=π t := by
      simpa only [dot,mass,Rat.mul_comm] using hp
    have hx' : mass xs (fun s => x s*P s t)=x t := by
      simpa only [dot,mass,Rat.mul_comm] using hx
    simp only [dot] at sub scale
    change (xs.map (fun s => (x s-r*π s)*P s t)).sum=x t-r*π t
    rw [sub,scale]
    change mass xs (fun s => x s*P s t)-r*mass xs (fun s => π s*P s t)=x t-r*π t
    rw [hx',hp']
  have products_nonpos : ∀ s ∈ xs, δ s*P s t ≤ 0 := by
    intro s hs
    have h := Rat.mul_le_mul_of_nonneg_right (nonpos s) (Rat.le_of_lt (positive s t))
    simpa using h
  have products_zero := zero_sum_nonpositive xs (fun s => δ s*P s t) products_nonpos
    (δfixed.trans atmax)
  have scaled : x = fun s => r*π s := by
    funext s
    have h := products_zero s (cover s)
    have hn := Rat.ne_of_gt (positive s t)
    have hd : δ s=0 := by grind
    change x s-r*π s=0 at hd
    grind
  have hr : r=1 := by
    rw [scaled,mass_scale,πmass] at xmass
    grind
  rw [scaled,hr]
  simp

theorem mass_zero (xs : List X) : mass xs (fun _ => 0)=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change 0+mass xs (fun _ => 0)=0; rw [ih]; grind

theorem mass_add (xs : List X) (f g : X → Rat) :
    mass xs (fun x => f x+g x) = mass xs f+mass xs g := by
  induction xs with
  | nil => change (0:Rat)=0+0; grind
  | cons x xs ih => simp only [mass,List.map_cons,List.sum_cons] at *; grind

theorem sum_swap {Y : Type} (xs : List X) (ys : List Y) (f : X → Y → Rat) :
    mass xs (fun x => mass ys (f x)) = mass ys (fun y => mass xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    change 0=mass ys (fun _ => 0)
    exact (mass_zero ys).symm
  | cons x xs ih =>
    change mass ys (f x)+mass xs (fun x => mass ys (f x)) =
      mass ys (fun y => f x y+mass xs (fun x => f x y))
    rw [ih]
    exact (mass_add ys (f x) (fun y => mass xs (fun x => f x y))).symm

theorem mass_mul (xs : List X) (r : Rat) (f : X → Rat) :
    mass xs (fun x => f x*r) = mass xs f*r := by
  simpa only [Rat.mul_comm] using mass_scale xs r f

theorem fixed_product [DecidableEq X] (xs : List X) (P Q : Matrix X) (π : Vector X)
    (hp : Fixed xs P π) (hq : Fixed xs Q π) :
    Fixed xs (CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules.product xs P Q) π := by
  intro t
  change mass xs (fun s => mass xs (fun k => P s k*Q k t)*π s)=π t
  have inner : ∀ s, mass xs (fun k => P s k*Q k t)*π s =
      mass xs (fun k => P s k*Q k t*π s) := by
    intro s
    exact (mass_mul xs (π s) (fun k => P s k*Q k t)).symm
  simp only [inner]
  rw [sum_swap]
  have reorder : ∀ k, mass xs (fun s => P s k*Q k t*π s) =
      mass xs (fun s => P s k*π s)*Q k t := by
    intro k
    have eq : (fun s => P s k*Q k t*π s) = (fun s => (P s k*π s)*Q k t) := by
      funext s
      grind
    rw [eq,mass_mul]
  simp only [reorder]
  have hp' : ∀ k, mass xs (fun s => P s k*π s)=π k := hp
  simp only [hp']
  have hq' : mass xs (fun k => Q k t*π k)=π t := hq t
  simpa only [Rat.mul_comm] using hq'

theorem product_identity_left [DecidableEq X] (xs : List X) (nodup : xs.Nodup)
    (cover : ∀ x, x∈xs) (P : Matrix X) :
    CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules.product xs identity P = P := by
  funext s t
  exact (dot_indicator xs nodup s (fun k => P k t)).trans (by simp [cover])

theorem fixed_identity [DecidableEq X] (xs : List X) (nodup : xs.Nodup)
    (cover : ∀ x, x∈xs) (π : Vector X) : Fixed xs identity π := by
  intro t
  have h := dot_indicator xs nodup t π
  simpa only [cover t,if_true,identity,eq_comm] using h

theorem fixed_power [DecidableEq X] (xs : List X) (nodup : xs.Nodup)
    (cover : ∀ x, x∈xs) (P : Matrix X) (π : Vector X)
    (h : Fixed xs P π) (n : Nat) :
    Fixed xs (CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules.power xs P n) π := by
  induction n with
  | zero => exact fixed_identity xs nodup cover π
  | succ n ih => exact fixed_product xs _ P π ih h

theorem product_assoc (xs : List X) (A B C : Matrix X) :
    CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules.product xs
      (CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules.product xs A B) C =
    CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules.product xs A
      (CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules.product xs B C) := by
  funext s t
  change mass xs (fun k => mass xs (fun j => A s j*B j k)*C k t) =
    mass xs (fun j => A s j*mass xs (fun k => B j k*C k t))
  have distribute : ∀ k, mass xs (fun j => A s j*B j k)*C k t =
      mass xs (fun j => A s j*B j k*C k t) := by
    intro k
    exact (mass_mul xs (C k t) (fun j => A s j*B j k)).symm
  simp only [distribute]
  rw [sum_swap]
  congr 1
  funext j
  have assoc : (fun k => A s j*B j k*C k t) = (fun k => A s j*(B j k*C k t)) := by
    funext k
    grind
  rw [assoc,mass_scale]

theorem nonnegative_sum (xs : List X) (f : X → Rat) (h : ∀ x∈xs, 0≤f x) :
    0≤mass xs f := by
  induction xs with
  | nil => exact Rat.le_refl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (by intro x hx; exact h x (by simp [hx]))
    change 0≤f x+mass xs f
    grind

theorem positive_sum (xs : List X) (f : X → Rat) (h : ∀ x∈xs, 0≤f x)
    (t : X) (mem : t∈xs) (pos : 0<f t) : 0<mass xs f := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    have hx := h x (by simp)
    have hn : ∀ x∈xs, 0≤f x := by intro x hx; exact h x (by simp [hx])
    change 0<f x+mass xs f
    rcases List.mem_cons.mp mem with rfl | mem
    · have hr := nonnegative_sum xs f hn
      grind
    · have hr := ih hn mem
      grind

theorem positive_product (xs : List X) (cover : ∀ x, x∈xs) (A B : Matrix X)
    (ap : ∀ s t, 0<A s t) (bn : ∀ s t, 0≤B s t) (bp : ∀ t, 0<B t t) :
    ∀ s t, 0<CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules.product xs A B s t := by
  intro s t
  apply positive_sum xs (fun k => A s k*B k t) _ t (cover t) (Rat.mul_pos (ap s t) (bp t))
  intro k hk
  have h := Rat.mul_le_mul_of_nonneg_left (bn k t) (Rat.le_of_lt (ap s k))
  simpa using h

def push (xs : List X) (P : Matrix X) (π : Vector X) : Vector X :=
  fun t => dot xs (fun s => P s t) π

theorem push_product (xs : List X) (P Q : Matrix X) (π : Vector X) :
    push xs (CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules.product xs P Q) π =
      push xs Q (push xs P π) := by
  funext t
  change mass xs (fun s => mass xs (fun k => P s k*Q k t)*π s)=
    mass xs (fun k => Q k t*mass xs (fun s => P s k*π s))
  have inner : ∀ s, mass xs (fun k => P s k*Q k t)*π s =
      mass xs (fun k => P s k*Q k t*π s) := by
    intro s
    exact (mass_mul xs (π s) (fun k => P s k*Q k t)).symm
  simp only [inner]
  rw [sum_swap]
  congr 1
  funext k
  have eq : (fun s => P s k*Q k t*π s) = (fun s => Q k t*(P s k*π s)) := by
    funext s
    grind
  rw [eq,mass_scale]
end CSTTT.FullNative.PositiveMatrix
