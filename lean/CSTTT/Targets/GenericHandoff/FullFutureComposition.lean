import CSTTT.Transport.FullFuture

/-! Heterogeneous whole-future composition from one-step interpreted laws.
State and observation types may change at each handoff. Outcomes and actions
share declared coordinates; outcome lists must agree literally. Closure covers
every declared outcome, including those whose weight is zero. -/
namespace CSTTT.TargetTheory.GenericHandoff.FullFutureComposition
open CSTTT.TransportTheory

variable {S T U A O CS CT CU VS VT VU : Type}

structure Laws (source : FullFutureModel S A O CS VS)
    (target : FullFutureModel T A O CT VT) (closed : S → Prop)
    (translate : S → T) (image : VS → VT) : Prop where
  outcomes : target.outcomes=source.outcomes
  imageInjective : Function.Injective image
  closedNext : ∀ x, closed x → ∀ a o, o ∈ source.outcomes → closed (source.next x a o)
  observation : ∀ x, closed x → target.observe (translate x)=image (source.observe x)
  weight : ∀ x, closed x → ∀ a o, target.weight (translate x) a o=source.weight x a o
  next : ∀ x, closed x → ∀ a o, target.next (translate x) a o=translate (source.next x a o)

theorem all_words [DecidableEq VS] [DecidableEq VT]
    (source : FullFutureModel S A O CS VS) (target : FullFutureModel T A O CT VT)
    (closed : S → Prop) (translate : S → T) (image : VS → VT)
    (laws : Laws source target closed translate image)
    (x : S) (hx : closed x) (word : List A) (trace : List VS) :
    fullFuture target (translate x) word (trace.map image)=fullFuture source x word trace := by
  induction word generalizing x trace with
  | nil =>
    simp only [fullFuture,laws.observation x hx]
    have hi : trace.map image=[image (source.observe x)] ↔ trace=[source.observe x] := by
      simpa only [List.map_cons,List.map_nil] using
        (List.map_inj_right (l := trace) (l' := [source.observe x])
          (fun _ _ h => laws.imageInjective h))
    simp only [hi]
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      have hi : image first=image (source.observe x) ↔ first=source.observe x :=
        ⟨fun h => laws.imageInjective h,congrArg image⟩
      simp only [List.map_cons,fullFuture,laws.observation x hx,hi]
      by_cases hf : first=source.observe x
      · simp only [hf,ite_true,laws.outcomes]
        apply congrArg List.sum
        apply List.map_congr_left
        intro o ho
        rw [laws.weight x hx,laws.next x hx,ih _ (laws.closedNext x hx a o ho)]
      · simp only [hf,ite_false]

/-- The composite map is constructed. Its one-step laws use the independently
checked full middle model, rather than a desired composed trace equality. -/
theorem compose
    (source : FullFutureModel S A O CS VS) (middle : FullFutureModel T A O CT VT)
    (target : FullFutureModel U A O CU VU) (firstClosed : S → Prop) (secondClosed : T → Prop)
    (first : S → T) (second : T → U) (firstImage : VS → VT) (secondImage : VT → VU)
    (left : Laws source middle firstClosed first firstImage)
    (right : Laws middle target secondClosed second secondImage)
    (seam : ∀ x, firstClosed x → secondClosed (first x)) :
    Laws source target firstClosed (second ∘ first) (secondImage ∘ firstImage) := by
  refine ⟨right.outcomes.trans left.outcomes,
    right.imageInjective.comp left.imageInjective,left.closedNext,?_,?_,?_⟩
  · intro x hx
    simp only [Function.comp_def,right.observation _ (seam x hx),left.observation x hx]
  · intro x hx a o
    exact (right.weight _ (seam x hx) a o).trans (left.weight x hx a o)
  · intro x hx a o
    simp only [Function.comp_def,right.next _ (seam x hx),left.next x hx]

theorem composed_all_words [DecidableEq VS] [DecidableEq VU]
    (source : FullFutureModel S A O CS VS) (middle : FullFutureModel T A O CT VT)
    (target : FullFutureModel U A O CU VU) (firstClosed : S → Prop) (secondClosed : T → Prop)
    (first : S → T) (second : T → U) (firstImage : VS → VT) (secondImage : VT → VU)
    (left : Laws source middle firstClosed first firstImage)
    (right : Laws middle target secondClosed second secondImage)
    (seam : ∀ x, firstClosed x → secondClosed (first x))
    (x : S) (hx : firstClosed x) (word : List A) (trace : List VS) :
    fullFuture target (second (first x)) word (trace.map (secondImage ∘ firstImage))=
      fullFuture source x word trace :=
  all_words source target firstClosed (second ∘ first) (secondImage ∘ firstImage)
    (compose source middle target firstClosed secondClosed first second firstImage secondImage left right seam)
    x hx word trace

end CSTTT.TargetTheory.GenericHandoff.FullFutureComposition
