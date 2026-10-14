import CSTTT.Targets.GenericHandoff.NativeComposition.MiddleTrace

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
open RegisterInterpreter ModeExecution EpisodeMap CSTTT.TransportTheory

def clearHidden (x : Frame.State) : Frame.State :=
  {x with factor := (x.factor.1,x.factor.2.1,false)}
def brokenTranslation : (k : Unit) → Expr Owner MemoryValue Unit (fun _ => Frame.State) Unit Frame.State :=
  fun k => .map clearHidden (translation k)

theorem broken_ready : RegisterSubstitution.Ready brokenTranslation nativeAssignment := by
  intro r k hk
  exact map_ready r k hk

theorem broken_on_closure (x : Frame.Registers) (hx : SourceClosure x) :
    RegisterSubstitution.translate brokenTranslation nativeAssignment broken_ready x ()=
      Frame.pack (clearHidden (shifted (x ()))) := by
  funext r
  have he := RegisterSubstitution.translation_equation brokenTranslation nativeAssignment broken_ready x () r
  have ht := RegisterSubstitution.translation_equation translation nativeAssignment map_ready x () r
  rw [translation_on_closure x hx] at ht
  change (translation r).eval nativeAssignment x ()=some (shifted (x ())) at ht
  change ((translation r).eval nativeAssignment x ()).map clearHidden=some _ at he
  rw [ht] at he
  exact (Option.some.inj he).symm

theorem anchor_in_closure : SourceClosure (sourceRoot (false,false,false)) :=
  FutureClosure.root _ (List.mem_map.mpr ⟨(false,false,false),factor_mem _,rfl⟩)

theorem broken_agrees_at_anchor :
    RegisterSubstitution.translate brokenTranslation nativeAssignment broken_ready (sourceRoot (false,false,false)) ()=
      translate (sourceRoot (false,false,false)) := by
  rw [broken_on_closure _ anchor_in_closure]
  change Frame.pack (clearHidden (shifted (sourceRoot (false,false,false) ())))=
    RegisterSubstitution.translate translation nativeAssignment map_ready (sourceRoot (false,false,false)) ()
  rw [translation_on_closure _ anchor_in_closure,source_root]
  rfl

theorem hidden_successor_has_zero_weight :
    RegisterFuture.weight source nativeAssignment source_ready (sourceRoot (false,false,false))
      ((),false) (false,false,true)=0 := by
  simp [RegisterFuture.weight,source_row,source_root,middleState,Frame.pack,destination]
  decide +kernel

/-- Direct successor-transport refutation. The changed branch has zero
weight but belongs to the actual declared future closure. -/
theorem broken_successor_transport_rejected :
    ¬ ∀ x : Frame.Registers, SourceClosure x → ∀ da : Unit × Bool, ∀ o : Factor,
      RegisterSubstitution.translate brokenTranslation nativeAssignment broken_ready
        (RegisterFuture.next source nativeAssignment source_ready x da o) () =
      RegisterFuture.next target nativeAssignment target_ready
        (RegisterSubstitution.translate brokenTranslation nativeAssignment broken_ready x ()) da o := by
  intro h
  have hn : SourceClosure (RegisterFuture.next source nativeAssignment source_ready
      (sourceRoot (false,false,false)) ((),false) (false,false,true)) :=
    FutureClosure.step anchor_in_closure ((),false) (false,false,true) (factor_mem _)
  have he := h _ anchor_in_closure ((),false) (false,false,true)
  rw [broken_on_closure _ hn,broken_on_closure _ anchor_in_closure,source_next,target_next,source_root] at he
  have hf := congrArg (fun x : Frame.Registers => (x ()).factor) he
  change (false,false,false)=(false,false,true) at hf
  contradiction

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
