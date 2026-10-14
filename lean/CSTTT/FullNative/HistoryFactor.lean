import CSTTT.FullNative.ActualBinding
namespace CSTTT.FullNative.FullInterface
open TargetTheory.GenericHandoff
set_option autoImplicit false

theorem observation_code_exact (r s : Run) : observe r=observe s ↔ code r=code s := by
  constructor
  · intro h
    have hp := congrArg TemporalFactorRules.Observation.predictive h
    have hm := congrArg (fun x => x.1) (Sum.inl.inj hp)
    have ho := congrArg TemporalFactorRules.Observation.order h
    have hr := congrArg TemporalFactorRules.Observation.record h
    have ht := congrArg TemporalFactorRules.Observation.residue h
    have hc := congrArg TemporalFactorRules.Observation.maintenance h
    have hw := congrArg TemporalFactorRules.Observation.owner h
    have ctx : r.context=s.context := by
      cases r with
      | mk r c =>
        cases s with
        | mk s d =>
          cases c
          cases d
          simp only [observe] at ho hr ht hc hw
          simp_all
    exact Prod.ext hm ctx
  · intro h
    have hp := (code_projection_exact r s).mp h
    calc
      observe r=observe (representative (project r)) := congrFun observation_projection r
      _=observe (representative (project s)) := congrArg (fun q => observe (representative q)) hp
      _=observe s := (congrFun observation_projection s).symm

theorem full_future_exact (r s : Run) :
    (∀ word trace, WeightedFuture.law rows observe r word trace=
      WeightedFuture.law rows observe s word trace) ↔ code r=code s := by
  constructor
  · intro laws
    have witness := laws [] [observe r]
    apply (observation_code_exact r s).mp
    by_cases h : observe r=observe s
    · exact h
    · simp [WeightedFuture.law,h] at witness
  · exact all_words r s
end CSTTT.FullNative.FullInterface
namespace CSTTT.FullNative.PhysicalExecution
set_option autoImplicit false

theorem actual_full_future_exact (x y : Execution) (hx : sector x) (hy : sector y) :
    (∀ word trace, WeightedFuture.law (normalizedRows AccountExecution.renewable)
        (fun x => FullInterface.observe (frame x)) x word trace=
      WeightedFuture.law (normalizedRows AccountExecution.renewable)
        (fun y => FullInterface.observe (frame y)) y word trace) ↔
    FullInterface.code (frame x)=FullInterface.code (frame y) := by
  have bridge : (∀ word trace, WeightedFuture.law (normalizedRows AccountExecution.renewable)
        (fun x => FullInterface.observe (frame x)) x word trace=
      WeightedFuture.law (normalizedRows AccountExecution.renewable)
        (fun y => FullInterface.observe (frame y)) y word trace) ↔
      (∀ word trace, WeightedFuture.law FullInterface.rows FullInterface.observe (frame x) word trace=
        WeightedFuture.law FullInterface.rows FullInterface.observe (frame y) word trace) := by
    constructor <;> intro h word trace
    · simpa only [actual_full_law x hx,actual_full_law y hy] using h word trace
    · simpa only [actual_full_law x hx,actual_full_law y hy] using h word trace
  exact bridge.trans (FullInterface.full_future_exact _ _)
theorem actual_history_split (x : Execution) (hx : sector x) :
    FullInterface.code (frame (Binding.splitExecution x false))≠
      FullInterface.code (frame (Binding.splitExecution x true)) ∧
    ¬ (∀ word trace, WeightedFuture.law (normalizedRows AccountExecution.renewable)
        (fun y => FullInterface.observe (frame y)) (Binding.splitExecution x false) word trace=
      WeightedFuture.law (normalizedRows AccountExecution.renewable)
        (fun y => FullInterface.observe (frame y)) (Binding.splitExecution x true) word trace) := by
  have codes : FullInterface.code (frame (Binding.splitExecution x false))≠
      FullInterface.code (frame (Binding.splitExecution x true)) := by
    intro eq
    exact (Binding.split_promotion x.resident.current).2 (congrArg Prod.fst eq)
  exact ⟨codes,fun laws => codes ((actual_full_future_exact _ _
    (Binding.actual_split_sectors x hx false) (Binding.actual_split_sectors x hx true)).mp laws)⟩

/-- The complete history coordinate also factors the joint continuation law. -/
theorem full_history_binding (x y : Execution) (hx : sector x) (hy : sector y)
    (same : FullInterface.code (frame x)=FullInterface.code (frame y))
    (word : List Bool) (outputs : List Nat) :
    Binding.emittedLaw (normalizedRows AccountExecution.renewable)
      (fun z => Binding.joint z.resident.current) x word outputs=
    Binding.emittedLaw (normalizedRows AccountExecution.renewable)
      (fun z => Binding.joint z.resident.current) y word outputs := by
  rw [Binding.actual_emitted_law _ x hx,Binding.actual_emitted_law _ y hy]
  exact Binding.joint_coherence _ _ (congrArg Prod.fst same) word outputs

end CSTTT.FullNative.PhysicalExecution
