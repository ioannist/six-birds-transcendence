import CSTTT.FullNative02.PhysicalPackage

namespace CSTTT.FullNative02.Temporal
open FullNative
set_option autoImplicit false

theorem observation_code_exact (r s : Run) : observe r=observe s ↔ code r=code s := by
  constructor
  · intro h
    rcases r with ⟨rs,⟨ro,rn,rr,rc,ra⟩⟩
    rcases s with ⟨ss,⟨so,sn,sr,sc,sa⟩⟩
    simp only [observe,Observation.mk.injEq] at h
    simp only [code,Prod.mk.injEq,Context.mk.injEq]
    exact ⟨h.1,h.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2⟩
  · intro same
    have projected := (code_projection_exact r s).mp same
    have equal := congrArg (fun q => observe (representative q)) projected
    simpa only [←congrFun observation_projection r,←congrFun observation_projection s] using equal

theorem option_all_words (r s : Run) (same : code r=code s) (word : List Bool)
    (trace : List (Option Observation)) :
    WeightedFuture.law rows (fun r => some (observe r)) r word trace=
      WeightedFuture.law rows (fun r => some (observe r)) s word trace := by
  have mapped : (fun r => some (observe r))=
      (fun r => some (observe (representative (project r)))) := by
    funext r
    exact congrArg some (congrFun observation_projection r)
  rw [mapped]
  exact WeightedFuture.equal_projection_all_words rows (fun q => some (observe (representative q)))
    project representative projected_rows r s ((code_projection_exact r s).mp same) word trace

theorem actual_full_future_exact (w v : World) (owner other : Nat) (r s : Resident) (key k : Token)
    (hw : access w owner=some (r,.canonical32,key))
    (hv : access v other=some (s,.canonical32,k)) :
    (∀ word trace,
      WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
        (fun w => (actual w owner).map observe) w word trace=
      WeightedFuture.law (fun w a => normalizedNative renewable w other a)
        (fun w => (actual w other).map observe) v word trace) ↔
      code (frame w r key)=code (frame v s k) := by
  constructor
  · intro laws
    have witness := laws [] [some (observe (frame w r key))]
    rw [actual_all_words _ _ _ _ hw,actual_all_words _ _ _ _ hv] at witness
    have equal : observe (frame w r key)=observe (frame v s k) := by
      by_cases h : observe (frame w r key)=observe (frame v s k)
      · exact h
      · simp [WeightedFuture.law,h] at witness
    exact (observation_code_exact _ _).mp equal
  · intro same word trace
    rw [actual_all_words _ _ _ _ hw,actual_all_words _ _ _ _ hv]
    exact option_all_words _ _ same word trace

/-- Both registered ROMs, all actual contexts and all words. The immutable ROM
is part of the typed birth residue, so differing generators are not conflated. -/
theorem actual_rom_full_future_exact (w v : World) (owner other : Nat) (r s : Resident)
    (rom otherROM : ROM) (key k : Token)
    (hw : binding w owner=some (r,rom,key)) (hv : binding v other=some (s,otherROM,k)) :
    (∀ word trace,
      WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
        (fun w => (actual w owner).map observe) w word trace=
      WeightedFuture.law (fun w a => normalizedNative renewable w other a)
        (fun w => (actual w other).map observe) v word trace) ↔
      code (frameROM w r rom key)=code (frameROM v s otherROM k) := by
  constructor
  · intro laws
    have witness := laws [] [some (observe (frameROM w r rom key))]
    rw [actual_rom_all_words _ _ _ _ _ hw,actual_rom_all_words _ _ _ _ _ hv] at witness
    have equal : observe (frameROM w r rom key)=observe (frameROM v s otherROM k) := by
      by_cases h : observe (frameROM w r rom key)=observe (frameROM v s otherROM k)
      · exact h
      · simp [WeightedFuture.law,h] at witness
    exact (observation_code_exact _ _).mp equal
  · intro same word trace
    rw [actual_rom_all_words _ _ _ _ _ hw,actual_rom_all_words _ _ _ _ _ hv]
    exact option_all_words _ _ same word trace

end CSTTT.FullNative02.Temporal
