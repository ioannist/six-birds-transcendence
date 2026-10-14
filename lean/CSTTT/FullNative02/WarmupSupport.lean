import CSTTT.FullNative02.Reachability

namespace CSTTT.FullNative02
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

/-- Fixed six-edge cycle, alternating from the ACTUAL starting phase. -/
def cycleFrom (phase : Bool) : List FullNative.State :=
  [⟨false,false,true,false,!phase⟩,⟨false,true,true,false,phase⟩,
   ⟨false,false,false,false,!phase⟩,⟨false,false,true,false,phase⟩,
   ⟨false,true,true,false,!phase⟩,⟨false,false,false,false,phase⟩]

theorem cycle_from_initial_phase : cycleFrom false=sixCycle := rfl

/-- The preregistered seventh-step acquisition, never a phase reset. Native
requests must be present in the actual installed/owned support. -/
def outputWarmup (w : World) : Option World := do
  let r ← w.residents 3
  let next ← chooseNative renewable w 3 false ⟨false,false,false,false,!r.current.phase⟩
  runChoices renewable next 3 (cycleFrom (!r.current.phase))

def strongerFork (w : World) : Option (List (Settlement × Rat)) := do
  let divided ← partition w 3 4 5 [1] [2]
  let request ← requestFor divided 4 5 6 false false
  pure (fusionRows renewable divided request)

theorem every_main_output_warmup_supported :
    ∀ e∈fusionRows renewable branchesWorld mainRequest, (outputWarmup e.1.world).isSome=true := by
  decide +kernel

theorem every_mature_output_fork_supported :
    ∀ e∈fusionRows renewable branchesWorld mainRequest,
      ∀ v∈(outputWarmup e.1.world).toList,
        (strongerFork v).isSome=true ∧
          ∀ rows∈(strongerFork v).toList, rows≠[] ∧ (rows.map Prod.snd).sum=1 := by
  decide +kernel

theorem every_mature_output_readout :
    ∀ e∈fusionRows renewable branchesWorld mainRequest,
      ∀ v∈(outputWarmup e.1.world).toList,
        (v.residents 3).map (fun r => (r.installed,r.current,r.birth,r.receipts.length))=
          some (some .canonical32,⟨false,false,false,false,false⟩,.birth 24,7) ∧
        v.accounts.cursor 1=14 ∧ v.accounts.charge 1=true ∧
        ∀ r∈(v.residents 3).toList, ∀ receipt∈r.receipts,
          receipt.issuer=.local 3 ∧ receipt.owner=3 ∧ receipt.token=1 := by
  decide +kernel

theorem output_warmup_history (w v : World) (h : outputWarmup w=some v)
    (history : History renewable 8 .canonical32 w) : History renewable 8 .canonical32 v := by
  cases hr : w.residents 3 with
  | none => simp [outputWarmup,hr] at h
  | some r =>
    cases hc : chooseNative renewable w 3 false ⟨false,false,false,false,!r.current.phase⟩ with
    | none => simp [outputWarmup,hr,hc] at h
    | some next =>
      simp only [outputWarmup,hr,hc,Bind.bind,Option.bind] at h
      exact run_choices_history _ _ _ _ _ _ _ h
        (.next history (chosen_native_step _ _ _ _ _ _ hc))

end CSTTT.FullNative02
