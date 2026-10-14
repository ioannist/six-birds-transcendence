import CSTTT.FullNative.PhysicalFuture

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 8000000

inductive ROM where
  | canonical32 | flat32
  deriving DecidableEq, Repr

def ROM.program : ROM → Model
  | .canonical32 => model
  | .flat32 => flatten model

theorem canonical_projection (s : State) (a : Bool) :
    ROM.canonical32.program.rows s a = model.rows s a := rfl

theorem flat_projection (s : State) (a : Bool) :
    ROM.flat32.program.rows s a = (flatten model).rows s a := rfl

theorem rom_rows_positive_normalized (rom : ROM) (s : State) (a : Bool) :
    (∀ e ∈ rom.program.rows s a, 0 < e.2) ∧
    ((rom.program.rows s a).map Prod.snd).sum = 16 := by
  cases rom
  · exact ⟨fun e h => ((rows_positive_normalized s a).1 e h).1,
      (rows_positive_normalized s a).2⟩
  · rcases s with ⟨p,u,v,r,c⟩
    cases p <;> cases u <;> cases v <;> cases r <;> cases c <;> cases a <;> decide +kernel

end CSTTT.FullNative02
