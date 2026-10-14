import CSTTT.FullNative02.Epoch

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 32000000

theorem rom_physical_classes (rom : ROM) (s : State) : classes rom.program s=classFormula s := by
  cases rom
  · exact congrFun first_profile_equation s
  · rcases s with ⟨p,u,v,r,c⟩
    cases p <;> cases u <;> cases v <;> cases r <;> cases c <;> decide +kernel

theorem rom_projected_rows (rom : ROM) (s : State) (action : Bool) :
    (rationalRows rom.program s action).map (fun e => (eraseReplica e.1,e.2))=
      WeightedFuture.projectedRows (rationalRows rom.program) eraseReplica representative (eraseReplica s) action := by
  cases rom <;> cases action <;> rfl

end CSTTT.FullNative02
