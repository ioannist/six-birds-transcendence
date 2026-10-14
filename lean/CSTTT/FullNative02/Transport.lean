import CSTTT.FullNative02.FissionLaws
import CSTTT.FullNative02.ActualFusion

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false

/-- Relative parent times are separate labeled offsets, computed from each
paid local history. No maximum, mean, shared epoch or owner equality is used. -/
def transportedOrders (r : Resident) : List (Node × Nat) :=
  r.roots.map fun root => (root.1,root.2+r.receipts.length)

theorem native_transport_commutes (supply : Supply) (w : World) (owner : Nat)
    (r : Resident) (rom : ROM) (key : Token) (a : Bool) (edge : State × Nat) :
    ((advance supply w owner r rom key a edge).residents owner).map transportedOrders =
      some ((transportedOrders r).map (fun root => (root.1,root.2+1))) := by
  simp [advance,put,transportedOrders,List.map_map,Nat.add_assoc]

theorem fusion_two_transports (supply : Supply) (w : World) (q : FusionRequest)
    (p : Parents) (pair : Pair) (probability : Rat) :
    ((settle supply w q p pair probability).world.residents q.output).map transportedOrders=
      some [(.version w.events.length,p.left.receipts.length+1),
        (.version (w.events.length+1),p.right.receipts.length+1)] := by
  simp [settle,put,transportedOrders]

theorem fusion_native_future_at_advanced_states (rom : ROM) (s t : State) (a b : Bool)
    (pair : Pair) (member : pair∈meeting rom s t a b) (observe : State → Nat)
    (word : List Bool) (trace : List Nat) :
    WeightedFuture.law (rationalRows rom.program) observe pair.1.state word trace=
      WeightedFuture.law (rationalRows rom.program) observe pair.2.state word trace := by
  rw [(meeting_support rom s t a b pair member).2.2]

theorem source_capture_anchor :
    (readCapture sourceWorld 0).map (fun c => (c.serial,c.order,c.count,c.sourceVersion))=
      some (20,6,6,.version 6) := by decide +kernel

theorem actual_fusion_parent_offsets :
    (fused.residents 3).map transportedOrders=some [(.version 22,7),(.version 23,7)] := by
  decide +kernel

end CSTTT.FullNative02
