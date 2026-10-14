import CSTTT.POS04.Assigned.C457
namespace CSTTT.POS04.Assigned

theorem c4_gate_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c4) a b) : C4Gate a tag ↔ C4Gate b tag := by
  unfold C4Gate
  rw [ready_locality h,extra_locality h]
theorem c4_acceptance_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c4) a b) : C4Accept a tag ↔ C4Accept b tag := by
  unfold C4Accept
  rw [c4_gate_locality h,extra_locality h]
theorem c5_gate_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c5) a b) : C5Gate a tag ↔ C5Gate b tag := ready_locality h
theorem c5_acceptance_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c5) a b) : C5Accept a tag ↔ C5Accept b tag := by
  unfold C5Accept
  rw [c5_gate_locality h,extra_locality h]
theorem c7_gate_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c7) a b) : C7Gate a tag ↔ C7Gate b tag := by
  unfold C7Gate
  rw [ready_locality h,extra_locality h]
theorem c7_acceptance_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c7) a b) : C7Accept a tag ↔ C7Accept b tag := by
  unfold C7Accept
  rw [c7_gate_locality h,extra_locality h]

def transportScope (c : Clause) := clauseScope .source c ++ clauseScope .target c

theorem transport_agrees {a b : Assignment} {c : Clause}
    (h : Agrees (transportScope c) a b) (tag : Tag) : Agrees (clauseScope tag c) a b := by
  intro k hk
  apply h k
  cases tag <;> simp [transportScope,hk]
theorem c5_transport_locality {a b : Assignment}
    (h : Agrees (transportScope .c5) a b) : C5Transport a ↔ C5Transport b := by
  unfold C5Transport
  rw [c5_gate_locality (transport_agrees h .source),
      c5_gate_locality (transport_agrees h .target),
      extra_locality (transport_agrees h .source),extra_locality (transport_agrees h .target)]
theorem c7_transport_locality {a b : Assignment}
    (h : Agrees (transportScope .c7) a b) : C7Transport a ↔ C7Transport b := by
  unfold C7Transport
  rw [c7_gate_locality (transport_agrees h .source),
      c7_gate_locality (transport_agrees h .target),
      extra_locality (transport_agrees h .source),extra_locality (transport_agrees h .target)]
theorem future_references_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c6) a b) :
    FutureReferenceGate a tag ↔ FutureReferenceGate b tag := by
  unfold FutureReferenceGate
  rw [complete_locality h,extra_locality h]

end CSTTT.POS04.Assigned
