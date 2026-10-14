import CSTTT.Corridor.RawDirectSuccessor
namespace CSTTT.CorridorTheory.GlobalTokenUse
open CSTTT.CorridorTheory.RawDirectSuccessor

theorem actual_fire_state (raw : Raw) (a : Assignment) (d : Delivered) (next : Assignment)
    (fired : fire raw a=some (d,next)) : next=consumeToken d.consumedToken.id a := by
  unfold fire at fired
  cases hg : generated raw a with
  | nil => simp [hg] at fired
  | cons first rest =>
    cases rest with
    | nil =>
      simp [hg] at fired
      obtain ⟨hd,hn⟩ := fired
      subst d
      exact hn.symm
    | cons other tail => simp [hg] at fired

theorem actual_fire_refutes_every_token_alias (firingRaw receivingRaw : Raw)
    (a : Assignment) (d : Delivered) (next : Assignment) (edge : Edge)
    (input : SourceEvent) (token : Token)
    (fired : fire firingRaw a=some (d,next))
    (assigned : a edge.parent=some input) (identity : input.token=some token)
    (sameToken : token.id=d.consumedToken.id) : emit receivingRaw next edge=none := by
  rw [actual_fire_state firingRaw a d next fired]
  exact consumed_token_alias_emit receivingRaw a edge input token d.consumedToken.id
    assigned identity sameToken

end CSTTT.CorridorTheory.GlobalTokenUse
