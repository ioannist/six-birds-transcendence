import CSTTT.Fallback.ExecutableSeed

namespace CSTTT.FallbackTheory.CachedSeed
open CSTTT.FallbackTheory.ExecutableSeed
open CSTTT.FallbackTheory.FiniteClosure
open CSTTT.FallbackTheory.FiniteHorn
open CSTTT.FallbackTheory.SharedOperationalSeed
open CSTTT.FallbackTheory.RawPredictiveQuotient
open CSTTT.FallbackTheory.OperationalTrace
open CSTTT.TransportTheory
variable {A : Type} [DecidableEq A]
-- Class (b): optional actual cache lookup never defaults a missing stored bit.
def lookup (key : A) : List (A × Bool) → Option Bool
  | [] => none
  | (node,value)::rest => if node=key then some value else lookup key rest
-- Class (b): an actually generated complete cache contains exactly the computed input bit at every address, including duplicates.
theorem lookup_map_exact (key : A) (nodes : List A) (bits : A → Bool) (member : key∈nodes) :
    lookup key (nodes.map (fun node => (node,bits node)))=some (bits key) := by
  induction nodes with
  | nil => simp at member
  | cons first rest ih =>
    by_cases equal : first=key
    · subst first; simp [lookup]
    · have tail : key∈rest := (List.mem_cons.mp member).resolve_left (Ne.symm equal)
      simpa [lookup,equal] using ih tail
-- Class (b): a derived finite table stores actual computed bits with proved lookup presence, not a function waiting to rebuild a table.
structure Cache (A : Type) [DecidableEq A] where
  values : List (A × Bool)
  complete : ∀ key,(lookup key values).isSome
-- Class (b): cache queries consume the stored table using proof-backed Option.get, never a missing-value fallback.
def readCache (cache : Cache A) (key : A) : Bool :=
  (lookup key cache.values).get (cache.complete key)
-- Class (b): actual per-step cache construction computes every bit into a finite stored list before queries occur.
def makeCache (nodes : CSTTT.FiniteEnum A) (bits : A → Bool) : Cache A where
  values := nodes.elems.map (fun node => (node,bits node))
  complete := by
    intro key
    rw [lookup_map_exact key nodes.elems bits (nodes.complete key)]
    rfl
-- Class (b): every stored generated cache returns exactly its input bit function, including duplicate raw nodes.
theorem read_cache_exact (nodes : CSTTT.FiniteEnum A) (bits : A → Bool) : readCache (makeCache nodes bits)=bits := by
  funext key
  unfold readCache makeCache
  simp [lookup_map_exact key nodes.elems bits (nodes.complete key)]
-- Class (b): actual finite iteration returns realized data tables; its recursive predecessor is a stored table, not a recursive query closure.
def iterateCache (nodes : CSTTT.FiniteEnum A) (next : (A → Bool) → A → Bool) (seed : A → Bool) : Nat → Cache A
  | 0 => makeCache nodes seed
  | n+1 =>
      let previous := iterateCache nodes next seed n
      makeCache nodes (next (readCache previous))
-- Class (b): all raw operators/seeds/bounds have exact stored-table/original iteration correspondence, without shortened horizons.
theorem cache_iterate_exact (nodes : CSTTT.FiniteEnum A) (next : (A → Bool) → A → Bool) (seed : A → Bool) :
    ∀ n,readCache (iterateCache nodes next seed n)=iterate next seed n := by
  intro n
  induction n with
  | zero => exact read_cache_exact nodes seed
  | succ n ih => simp only [iterateCache,read_cache_exact,ih,iterate]
-- Class (b): runtime path classification uses the same derived frame/edges/rules and exact bound, with actual table storage.
def pathBit (edges : List (Nat × Nat)) (source target : Nat) : Bool :=
  let frame := graphEnum edges source target
  let nodes := pairEnum frame
  let graph := graphEdges edges source target
  let table := iterateCache nodes (gamma (edgeSeed graph) (transRules frame) (fun _ => true)) (edgeSeed graph) nodes.elems.length
  readCache table (⟨source,by simp [graphAddresses]⟩,⟨target,by simp [graphAddresses]⟩)
-- Class (b): actual stored-table path bit equals the original exact bit on every finite raw graph/endpoints.
theorem path_bit_eq (edges : List (Nat × Nat)) (source target : Nat) :
    pathBit edges source target=CSTTT.FallbackTheory.ExecutableSeed.pathBit edges source target := by
  simp only [pathBit,cache_iterate_exact,CSTTT.FallbackTheory.ExecutableSeed.pathBit,reachable,ancestry,closure]
-- Class (b): all-input positive-length operational Path exactness is preserved by the realized table backend.
theorem path_bit_exact (edges : List (Nat × Nat)) (source target : Nat) : pathBit edges source target=true ↔ Path edges source target := by
  rw [path_bit_eq]
  exact CSTTT.FallbackTheory.ExecutableSeed.path_bit_exact edges source target
variable {H S T E R SC TC RR M : Type} [DecidableEq S]
-- Class (b): optional table-cached Seed consumes actual same checked readouts with no missing-value defaults.
def seedDecision (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T) (source target : Nat) : Option Bool := do
  let (original,decoded,edges) ← readAt inputs source target
  some (pathBit edges source target && decide (sourceSignature b (classQueries b) original=targetSignature b (classQueries b) decoded))
-- Class (b): the stored-table implementation preserves every original tri-state outcome for every partial shared raw input.
theorem seed_decision_eq (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T) (source target : Nat) :
    seedDecision b inputs source target=CSTTT.FallbackTheory.ExecutableSeed.seedDecision b inputs source target := by
  cases read : readAt inputs source target with
  | none => simp [seedDecision,CSTTT.FallbackTheory.ExecutableSeed.seedDecision,read]
  | some value =>
    obtain ⟨original,decoded,edges⟩ := value
    simp [seedDecision,CSTTT.FallbackTheory.ExecutableSeed.seedDecision,read,path_bit_eq]
-- Class (b): exact every-partial shared Seed iff remains unconditional in the stored-table implementation.
theorem seed_decision_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T) (source target : Nat) :
    seedDecision b inputs source target=some true ↔ Seed b inputs source target := by
  rw [seed_decision_eq]
  exact CSTTT.FallbackTheory.ExecutableSeed.seed_decision_exact b inputs source target
end CSTTT.FallbackTheory.CachedSeed
