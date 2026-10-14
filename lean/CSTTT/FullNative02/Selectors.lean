import CSTTT.FullNative02.Blocks

namespace CSTTT.FullNative02
set_option autoImplicit false

/-- The same fixed ascending token enumeration used by actual partition
execution. Request ordering is not ownership ordering. -/
def leastOwned (selector : List Token) : Option Token :=
  (tokens.filter fun t => decide (t∈selector)).head?

theorem least_owned_matches_execution (selector : List Token) :
    leastOwned selector=(tokens.filter fun t => decide (t∈selector)).head? := rfl

theorem least_owned_permutation (xs ys : List Token) (permutation : xs.Perm ys) :
    leastOwned xs=leastOwned ys := by
  have predicates : (fun t : Token => decide (t∈xs))=(fun t => decide (t∈ys)) := by
    funext t
    simp only [permutation.mem_iff]
  simp only [leastOwned,predicates]

end CSTTT.FullNative02
