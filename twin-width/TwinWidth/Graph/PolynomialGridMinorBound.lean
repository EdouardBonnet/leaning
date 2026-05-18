import Mathlib.Data.Nat.Log

/-!
# Polynomial grid-minor threshold

This definition-only file contains the natural-number threshold expression used
in the polynomial grid-minor theorem.  It is separate from the contract theorem
so proof files can refer to the bound without importing the final theorem
wrapper.
-/

namespace TwinWidth
namespace SimpleGraph

/-- The explicit natural-number treewidth threshold
`c1 * g^9 * (log_2 g)^c2` used to state the polynomial grid-minor theorem. -/
def polynomialGridMinorTreewidthBound (c1 c2 g : ℕ) : ℕ :=
  c1 * g ^ 9 * (Nat.log 2 g) ^ c2

end SimpleGraph
end TwinWidth
