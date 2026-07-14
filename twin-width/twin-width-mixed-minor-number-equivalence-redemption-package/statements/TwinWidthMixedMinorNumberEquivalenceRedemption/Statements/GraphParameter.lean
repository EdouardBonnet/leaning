import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace GraphParameter

/-- A finite simple-graph parameter. -/
def GraphParam :=
  ∀ {V : Type}, [Fintype V] → [DecidableEq V] →
    (G : SimpleGraph V) → [DecidableRel G.Adj] → ℕ

end GraphParameter
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
