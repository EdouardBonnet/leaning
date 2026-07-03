import TwinWidthTreewidthExponentialRedemption.Statements.LeastNatural
import TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth

namespace TwinWidthTreewidthExponentialRedemption.Statements.Treewidth

open TwinWidthTreewidthExponentialRedemption.Statements.LeastNatural
open TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth

noncomputable section

/-- The treewidth of a finite graph is the least width of a tree decomposition.
The fallback value is `0` if the search type is empty. -/
def treewidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  leastNat fun width => ∃ D : TreeDecomposition G,
    treeDecompositionWidth D ≤ width

end

end TwinWidthTreewidthExponentialRedemption.Statements.Treewidth
