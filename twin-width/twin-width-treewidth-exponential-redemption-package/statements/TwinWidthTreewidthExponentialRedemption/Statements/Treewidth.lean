import TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth

namespace TwinWidthTreewidthExponentialRedemption.Statements.Treewidth

noncomputable section

/-- The treewidth of a finite graph is the least width for which the graph has
a tree decomposition of that width. -/
def treewidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact if h : ∃ width,
      TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth.HasTreeDecompositionWidthAtMost
        G width
    then Nat.find h else 0

end

end TwinWidthTreewidthExponentialRedemption.Statements.Treewidth
