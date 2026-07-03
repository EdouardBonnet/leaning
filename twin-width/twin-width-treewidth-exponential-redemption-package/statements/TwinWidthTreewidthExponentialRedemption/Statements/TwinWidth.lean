import TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth

namespace TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth

noncomputable section

/-- The twin-width of a finite graph is the least red-degree bound admitting a
contraction sequence. -/
def twinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact if h : ∃ d,
      TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth.HasContractionSequenceWidthAtMost
        G d
    then Nat.find h else 0

end

end TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth
