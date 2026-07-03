import TwinWidthTreewidthExponentialRedemption.Statements.LeastNatural
import TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth

namespace TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth

open TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth
open TwinWidthTreewidthExponentialRedemption.Statements.LeastNatural

noncomputable section

/-- The twin-width of a finite graph is the least red-degree bound admitting a
contraction sequence.  The fallback value is `0` if the search type is empty. -/
def twinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  leastNat fun d => Nonempty (ContractionSequence G d)

end

end TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth
