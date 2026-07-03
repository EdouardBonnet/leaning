import TwinWidthTreewidthExponentialRedemption2.Statements.LeastNatural
import TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth

namespace TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth

open TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth
open TwinWidthTreewidthExponentialRedemption2.Statements.LeastNatural

noncomputable section

/-- The twin-width of a finite graph is the least red-degree bound admitting a
contraction sequence.  The fallback value is `0` if the search type is empty. -/
def twinWidth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  leastNat fun d => Nonempty (ContractionSequence G d)

end

end TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth
