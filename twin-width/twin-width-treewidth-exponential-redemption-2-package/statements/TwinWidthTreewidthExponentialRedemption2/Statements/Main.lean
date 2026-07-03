import TwinWidthTreewidthExponentialRedemption2.Statements.Treewidth
import TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth

namespace TwinWidthTreewidthExponentialRedemption2.Statements.Main

open TwinWidthTreewidthExponentialRedemption2.Statements.Treewidth
open TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth

/-- For every `k`, some finite graph has treewidth at most `2*k+4` and
twin-width greater than `2^k`. -/
axiom twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth G

end TwinWidthTreewidthExponentialRedemption2.Statements.Main
