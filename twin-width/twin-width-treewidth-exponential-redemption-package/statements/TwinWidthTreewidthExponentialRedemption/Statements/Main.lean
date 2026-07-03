import TwinWidthTreewidthExponentialRedemption.Statements.Treewidth
import TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth

namespace TwinWidthTreewidthExponentialRedemption.Statements.Main

open TwinWidthTreewidthExponentialRedemption.Statements.Treewidth
open TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth

/-- For every `k`, some finite graph has treewidth at most `2*k+4` and
twin-width greater than `2^k`. -/
axiom twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      treewidth G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth G

end TwinWidthTreewidthExponentialRedemption.Statements.Main
