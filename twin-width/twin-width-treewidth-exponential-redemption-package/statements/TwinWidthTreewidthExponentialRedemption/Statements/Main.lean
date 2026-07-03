import TwinWidthTreewidthExponentialRedemption.Statements.Treewidth
import TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth

namespace TwinWidthTreewidthExponentialRedemption.Statements.Main

/-- For every `k`, some finite graph has treewidth at most `2*k+4` and
twin-width greater than `2^k`. -/
axiom twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      TwinWidthTreewidthExponentialRedemption.Statements.Treewidth.treewidth G ≤ 2 * k + 4 ∧
        2 ^ k < TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth.twinWidth G

end TwinWidthTreewidthExponentialRedemption.Statements.Main
