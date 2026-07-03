import Mathlib.Data.Finset.Card

namespace TwinWidthTreewidthExponentialRedemption.Statements.FinalTrigraphState

/-- A final trigraph state has at most one current bag. -/
def IsFinalTrigraphState {V : Type} (bags : Finset (Finset V)) : Prop :=
  bags.card ≤ 1

end TwinWidthTreewidthExponentialRedemption.Statements.FinalTrigraphState
