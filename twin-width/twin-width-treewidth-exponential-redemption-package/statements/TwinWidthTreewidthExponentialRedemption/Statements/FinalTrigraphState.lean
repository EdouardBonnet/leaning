import Mathlib.Data.Finset.Card
import TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState

namespace TwinWidthTreewidthExponentialRedemption.Statements.FinalTrigraphState

open TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState

/-- The type of final trigraph states, namely states with at most one current
bag. -/
def FinalState (V : Type) [DecidableEq V] : Type :=
  Σ state : State V, PLift ((bags state).card ≤ 1)

/-- The underlying trigraph state of a final state. -/
def state {V : Type} [DecidableEq V] (F : FinalState V) : State V :=
  Sigma.fst F

end TwinWidthTreewidthExponentialRedemption.Statements.FinalTrigraphState
