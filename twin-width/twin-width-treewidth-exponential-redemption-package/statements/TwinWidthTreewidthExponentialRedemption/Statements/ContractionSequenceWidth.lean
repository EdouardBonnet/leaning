import Mathlib.Combinatorics.SimpleGraph.Basic
import TwinWidthTreewidthExponentialRedemption.Statements.ContractionStep
import TwinWidthTreewidthExponentialRedemption.Statements.FinalTrigraphState
import TwinWidthTreewidthExponentialRedemption.Statements.InitialTrigraphState
import TwinWidthTreewidthExponentialRedemption.Statements.RedDegree

namespace TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth

open TwinWidthTreewidthExponentialRedemption.Statements.ContractionStep
open TwinWidthTreewidthExponentialRedemption.Statements.FinalTrigraphState
open TwinWidthTreewidthExponentialRedemption.Statements.InitialTrigraphState
open TwinWidthTreewidthExponentialRedemption.Statements.RedDegree
open TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState

/-- The type of contraction sequences whose red degree is everywhere at most
`d`.  The data are a finite time horizon, a trigraph state at each time, an
initial-state witness, a final-state witness, a contraction witness for each
successive pair of states, and the red-degree bound. -/
def ContractionSequence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Type :=
  Σ stepCount : ℕ,
  Σ state : ℕ → State V,
  Σ start : InitialState G,
  Σ final : FinalState V,
    PLift (state 0 = InitialTrigraphState.state start) ×
    PLift (state stepCount = FinalTrigraphState.state final) ×
    (∀ i, i < stepCount → Step (state i) (state (i + 1))) ×
    PLift (∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ bags (state i) →
      redDegree (state i) A ≤ d)

end TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth
