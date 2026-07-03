import Mathlib.Combinatorics.SimpleGraph.Basic
import TwinWidthTreewidthExponentialRedemption2.Statements.ContractionStep
import TwinWidthTreewidthExponentialRedemption2.Statements.FinalTrigraphState
import TwinWidthTreewidthExponentialRedemption2.Statements.InitialTrigraphState
import TwinWidthTreewidthExponentialRedemption2.Statements.RedDegree

namespace TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth

open TwinWidthTreewidthExponentialRedemption2.Statements.ContractionStep
open TwinWidthTreewidthExponentialRedemption2.Statements.FinalTrigraphState
open TwinWidthTreewidthExponentialRedemption2.Statements.InitialTrigraphState
open TwinWidthTreewidthExponentialRedemption2.Statements.RedDegree
open TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState

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

end TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth
