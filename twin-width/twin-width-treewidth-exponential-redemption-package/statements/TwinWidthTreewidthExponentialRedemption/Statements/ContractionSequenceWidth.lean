import Mathlib.Combinatorics.SimpleGraph.Basic
import TwinWidthTreewidthExponentialRedemption.Statements.ContractionStep
import TwinWidthTreewidthExponentialRedemption.Statements.FinalTrigraphState
import TwinWidthTreewidthExponentialRedemption.Statements.InitialTrigraphState
import TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState
import TwinWidthTreewidthExponentialRedemption.Statements.RedDegree

namespace TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth

/-- A contraction sequence of width at most `d`, with all trigraph-state data
spelled out explicitly on the original vertex type. -/
def HasContractionSequenceWidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ stepCount : ℕ,
  ∃ bags : ℕ → Finset (Finset V),
  ∃ blackAdj : ℕ → Finset V → Finset V → Prop,
  ∃ redAdj : ℕ → Finset V → Finset V → Prop,
    (∀ i,
      TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState.IsTrigraphState
        (bags i) (blackAdj i) (redAdj i)) ∧
    TwinWidthTreewidthExponentialRedemption.Statements.InitialTrigraphState.IsInitialTrigraphState G
      (bags 0) (blackAdj 0) (redAdj 0) ∧
    TwinWidthTreewidthExponentialRedemption.Statements.FinalTrigraphState.IsFinalTrigraphState
      (bags stepCount) ∧
    (∀ i, i < stepCount →
      TwinWidthTreewidthExponentialRedemption.Statements.ContractionStep.IsContractionStep
        (bags i) (blackAdj i) (redAdj i)
        (bags (i + 1)) (blackAdj (i + 1)) (redAdj (i + 1))) ∧
    (∀ i, i ≤ stepCount → ∀ ⦃A⦄, A ∈ bags i →
      TwinWidthTreewidthExponentialRedemption.Statements.RedDegree.redDegree
        (bags i) (redAdj i) A ≤ d)

end TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth
