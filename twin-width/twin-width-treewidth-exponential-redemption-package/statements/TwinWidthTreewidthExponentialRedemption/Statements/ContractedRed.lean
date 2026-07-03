import Mathlib.Data.Finset.Basic
import TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState

namespace TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed

open TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState

/-- Red adjacency after contracting two bags `A` and `B` in a trigraph state. -/
def contractedRed {V : Type} [DecidableEq V]
    (T : State V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    redAdj T A Y ∨ redAdj T B Y ∨
      blackAdj T A Y ≠ blackAdj T B Y
  else if Y = A ∪ B then
    redAdj T X A ∨ redAdj T X B ∨
      blackAdj T X A ≠ blackAdj T X B
  else
    redAdj T X Y

end TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed
