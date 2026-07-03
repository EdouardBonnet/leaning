import Mathlib.Data.Finset.Basic
import TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState

namespace TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed

open TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState

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

end TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed
