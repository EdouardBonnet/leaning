import TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed

namespace TwinWidthTreewidthExponentialRedemption2.Statements.ContractedBlack

open TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed
open TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState

/-- Black adjacency after contracting two bags `A` and `B` in a trigraph
state. -/
def contractedBlack {V : Type} [DecidableEq V]
    (T : State V) (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    blackAdj T A Y ∧ blackAdj T B Y ∧
      ¬ contractedRed T A B X Y
  else if Y = A ∪ B then
    blackAdj T X A ∧ blackAdj T X B ∧
      ¬ contractedRed T A B X Y
  else
    blackAdj T X Y

end TwinWidthTreewidthExponentialRedemption2.Statements.ContractedBlack
