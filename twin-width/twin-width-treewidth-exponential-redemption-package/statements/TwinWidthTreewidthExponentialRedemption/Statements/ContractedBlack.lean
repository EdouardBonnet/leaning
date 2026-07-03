import TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed

namespace TwinWidthTreewidthExponentialRedemption.Statements.ContractedBlack

/-- Black adjacency after contracting two bags `A` and `B`. -/
def contractedBlack {V : Type} [DecidableEq V]
    (blackAdj redAdj : Finset V → Finset V → Prop)
    (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    blackAdj A Y ∧ blackAdj B Y ∧
      ¬ TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed.contractedRed
        blackAdj redAdj A B X Y
  else if Y = A ∪ B then
    blackAdj X A ∧ blackAdj X B ∧
      ¬ TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed.contractedRed
        blackAdj redAdj A B X Y
  else
    blackAdj X Y

end TwinWidthTreewidthExponentialRedemption.Statements.ContractedBlack
