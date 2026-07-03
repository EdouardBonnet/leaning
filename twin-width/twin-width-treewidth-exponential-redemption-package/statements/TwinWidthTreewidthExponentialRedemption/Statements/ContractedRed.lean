import Mathlib.Data.Finset.Basic

namespace TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed

/-- Red adjacency after contracting two bags `A` and `B`. -/
def contractedRed {V : Type} [DecidableEq V]
    (blackAdj redAdj : Finset V → Finset V → Prop)
    (A B X Y : Finset V) : Prop :=
  if X = Y then
    False
  else if X = A ∪ B then
    redAdj A Y ∨ redAdj B Y ∨ blackAdj A Y ≠ blackAdj B Y
  else if Y = A ∪ B then
    redAdj X A ∨ redAdj X B ∨ blackAdj X A ≠ blackAdj X B
  else
    redAdj X Y

end TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed

