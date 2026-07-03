import TwinWidthTreewidthExponentialRedemption.Statements.ContractedBlack
import TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed

namespace TwinWidthTreewidthExponentialRedemption.Statements.ContractionStep

/-- One step of a contraction sequence, unpacked as the replacement of two
distinct current bags by their union and the induced black/red adjacencies. -/
def IsContractionStep {V : Type} [DecidableEq V]
    (bags : Finset (Finset V))
    (blackAdj redAdj : Finset V → Finset V → Prop)
    (nextBags : Finset (Finset V))
    (nextBlackAdj nextRedAdj : Finset V → Finset V → Prop) : Prop :=
  ∃ A ∈ bags, ∃ B ∈ bags, A ≠ B ∧
    nextBags = insert (A ∪ B) ((bags.erase A).erase B) ∧
    (∀ ⦃X Y⦄, X ∈ nextBags → Y ∈ nextBags →
      (nextRedAdj X Y ↔
        TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed.contractedRed
          blackAdj redAdj A B X Y)) ∧
    (∀ ⦃X Y⦄, X ∈ nextBags → Y ∈ nextBags →
      (nextBlackAdj X Y ↔
        TwinWidthTreewidthExponentialRedemption.Statements.ContractedBlack.contractedBlack
          blackAdj redAdj A B X Y))

end TwinWidthTreewidthExponentialRedemption.Statements.ContractionStep
