import TwinWidthTreewidthExponentialRedemption2.Statements.ContractedBlack
import TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed

namespace TwinWidthTreewidthExponentialRedemption2.Statements.ContractionStep

open TwinWidthTreewidthExponentialRedemption2.Statements.ContractedBlack
open TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed
open TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState

/-- The type of witnesses that one trigraph state is obtained from another by
contracting two distinct current bags. -/
def Step {V : Type} [DecidableEq V]
    (T U : State V) : Type :=
  Σ left : Finset V,
  Σ right : Finset V,
    PLift (
    left ∈ bags T ∧
    right ∈ bags T ∧
    left ≠ right ∧
    bags U = insert (left ∪ right) (((bags T).erase left).erase right) ∧
    (∀ ⦃X Y⦄, X ∈ bags U → Y ∈ bags U →
      (redAdj U X Y ↔ contractedRed T left right X Y)) ∧
    (∀ ⦃X Y⦄, X ∈ bags U → Y ∈ bags U →
      (blackAdj U X Y ↔ contractedBlack T left right X Y)))

end TwinWidthTreewidthExponentialRedemption2.Statements.ContractionStep
