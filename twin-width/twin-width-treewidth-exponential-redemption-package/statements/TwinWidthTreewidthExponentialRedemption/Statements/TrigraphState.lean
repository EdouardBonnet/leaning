import Mathlib.Data.Finset.Basic

namespace TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState

/-- A trigraph state on a fixed original vertex type, unpacked as a bag
partition together with symmetric black and red adjacency relations. -/
def IsTrigraphState {V : Type} [DecidableEq V]
    (bags : Finset (Finset V))
    (blackAdj redAdj : Finset V → Finset V → Prop) : Prop :=
  (∀ ⦃A⦄, A ∈ bags → A.Nonempty) ∧
  (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → A ≠ B → Disjoint A B) ∧
  (∀ v : V, ∃ A ∈ bags, v ∈ A) ∧
  (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → blackAdj B A) ∧
  (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → redAdj A B → redAdj B A) ∧
  (∀ ⦃A⦄, A ∈ bags → ¬ blackAdj A A) ∧
  (∀ ⦃A⦄, A ∈ bags → ¬ redAdj A A) ∧
  (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → ¬ redAdj A B)

end TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState

