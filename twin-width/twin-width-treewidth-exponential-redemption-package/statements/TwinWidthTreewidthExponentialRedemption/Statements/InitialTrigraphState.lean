import Mathlib.Combinatorics.SimpleGraph.Basic
import TwinWidthTreewidthExponentialRedemption.Statements.SingletonBags

namespace TwinWidthTreewidthExponentialRedemption.Statements.InitialTrigraphState

/-- The initial trigraph state associated with a graph: singleton bags, black
edges exactly where the graph has an edge between the two bags, and no red
edges. -/
def IsInitialTrigraphState {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (bags : Finset (Finset V))
    (blackAdj redAdj : Finset V → Finset V → Prop) : Prop :=
  bags = TwinWidthTreewidthExponentialRedemption.Statements.SingletonBags.singletonBags V ∧
  (∀ ⦃A B⦄, A ∈ bags → B ∈ bags →
    (blackAdj A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b)) ∧
  (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → ¬ redAdj A B)

end TwinWidthTreewidthExponentialRedemption.Statements.InitialTrigraphState
