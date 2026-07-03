import Mathlib.Combinatorics.SimpleGraph.Basic
import TwinWidthTreewidthExponentialRedemption.Statements.SingletonBags
import TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState

namespace TwinWidthTreewidthExponentialRedemption.Statements.InitialTrigraphState

open TwinWidthTreewidthExponentialRedemption.Statements.SingletonBags
open TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState

/-- The type of initial trigraph states associated with a graph.  Such a state
has singleton bags, black adjacency exactly when the graph has an edge between
the two bags, and no red adjacency. -/
def InitialState {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Type :=
  Σ state : State V,
    PLift (
    bags state = singletonBags V ∧
    (∀ ⦃A B⦄, A ∈ bags state → B ∈ bags state →
      (blackAdj state A B ↔ ∃ a ∈ A, ∃ b ∈ B, G.Adj a b)) ∧
    (∀ ⦃A B⦄, A ∈ bags state → B ∈ bags state →
      ¬ redAdj state A B))

/-- The underlying trigraph state of an initial state. -/
def state {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (I : InitialState G) : State V :=
  Sigma.fst I

end TwinWidthTreewidthExponentialRedemption.Statements.InitialTrigraphState
