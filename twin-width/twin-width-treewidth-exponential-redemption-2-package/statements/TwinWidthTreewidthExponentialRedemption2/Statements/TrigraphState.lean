import Mathlib.Data.Finset.Basic

namespace TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState

/-- A trigraph state on a fixed original vertex type.  The data are current
bags, black adjacency on bags, and red adjacency on bags, together with the
partition, symmetry, looplessness, and disjoint-color invariants. -/
def State (V : Type) [DecidableEq V] : Type :=
  Σ bags : Finset (Finset V),
  Σ blackAdj : Finset V → Finset V → Prop,
  Σ redAdj : Finset V → Finset V → Prop,
    PLift (
    (∀ ⦃A⦄, A ∈ bags → A.Nonempty) ∧
    (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → A ≠ B → Disjoint A B) ∧
    (∀ v : V, ∃ A ∈ bags, v ∈ A) ∧
    (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → blackAdj B A) ∧
    (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → redAdj A B → redAdj B A) ∧
    (∀ ⦃A⦄, A ∈ bags → ¬ blackAdj A A) ∧
    (∀ ⦃A⦄, A ∈ bags → ¬ redAdj A A) ∧
    (∀ ⦃A B⦄, A ∈ bags → B ∈ bags → blackAdj A B → ¬ redAdj A B))

/-- The current bags of a trigraph state. -/
def bags {V : Type} [DecidableEq V] (T : State V) : Finset (Finset V) :=
  Sigma.fst T

/-- The black adjacency relation of a trigraph state. -/
def blackAdj {V : Type} [DecidableEq V] (T : State V) :
    Finset V → Finset V → Prop :=
  Sigma.fst (Sigma.snd T)

/-- The red adjacency relation of a trigraph state. -/
def redAdj {V : Type} [DecidableEq V] (T : State V) :
    Finset V → Finset V → Prop :=
  Sigma.fst (Sigma.snd (Sigma.snd T))

end TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState
