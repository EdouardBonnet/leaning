import TwinWidth.Equivalence.FunctionalEquivalence
import TwinWidth.Graph.MixedMinorNumber

/-!
# Twin-width to mixed minor number

This module records the directional bound needed for functional equivalence.
The Section 5 proof of the first twin-width paper should eventually provide a
specific witness such as `fun d => 2 * d + 2`.
-/

namespace TwinWidth
namespace SimpleGraph

/-- The proposition that mixed minor number is bounded by a numerical function
of twin-width. -/
def MixedMinorNumberBoundedByTwinWidth : Prop :=
  ∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
    mixedMinorNumber G ≤ f (twinWidth G)

/-- The linear bound predicted by the first item of the grid-minor theorem for
twin-width: a `d`-twin-ordered matrix is `(2*d+2)`-mixed-free. -/
def mixedMinorNumberBoundOfTwinWidth (d : ℕ) : ℕ :=
  2 * d + 2

/-- Matrix-level ordered-adjacency form of the twin-width-to-mixed direction.

This is the exact interface supplied by Section 5's first item: for every graph,
there is a vertex order whose adjacency matrix has mixed number bounded by a
function of the graph twin-width.  Since `mixedMinorNumber` is the minimum over
orders, this immediately gives the graph-parameter direction below. -/
def OrderedAdjacencyMixedNumberBoundedByTwinWidth (f : ℕ → ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
    ∃ σ : VertexOrder V (Fintype.card V),
      Matrix.orderedAdjacencyMixedNumber G σ ≤ f (twinWidth G)

/-- Passing from a bounded ordered adjacency matrix to the graph mixed minor
number. -/
theorem mixedMinorNumber_le_of_orderedAdjacencyMixedNumber_le
    {V : Type} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V} {f : ℕ → ℕ}
    {σ : VertexOrder V (Fintype.card V)}
    (hσ : Matrix.orderedAdjacencyMixedNumber G σ ≤ f (twinWidth G)) :
    mixedMinorNumber G ≤ f (twinWidth G) :=
  le_trans (mixedMinorNumber_le_orderedAdjacencyMixedNumber G σ) hσ

/-- The graph-parameter direction follows from the ordered-adjacency matrix
bound. -/
theorem mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyBound
    {f : ℕ → ℕ}
    (h : OrderedAdjacencyMixedNumberBoundedByTwinWidth f) :
    MixedMinorNumberBoundedByTwinWidth := by
  refine ⟨f, ?_⟩
  intro V _ _ G
  rcases h G with ⟨σ, hσ⟩
  exact mixedMinorNumber_le_of_orderedAdjacencyMixedNumber_le (G := G) hσ

/-- The concrete one-direction statement corresponding to the paper's
`2*d+2` convention.  The remaining mathematical input is the Section 5 matrix
proof that supplies such an ordered adjacency matrix. -/
def OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth : Prop :=
  OrderedAdjacencyMixedNumberBoundedByTwinWidth mixedMinorNumberBoundOfTwinWidth

/-- One functional-equivalence direction with the explicit `2*d+2` witness,
assuming the Section 5 ordered-adjacency bound. -/
theorem mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyLinearBound
    (h : OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth) :
    MixedMinorNumberBoundedByTwinWidth :=
  mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyBound h

/-- Contract theorem for
`TwinWidthToMixedContract.mixed_minor_number_le_twice_twin_width_add_two_of_ordered_adjacency_bound`.

An ordered-adjacency linear bound immediately gives the same graph-level bound,
because `mixedMinorNumber` is the minimum over vertex orders. -/
theorem mixed_minor_number_le_twice_twin_width_add_two_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        ∃ σ : VertexOrder V (Fintype.card V),
          Matrix.orderedAdjacencyMixedNumber G σ ≤ 2 * twinWidth G + 2) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      mixedMinorNumber G ≤ 2 * twinWidth G + 2 := by
  intro V _ _ G
  rcases h G with ⟨σ, hσ⟩
  exact mixedMinorNumber_le_of_orderedAdjacencyMixedNumber_le
    (G := G) (f := fun d => 2 * d + 2) hσ

end SimpleGraph
end TwinWidth
