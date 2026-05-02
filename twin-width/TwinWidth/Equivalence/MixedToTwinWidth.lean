import TwinWidth.Equivalence.TwinWidthToMixed

/-!
# Mixed minor number to twin-width

This module records the opposite directional bound needed for functional
equivalence.  Section 5 gives an explicit elementary double-exponential bound
via the Marcus-Tardos theorem and the mixed-free matrix construction.
-/

namespace TwinWidth
namespace SimpleGraph

/-- The proposition that twin-width is bounded by a numerical function of mixed
minor number. -/
def TwinWidthBoundedByMixedMinorNumber : Prop :=
  ∃ f : ℕ → ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
    twinWidth G ≤ f (mixedMinorNumber G)

/-- A concrete elementary bound shape for the mixed-minor-to-twin-width
direction.  The Section 5 proof gives a double-exponential bound; this project
keeps the exact quantitative witness explicit rather than encoding `O(_)`
notation. -/
def twinWidthBoundOfMixedMinorNumber (k : ℕ) : ℕ :=
  2 ^ (2 ^ (k + 1))

/-- Matrix-level ordered-adjacency form of the mixed-to-twin-width direction.

This is the graph-facing interface of the second item of the grid-minor theorem
for twin-width: the twin-width of the graph represented by an ordered adjacency
matrix is bounded by a function of that matrix's mixed number. -/
def TwinWidthBoundedByOrderedAdjacencyMixedNumber (f : ℕ → ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
    (σ : VertexOrder V (Fintype.card V)),
      twinWidth G ≤ f (Matrix.orderedAdjacencyMixedNumber G σ)

/-- Passing from a bound for every ordered adjacency matrix to the graph mixed
minor number, using an order that realizes the minimum in `mixedMinorNumber`. -/
theorem twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyBound
    {f : ℕ → ℕ}
    (h : TwinWidthBoundedByOrderedAdjacencyMixedNumber f) :
    TwinWidthBoundedByMixedMinorNumber := by
  refine ⟨f, ?_⟩
  intro V _ _ G
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤ f (Matrix.orderedAdjacencyMixedNumber G σ) := h G σ
    _ = f (mixedMinorNumber G) := by rw [hσ]

/-- The concrete mixed-minor-to-twin-width direction, assuming the Section 5
ordered-adjacency matrix bound with the chosen elementary witness. -/
def TwinWidthBoundedByOrderedAdjacencyMixedNumberExplicit : Prop :=
  TwinWidthBoundedByOrderedAdjacencyMixedNumber twinWidthBoundOfMixedMinorNumber

/-- One functional-equivalence direction with the explicit mixed-minor witness,
obtained from the ordered-adjacency matrix bound. -/
theorem twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyExplicitBound
    (h : TwinWidthBoundedByOrderedAdjacencyMixedNumberExplicit) :
    TwinWidthBoundedByMixedMinorNumber :=
  twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyBound h

/-- Contract theorem for
`MixedToTwinWidthContract.twin_width_le_double_exponential_mixed_minor_number_of_ordered_adjacency_bound`.

An ordered-adjacency double-exponential bound gives the same graph-level bound
by choosing an order that realizes `mixedMinorNumber`. -/
theorem twin_width_le_double_exponential_mixed_minor_number_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
        (σ : VertexOrder V (Fintype.card V)),
          twinWidth G ≤ 2 ^ (2 ^ (Matrix.orderedAdjacencyMixedNumber G σ + 1))) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      twinWidth G ≤ 2 ^ (2 ^ (mixedMinorNumber G + 1)) := by
  intro V _ _ G
  obtain ⟨σ, hσ⟩ := exists_order_mixedNumber_eq_mixedMinorNumber G
  calc
    twinWidth G ≤ 2 ^ (2 ^ (Matrix.orderedAdjacencyMixedNumber G σ + 1)) := h G σ
    _ = 2 ^ (2 ^ (mixedMinorNumber G + 1)) := by rw [hσ]

end SimpleGraph
end TwinWidth
