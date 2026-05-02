import TwinWidth.Equivalence.MixedToTwinWidth

/-!
# Main equivalence statement from directional bounds

This file contains the theorem-combiner layer.  The two hard mathematical
ingredients are the directional bounds recorded in the imported modules.
-/

namespace TwinWidth

open SimpleGraph

/-- The two directional bounds imply functional equivalence of twin-width and
mixed minor number. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds
    (h₁ : TwinWidthBoundedByMixedMinorNumber)
    (h₂ : MixedMinorNumberBoundedByTwinWidth) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  exact ⟨h₁, h₂⟩

/-- Functional equivalence from the hard mixed-to-twin-width bound and the
Section 5 ordered-adjacency form of the twin-width-to-mixed direction. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_mixedToTwinWidth_and_orderedAdjacency
    (h₁ : TwinWidthBoundedByMixedMinorNumber)
    (h₂ : OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  exact twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds h₁
    (mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyLinearBound h₂)

/-- Functional equivalence from the two ordered-adjacency matrix bounds supplied
by the grid-minor theorem for twin-width. -/
theorem twinWidth_functionallyEquivalent_mixedMinorNumber_of_orderedAdjacencyBounds
    (h₁ : TwinWidthBoundedByOrderedAdjacencyMixedNumberExplicit)
    (h₂ : OrderedAdjacencyMixedNumberLinearlyBoundedByTwinWidth) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  exact twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds
    (twinWidthBoundedByMixedMinorNumber_of_orderedAdjacencyExplicitBound h₁)
    (mixedMinorNumberBoundedByTwinWidth_of_orderedAdjacencyLinearBound h₂)

/-- Contract theorem for
`MainContract.twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds`.

The two explicit directional inequalities imply functional equivalence. -/
theorem twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds
    (h₁ :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        twinWidth G ≤ 2 ^ (2 ^ (mixedMinorNumber G + 1)))
    (h₂ :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        mixedMinorNumber G ≤ 2 * twinWidth G + 2) :
    FunctionallyEquivalent twinWidth mixedMinorNumber := by
  constructor
  · refine ⟨fun k => 2 ^ (2 ^ (k + 1)), ?_⟩
    intro V _ _ G
    exact h₁ G
  · refine ⟨fun d => 2 * d + 2, ?_⟩
    intro V _ _ G
    exact h₂ G

end TwinWidth
