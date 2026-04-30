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

end TwinWidth
