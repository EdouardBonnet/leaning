import TwinWidth.Equivalence.Main

/-!
# Small examples

Examples are intentionally minimal until the core Section 5 constructions are
fully formalized.
-/

namespace TwinWidth

example
    (h₁ : SimpleGraph.TwinWidthBoundedByMixedMinorNumber)
    (h₂ : SimpleGraph.MixedMinorNumberBoundedByTwinWidth) :
    FunctionallyEquivalent SimpleGraph.twinWidth SimpleGraph.mixedMinorNumber :=
  twinWidth_functionallyEquivalent_mixedMinorNumber_of_bounds h₁ h₂

end TwinWidth
