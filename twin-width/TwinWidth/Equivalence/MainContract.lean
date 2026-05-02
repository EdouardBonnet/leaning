import TwinWidth.Equivalence.Main

/-!
# Contract statement for the main equivalence theorem

This contract file states the final combiner theorem currently proved by
`Main.lean`: the two explicit directional bounds imply functional equivalence.
-/

namespace TwinWidth
namespace MainContract

/-- If the explicit mixed-minor-to-twin-width and twin-width-to-mixed-minor
bounds both hold, then twin-width and mixed minor number are functionally
equivalent. -/
axiom twin_width_functionally_equivalent_mixed_minor_number_of_explicit_bounds
    (h₁ :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        SimpleGraph.twinWidth G ≤
          2 ^ (2 ^ (SimpleGraph.mixedMinorNumber G + 1)))
    (h₂ :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        SimpleGraph.mixedMinorNumber G ≤ 2 * SimpleGraph.twinWidth G + 2) :
    FunctionallyEquivalent SimpleGraph.twinWidth SimpleGraph.mixedMinorNumber

end MainContract
end TwinWidth
