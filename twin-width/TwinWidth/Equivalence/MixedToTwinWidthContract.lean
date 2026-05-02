import TwinWidth.Equivalence.MixedToTwinWidth

/-!
# Contract statements for the mixed-minor to twin-width direction

This contract file states the final reduction theorem currently proved by
`MixedToTwinWidth.lean`: an ordered-adjacency mixed-number bound implies the
graph-level mixed-minor bound.
-/

namespace TwinWidth
namespace SimpleGraph
namespace MixedToTwinWidthContract

/-- If every ordered adjacency matrix bounds the graph twin-width by
`2 ^ (2 ^ (ordered mixed number + 1))`, then every graph satisfies the same
bound with its mixed minor number. -/
axiom twin_width_le_double_exponential_mixed_minor_number_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V)
        (σ : VertexOrder V (Fintype.card V)),
          twinWidth G ≤ 2 ^ (2 ^ (Matrix.orderedAdjacencyMixedNumber G σ + 1))) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      twinWidth G ≤ 2 ^ (2 ^ (mixedMinorNumber G + 1))

end MixedToTwinWidthContract
end SimpleGraph
end TwinWidth
