import TwinWidth.Equivalence.TwinWidthToMixed

/-!
# Contract statements for the twin-width to mixed-minor direction

This contract file states the final reduction theorem currently proved by
`TwinWidthToMixed.lean`: an ordered-adjacency linear bound implies the
graph-level linear bound.
-/

namespace TwinWidth
namespace SimpleGraph
namespace TwinWidthToMixedContract

/-- If every finite graph has an ordered adjacency matrix with mixed number at
most `2 * twinWidth G + 2`, then the graph mixed minor number satisfies the
same bound. -/
axiom mixed_minor_number_le_twice_twin_width_add_two_of_ordered_adjacency_bound
    (h :
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
        ∃ σ : VertexOrder V (Fintype.card V),
          Matrix.orderedAdjacencyMixedNumber G σ ≤ 2 * twinWidth G + 2) :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V),
      mixedMinorNumber G ≤ 2 * twinWidth G + 2

end TwinWidthToMixedContract
end SimpleGraph
end TwinWidth
