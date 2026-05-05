import TwinWidth.Graph.TwinDecomposition

/-!
# Contract statement for the twin-width to mixed-minor direction

This file exposes the completed graph-facing linear bound obtained from the
left-to-right leaf order of a twin-decomposition.
-/

namespace TwinWidth
namespace SimpleGraph
namespace TwinWidthToMixedContract

/-- For every finite simple graph, mixed minor number is linearly bounded by
twin-width.  The constant reflects the project's diagonal and mirrored-fusion
conventions for simple graph adjacency matrices. -/
theorem mixed_minor_number_le_twin_width_linear
    {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    mixedMinorNumber G ≤ 2 * (twinWidth G + 3) + 2 := by
  exact TwinWidth.SimpleGraph.mixed_minor_number_le_twice_twin_width_plus_eight G

end TwinWidthToMixedContract
end SimpleGraph
end TwinWidth
