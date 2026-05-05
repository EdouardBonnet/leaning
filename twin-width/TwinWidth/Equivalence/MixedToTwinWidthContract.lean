import TwinWidth.Equivalence.MixedToTwinWidth

/-!
# Contract statement for the mixed-minor to twin-width direction

This file exposes the completed graph-facing bound obtained from the mirrored
matrix construction in Theorem 14.
-/

namespace TwinWidth
namespace SimpleGraph
namespace MixedToTwinWidthContract

/-- For every finite simple graph, twin-width is bounded by the explicit
Theorem 14 function of its mixed minor number. -/
theorem twin_width_le_mixed_minor_number_bound
    {V : Type} [Fintype V] [DecidableEq V] (G : _root_.SimpleGraph V) :
    twinWidth G ≤ twinWidthBoundOfMixedMinorNumber (mixedMinorNumber G) := by
  exact TwinWidth.SimpleGraph.twinWidth_le_twinWidthBoundOfMixedMinorNumber G

end MixedToTwinWidthContract
end SimpleGraph
end TwinWidth
