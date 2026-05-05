import TwinWidth.Graph.Theorem14

/-!
# Contract statement for Theorem 14

This file exposes the completed graph-facing statement of Theorem 14: graph
twin-width is bounded by the explicit mixed-free function at one more than the
graph mixed minor number.
-/

namespace TwinWidth
namespace SimpleGraph
namespace Theorem14Contract

/-- Theorem 14, graph form: every finite simple graph has twin-width bounded
by the explicit mixed-free bound at one more than its mixed minor number. -/
theorem twin_width_le_theorem14_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) :
    twinWidth G ≤ theorem14MixedFreeTwinWidthBound (mixedMinorNumber G + 1) := by
  exact theorem14_twinWidth_le_mixedMinorNumber_explicit G

end Theorem14Contract
end SimpleGraph
end TwinWidth
