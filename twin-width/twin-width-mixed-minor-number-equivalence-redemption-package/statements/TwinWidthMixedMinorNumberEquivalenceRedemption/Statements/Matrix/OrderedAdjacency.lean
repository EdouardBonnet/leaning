import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.VertexOrder

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace Matrix
namespace OrderedAdjacency

/-- The Boolean adjacency matrix of a graph in a chosen vertex order. -/
def orderedAdjacency {V : Type*} {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (σ : VertexOrder.Order V n) :
    _root_.Matrix (Fin n) (Fin n) Bool :=
  fun i j => decide (G.Adj ((show Fin n ≃ V from σ) i) ((show Fin n ≃ V from σ) j))

end OrderedAdjacency
end Matrix
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
