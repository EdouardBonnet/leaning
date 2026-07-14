import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedNumber
import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacency

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace Matrix
namespace OrderedAdjacencyMixedNumber

/-- The mixed number of the ordered adjacency matrix of a graph. -/
noncomputable def orderedAdjacencyMixedNumber {V : Type*} {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (σ : VertexOrder.Order V n) : ℕ :=
  MixedNumber.matrixMixedNumber (OrderedAdjacency.orderedAdjacency G σ)

end OrderedAdjacencyMixedNumber
end Matrix
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
