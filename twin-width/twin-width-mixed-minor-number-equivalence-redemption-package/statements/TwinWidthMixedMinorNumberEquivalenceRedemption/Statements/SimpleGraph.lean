import TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber

namespace TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
namespace SimpleGraph

/-- The mixed minor number of a finite graph is the infimum, in Nat, of the
ordered-adjacency mixed numbers over all vertex orders of cardinality length. -/
noncomputable def mixedMinorNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf { k : ℕ |
    ∃ σ : VertexOrder.Order V (Fintype.card V),
      Matrix.OrderedAdjacencyMixedNumber.orderedAdjacencyMixedNumber G σ = k }

end SimpleGraph
end TwinWidthMixedMinorNumberEquivalenceRedemption.Statements
