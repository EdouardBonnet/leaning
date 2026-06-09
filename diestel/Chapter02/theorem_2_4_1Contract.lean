import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

/--
Diestel, Theorem 2.4.1 (Nash-Williams/Tutte).
Natural-language statement:
A graph contains `k` edge-disjoint spanning trees iff every vertex
partition has at least `k(|P|-1)` cross-edges, with parallel edges counted.
-/
axiom theorem_2_4_1 {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (k : ℕ) :
  MultiGraph.Loopless G →
    (MultiGraph.HasKEdgeDisjointSpanningTrees G k ↔
      ∀ P : Finset (Set V), MultiGraph.IsVertexPartitionOf G.vertexSet P →
        k * (P.card - 1) ≤ MultiGraph.crossEdgeCount G P)

end Chapter02
end Diestel
