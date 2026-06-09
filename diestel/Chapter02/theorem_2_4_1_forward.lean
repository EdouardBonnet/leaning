import Chapter02.tree_packing_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

/--
The forward implication of Diestel, Theorem 2.4.1.
Edge-disjoint spanning trees force the Nash-Williams/Tutte partition
inequalities.
-/
theorem theorem_2_4_1_forward {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (k : ℕ) :
    G.HasKEdgeDisjointSpanningTrees k →
      ∀ P : Finset (Set V), IsVertexPartitionOf G.vertexSet P →
        k * (P.card - 1) ≤ G.crossEdgeCount P := by
  intro hpack P hP
  exact hasKEdgeDisjointSpanningTrees_partition_bound
    (G := G) (k := k) hpack hP

end MultiGraph

end Chapter02
end Diestel
