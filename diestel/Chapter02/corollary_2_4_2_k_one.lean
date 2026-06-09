import Chapter02.multigraph_spanning_tree_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

namespace MultiGraph

/--
The `k = 1` specialization of Diestel, Corollary 2.4.2.
The full contract remains the arbitrary-`k` statement.
-/
theorem corollary_2_4_2_k_one {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] :
    G.Loopless →
      G.IsLEdgeConnected (2 * 1) →
        G.HasKEdgeDisjointSpanningTrees 1 := by
  intro _ hconn
  exact hasOneEdgeDisjointSpanningTree_of_isLEdgeConnected_pos
    (G := G) hconn (by norm_num)

end MultiGraph

end Chapter02
end Diestel
