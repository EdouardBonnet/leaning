import Chapter02.edge_connectivity_partition_aux
import Chapter02.theorem_2_4_1

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

/--
Diestel, Corollary 2.4.2.
Natural-language statement:
Every `2k`-edge-connected finite graph has `k` edge-disjoint spanning
trees.
-/
theorem corollary_2_4_2 {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (k : ℕ) :
  MultiGraph.Loopless G →
    MultiGraph.IsLEdgeConnected G (2 * k) →
      MultiGraph.HasKEdgeDisjointSpanningTrees G k := by
  intro hLoopless hconn
  exact (theorem_2_4_1 (G := G) k hLoopless).mpr
    (fun P hP =>
      MultiGraph.isLEdgeConnected_partition_bound
        (G := G) (k := k) hconn hP)

end Chapter02
end Diestel
