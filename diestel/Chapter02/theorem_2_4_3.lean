import Chapter02.tree_covering_aux
import Chapter02.tree_covering_k_zero_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

/--
Diestel, Theorem 2.4.3 (Nash-Williams).
Natural-language statement:
The edges of a graph can be covered by at most `k` trees iff every
non-empty vertex set induces at most `k(|U|-1)` edges, with parallel
edges counted. Formally, the traces of those trees inside `G` are
multigraph forests, since the trees need not be subgraphs of `G`.
-/
theorem theorem_2_4_3 {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (k : ℕ) :
  MultiGraph.Loopless G →
    (MultiGraph.CanCoverEdgesByAtMostKTrees G k ↔
      ∀ U : Set V, U ⊆ G.vertexSet → U.Nonempty →
        MultiGraph.inducedEdgeCount G U ≤ k * (U.ncard - 1)) := by
  intro hLoopless
  by_cases hk : k = 0
  · subst k
    exact MultiGraph.theorem_2_4_3_k_zero G hLoopless
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    constructor
    · intro hcover
      exact MultiGraph.TreeCovering.canCoverEdgesByAtMostKTrees_inducedEdgeCount_bound
        (G := G) (k := k) hLoopless hcover
    · intro hbound
      exact MultiGraph.TreeCovering.canCoverEdgesByAtMostKTrees_of_induced_bound
        (G := G) (k := k) hkpos hLoopless hbound

end Chapter02
end Diestel
