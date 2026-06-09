import Chapter02.definitions_ch2

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
axiom corollary_2_4_2 {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (k : ℕ) :
  MultiGraph.Loopless G →
    MultiGraph.IsLEdgeConnected G (2 * k) →
      MultiGraph.HasKEdgeDisjointSpanningTrees G k

end Chapter02
end Diestel
