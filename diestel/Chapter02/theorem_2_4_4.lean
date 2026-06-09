import Chapter02.tree_packing_maximal_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

/--
Diestel, Theorem 2.4.4 (Bowler-Carmesin).
Natural-language statement:
For every connected graph and every `k`, there is a partition whose
induced parts have `k` edge-disjoint spanning trees and whose quotient
has its crossing edges covered by `k` spanning trees.
-/
theorem theorem_2_4_4 {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] (k : ℕ) :
  MultiGraph.Loopless G →
    MultiGraph.Connected G →
      ∃ P : Finset (Set V), MultiGraph.PackingCoveringPartition G P k := by
  intro hLoopless hG
  exact MultiGraph.exists_packingCoveringPartition_of_connected
    (G := G) (k := k) hLoopless hG

end Chapter02
end Diestel
