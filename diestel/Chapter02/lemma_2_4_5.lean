import Chapter02.matroid_tree_exchange_chain_aux
import Chapter02.spanning_tree_exchange_aux

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

/--
Diestel, Lemma 2.4.5.
If an edge starts an exchange chain with respect to a family of spanning
trees and lies in two of them, the family can be exchanged to strictly
increase its edge union.
-/
theorem lemma_2_4_5 {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] {k : ℕ} (T : Fin k → Set E) (e : E) :
  MultiGraph.Loopless G →
    MultiGraph.FamilySpanningTrees G T →
      MultiGraph.StartsExchangeChain G T e →
        MultiGraph.EdgeInAtLeastTwoTrees T e →
          MultiGraph.CanImproveTreeFamily G T := by
  classical
  intro hLoopless hFam hStart hTwo
  exact MultiGraph.canImprove_of_startsExchangeChain_spanningTree_exchange
    (G := G) (T := T) (e := e)
    (hExchange :=
      MultiGraph.TreeShadow.spanningTree_exchange_property
        (G := G) hLoopless)
    hFam hStart hTwo

end Chapter02
end Diestel
