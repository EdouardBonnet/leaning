import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u v

/--
Diestel, Lemma 2.4.5.
Natural-language statement:
If an edge starts an exchange chain with respect to a family of spanning
trees and lies in two of them, the family can be exchanged to strictly
increase its edge union.
-/
axiom lemma_2_4_5 {V : Type u} {E : Type v} (G : MultiGraph V E)
    [Finite V] [Finite E] {k : ℕ} (T : Fin k → Set E) (e : E) :
  MultiGraph.Loopless G →
    MultiGraph.FamilySpanningTrees G T →
      MultiGraph.StartsExchangeChain G T e →
        MultiGraph.EdgeInAtLeastTwoTrees T e →
          MultiGraph.CanImproveTreeFamily G T

end Chapter02
end Diestel
