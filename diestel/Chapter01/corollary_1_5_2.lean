import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Corollary 1.5.2.
A connected graph with `n` vertices is a tree iff it has `n - 1` edges.
-/
theorem corollary_1_5_2 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
  G.Connected → (G.IsTree ↔ G.edgeFinset.card + 1 = Fintype.card V) := by
  intro hG
  constructor
  · intro hT
    exact hT.card_edgeFinset
  · intro hcard
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨hG, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rwa [← SimpleGraph.edgeFinset_card]

end Chapter01
end Diestel
