import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Corollary 1.5.2.
Natural-language statement:
A connected graph with `n` vertices is a tree iff it has `n - 1` edges.
-/
axiom corollary_1_5_2 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
  G.Connected → (G.IsTree ↔ G.edgeFinset.card + 1 = Fintype.card V)

end Chapter01
end Diestel
