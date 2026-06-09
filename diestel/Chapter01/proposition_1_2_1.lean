import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.2.1.
The number of vertices of odd degree in a graph is always even.
-/
theorem proposition_1_2_1 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
  Even (Fintype.card {v : V // Odd (G.degree v)}) := by
  classical
  rw [Fintype.card_subtype]
  exact G.even_card_odd_degree_vertices

end Chapter01
end Diestel
