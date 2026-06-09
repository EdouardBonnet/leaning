import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.4.2.
Natural-language statement:
If `G` is non-trivial, then `κ(G) ≤ λ(G) ≤ δ(G)`.
-/
axiom proposition_1_4_2 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] :
  1 < Fintype.card V →
    vertex_connectivity G ≤ edge_connectivity G ∧ edge_connectivity G ≤ G.minDegree

end Chapter01
end Diestel
