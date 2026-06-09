import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.5.5.
Natural-language statement:
Every connected graph has a normal spanning tree.

Lean convention note:
The unrestricted statement is false for arbitrary simple graphs: an
uncountable complete graph cannot have a normal spanning tree, since
normality would make the tree-order a total order and hence leave at most
one vertex at each finite depth. In this Chapter 1 finite-graph
formalization, the theorem is stated for finite graphs.
-/
axiom proposition_1_5_5 {V : Type u} (G : SimpleGraph V) [Finite V] :
  G.Connected → ∃ T : SimpleGraph V, ∃ r : V, IsNormalSpanningTree G T r

end Chapter01
end Diestel
