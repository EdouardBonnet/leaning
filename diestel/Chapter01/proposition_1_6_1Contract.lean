import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.6.1.
Natural-language statement:
A graph is bipartite iff it contains no odd cycle.
-/
axiom proposition_1_6_1 {V : Type u} (G : SimpleGraph V) :
  G.IsBipartite ↔ ∀ a : V, ∀ c : G.Walk a a, c.IsCycle → ¬ Odd c.length

end Chapter01
end Diestel
