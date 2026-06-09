import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Theorem 2.1.4 (Gale-Shapley).
Natural-language statement:
For every set of preferences in a finite bipartite graph, there is a stable
matching.
-/
axiom theorem_2_1_4 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (A B : Set V) (P : Preferences G) :
  G.IsBipartiteWith A B →
    A ∪ B = Set.univ →
      ∃ M : G.Subgraph, StableMatching G P M

end Chapter02
end Diestel
