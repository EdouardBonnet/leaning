import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Corollary 2.1.3.
Natural-language statement:
Every finite positive-degree regular bipartite graph has a 1-factor.
-/
axiom corollary_2_1_3 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (A B : Set V) (k : ℕ) :
  G.IsBipartiteWith A B →
    G.IsRegularOfDegree k →
      1 ≤ k →
        ∃ M : G.Subgraph, M.IsPerfectMatching

end Chapter02
end Diestel
