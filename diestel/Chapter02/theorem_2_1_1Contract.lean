import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Theorem 2.1.1 (Konig).
Natural-language statement:
In a finite bipartite graph, the maximum cardinality of a matching equals
the minimum cardinality of a vertex cover of its edges.
-/
axiom theorem_2_1_1 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (A B : Set V) :
  G.IsBipartiteWith A B →
    A ∪ B = Set.univ →
      (matchingNumber G : ℕ∞) = SimpleGraph.vertexCoverNum G

end Chapter02
end Diestel
