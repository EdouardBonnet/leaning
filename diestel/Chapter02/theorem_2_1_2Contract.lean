import Chapter02.definitions_ch2

set_option linter.all false

namespace Diestel
namespace Chapter02

universe u

/--
Diestel, Theorem 2.1.2 (Hall).
Natural-language statement:
A finite bipartite graph with bipartition `{A,B}` contains a matching of
`A` if and only if every subset of `A` has at least as many neighbours in
`B` as its own cardinality.
-/
axiom theorem_2_1_2 {V : Type u} (G : SimpleGraph V)
    [Finite V] (A B : Set V) :
  G.IsBipartiteWith A B →
    (HasMatchingOf G A ↔ MarriageCondition G A B)

end Chapter02
end Diestel
