import Chapter01.definitions_ch1

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.3.1.
Natural-language statement:
Every graph contains a path of length `δ(G)` and, if `δ(G) ≥ 2`, a cycle
of length at least `δ(G) + 1`.
-/
axiom proposition_1_3_1 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [Nonempty V] [DecidableRel G.Adj] :
  (∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ G.minDegree ≤ p.length) ∧
    (2 ≤ G.minDegree →
      ∃ a : V, ∃ c : G.Walk a a, c.IsCycle ∧ G.minDegree + 1 ≤ c.length)

end Chapter01
end Diestel
