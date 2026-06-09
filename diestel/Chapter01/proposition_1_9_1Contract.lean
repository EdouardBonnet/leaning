import Chapter01.definitions_ch1

set_option linter.all false

open scoped BigOperators

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Proposition 1.9.1.
Natural-language statement:
For an edge set `D`, membership in the cycle space is equivalent to being
a disjoint union of cycles, and to every vertex having even degree in
the subgraph induced by `D`.
-/
axiom proposition_1_9_1 {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [Fintype G.edgeSet]
    (D : EdgeSpace G) :
  (D ∈ cycle_space G ↔
    ∃ cycles : List (Σ a : V, G.Walk a a),
      (∀ c ∈ cycles, c.2.IsCycle) ∧
        D = cycles.foldr (fun c acc => cycle_vector G c.2 + acc) 0) ∧
    (D ∈ cycle_space G ↔
      ∀ v : V, Even (Nat.card {e : G.edgeSet // D e = 1 ∧ v ∈ (e : Sym2 V)}))

end Chapter01
end Diestel
