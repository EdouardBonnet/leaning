import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Operations

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Theorem 1.5.1.
Natural-language statement:
For a graph `T`, being a tree is equivalent to unique paths between all
vertices, minimal connectedness, and maximal acyclicity.
-/
axiom theorem_1_5_1 {V : Type u} (T : SimpleGraph V) :
  T.IsTree ↔
    (∀ x y : V, ∃! p : T.Walk x y, p.IsPath) ∧
      (T.Connected ∧
        ∀ e : Sym2 V, e ∈ T.edgeSet → ¬ (T.deleteEdges {e}).Connected) ∧
          (T.IsAcyclic ∧
            ∀ x y : V, x ≠ y → ¬ T.Adj x y →
              ¬ (T ⊔ SimpleGraph.edge x y).IsAcyclic)

end Chapter01
end Diestel
