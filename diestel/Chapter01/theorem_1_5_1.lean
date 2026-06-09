import Chapter01.definitions_ch1
import Mathlib.Combinatorics.SimpleGraph.Operations

set_option linter.all false

namespace Diestel
namespace Chapter01

universe u

/--
Diestel, Theorem 1.5.1.
For a graph `T`, being a tree is equivalent to unique paths between all
vertices, minimal connectedness, and maximal acyclicity.
-/
theorem theorem_1_5_1 {V : Type u} (T : SimpleGraph V) :
  T.IsTree ↔
    (∀ x y : V, ∃! p : T.Walk x y, p.IsPath) ∧
      (T.Connected ∧
        ∀ e : Sym2 V, e ∈ T.edgeSet → ¬ (T.deleteEdges {e}).Connected) ∧
          (T.IsAcyclic ∧
            ∀ x y : V, x ≠ y → ¬ T.Adj x y →
              ¬ (T ⊔ SimpleGraph.edge x y).IsAcyclic) := by
  constructor
  · intro hT
    have huniq := (SimpleGraph.isTree_iff_existsUnique_path.mp hT).2
    have hmin := SimpleGraph.isTree_iff_minimal_connected.mp hT
    have hmax := (SimpleGraph.isTree_iff_maximal_isAcyclic.mp hT).2
    refine ⟨huniq, ⟨hT.connected, ?_⟩, ⟨hT.isAcyclic, ?_⟩⟩
    · intro e he hdel
      exact hmin.not_prop_of_lt
        (by simpa [SimpleGraph.deleteEdges, ← SimpleGraph.edgeSet_ssubset_edgeSet])
        hdel
    · intro x y hxy hn hac
      have hEq : T = T ⊔ SimpleGraph.edge x y := (hmax.eq_of_ge hac le_sup_left).symm
      have hedge : (SimpleGraph.edge x y).Adj x y := by
        rw [SimpleGraph.edge_adj]
        exact ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
      have hsup : (T ⊔ SimpleGraph.edge x y).Adj x y := Or.inr hedge
      exact hn (by simpa [← hEq] using hsup)
  · rintro ⟨_huniq, ⟨hconn, _hmin⟩, ⟨hacyc, _hmax⟩⟩
    exact ⟨hconn, hacyc⟩

end Chapter01
end Diestel
