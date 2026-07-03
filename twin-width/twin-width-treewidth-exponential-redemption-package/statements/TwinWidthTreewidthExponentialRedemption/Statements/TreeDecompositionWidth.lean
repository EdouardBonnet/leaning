import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth

/-- A graph has a tree decomposition of width at most `width`, unpacked as a
finite tree of bags satisfying vertex coverage, edge coverage, connectedness
of the bag indices for each vertex, and the usual maximum-bag-size bound. -/
def HasTreeDecompositionWidthAtMost {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (width : ℕ) : Prop :=
  ∃ Node : Type,
  ∃ nodeFintype : Fintype Node,
  ∃ _nodeDecidableEq : DecidableEq Node,
  ∃ tree : SimpleGraph Node,
    tree.IsTree ∧
    ∃ bag : Node → Finset V,
      (∀ v : V, ∃ i : Node, v ∈ bag i) ∧
      (∀ ⦃u v : V⦄, G.Adj u v → ∃ i : Node, u ∈ bag i ∧ v ∈ bag i) ∧
      (∀ v : V, (tree.induce {i : Node | v ∈ bag i}).Connected) ∧
      (letI : Fintype Node := nodeFintype;
        (Finset.univ.sup fun i : Node => (bag i).card) - 1) ≤ width

end TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth
