import TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Graph.BonnetDepresLower

namespace TwinWidthTreewidthExponentialTransparent.Statements.Main

axiom bonnet_depres_tree_decomposition_and_no_small_contraction_sequence
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (D : TwinWidth.SimpleGraph.TreeDecomposition G),
      (letI : Fintype D.Node := D.nodeFintype;
        (Finset.univ.sup fun i : D.Node => (D.bag i).card) - 1) ≤ 2 * k + 4 ∧
        ¬ Nonempty (TwinWidth.SimpleGraph.ContractionSequence G (2 ^ k))

end TwinWidthTreewidthExponentialTransparent.Statements.Main
