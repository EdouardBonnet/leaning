import TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Graph.BonnetDepresLower
import TwinWidthTreewidthExponentialTransparent.Statements.Main

namespace TwinWidthTreewidthExponentialTransparent.Proofs.Main

theorem bonnet_depres_tree_decomposition_and_no_small_contraction_sequence
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (D : TwinWidth.SimpleGraph.TreeDecomposition G),
      (letI : Fintype D.Node := D.nodeFintype;
        (Finset.univ.sup fun i : D.Node => (D.bag i).card) - 1) ≤ 2 * k + 4 ∧
        ¬ Nonempty (TwinWidth.SimpleGraph.ContractionSequence G (2 ^ k)) := by
  refine
    ⟨TwinWidth.SimpleGraph.BonnetDepresVertex k, inferInstance, inferInstance,
      TwinWidth.SimpleGraph.bonnetDepresGraph k,
      TwinWidth.SimpleGraph.bonnetDepresTreeDecomposition k, ?_, ?_⟩
  · simpa [
      TwinWidth.SimpleGraph.TreeDecomposition.width,
      TwinWidth.SimpleGraph.bonnetDepresApexCount
    ] using TwinWidth.SimpleGraph.bonnetDepresTreeDecomposition_width_le k
  · simpa [
      TwinWidth.SimpleGraph.HasTwinWidthAtMost
    ] using TwinWidth.SimpleGraph.BonnetDepres.bonnetDepres_not_hasTwinWidthAtMost_two_pow k

end TwinWidthTreewidthExponentialTransparent.Proofs.Main
