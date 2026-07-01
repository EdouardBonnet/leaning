import TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.BonnetDepresLower
import TwinWidthTreewidthExponentialSelfContained.Statements.Main

namespace TwinWidthTreewidthExponentialSelfContained.Proofs.Main

theorem twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      TwinWidthTreewidthExponentialSelfContained.Statements.Main.treewidth (V := V) G ≤ 2 * k + 4 ∧
        2 ^ k < TwinWidthTreewidthExponentialSelfContained.Statements.Main.twinWidth (V := V) G := by
  refine
    ⟨TwinWidth.SimpleGraph.BonnetDepresVertex k, inferInstance, inferInstance,
      TwinWidth.SimpleGraph.bonnetDepresGraph k, ?_, ?_⟩
  · simpa [
      TwinWidthTreewidthExponentialSelfContained.Statements.Main.treewidth
    ] using TwinWidth.SimpleGraph.bonnetDepres_treewidth_le k
  · simpa [
      TwinWidthTreewidthExponentialSelfContained.Statements.Main.twinWidth
    ] using TwinWidth.SimpleGraph.BonnetDepres.bonnetDepres_two_pow_lt_twinWidth k

theorem twin_width_can_be_exponential_in_treewidth_expanded
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      (by
        classical
        exact
          if htw :
              ∃ width : Nat,
                ∃ D : TwinWidth.SimpleGraph.TreeDecomposition G,
                  (letI : Fintype D.Node := D.nodeFintype;
                    (Finset.univ.sup fun i : D.Node => (D.bag i).card) - 1) ≤ width
            then Nat.find htw else 0) ≤ 2 * k + 4 ∧
        2 ^ k <
          (by
            classical
            exact
              if htww :
                  ∃ d : Nat,
                    Nonempty (TwinWidth.SimpleGraph.ContractionSequence G d)
                then Nat.find htww else 0) := by
  refine
    ⟨TwinWidth.SimpleGraph.BonnetDepresVertex k, inferInstance, inferInstance,
      TwinWidth.SimpleGraph.bonnetDepresGraph k, ?_, ?_⟩
  · simpa [
      TwinWidth.SimpleGraph.treewidth,
      TwinWidth.SimpleGraph.HasTreewidthAtMost,
      TwinWidth.SimpleGraph.TreeDecomposition.width
    ] using TwinWidth.SimpleGraph.bonnetDepres_treewidth_le k
  · simpa [
      TwinWidth.SimpleGraph.twinWidth,
      TwinWidth.SimpleGraph.HasTwinWidthAtMost
    ] using TwinWidth.SimpleGraph.BonnetDepres.bonnetDepres_two_pow_lt_twinWidth k

end TwinWidthTreewidthExponentialSelfContained.Proofs.Main
