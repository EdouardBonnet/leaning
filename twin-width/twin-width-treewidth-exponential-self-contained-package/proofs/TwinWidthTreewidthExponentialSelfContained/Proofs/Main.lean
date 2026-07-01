import TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.TwinWidthTreewidthContract
import TwinWidthTreewidthExponentialSelfContained.Statements.Main

namespace TwinWidthTreewidthExponentialSelfContained.Proofs.Main

theorem twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      TwinWidthTreewidthExponentialSelfContained.Statements.Main.treewidth (V := V) G ≤ 2 * k + 4 ∧
        2 ^ k < TwinWidthTreewidthExponentialSelfContained.Statements.Main.twinWidth (V := V) G :=
  by
    simpa [
      TwinWidthTreewidthExponentialSelfContained.Statements.Main.treewidth,
      TwinWidthTreewidthExponentialSelfContained.Statements.Main.twinWidth
    ] using
      TwinWidth.SimpleGraph.TwinWidthTreewidthContract.exists_graph_treewidth_linear_twin_width_exponential k

end TwinWidthTreewidthExponentialSelfContained.Proofs.Main
