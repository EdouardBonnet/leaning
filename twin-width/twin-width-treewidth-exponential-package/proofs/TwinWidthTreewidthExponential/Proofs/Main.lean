import TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Graph.TwinWidthTreewidthContract
import TwinWidthTreewidthExponential.Statements.Main

namespace TwinWidthTreewidthExponential.Proofs.Main

theorem twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      TwinWidthTreewidthExponential.Statements.Main.treewidth (V := V) G ≤ 2 * k + 4 ∧
        2 ^ k < TwinWidthTreewidthExponential.Statements.Main.twinWidth (V := V) G :=
  by
    simpa [
      TwinWidthTreewidthExponential.Statements.Main.treewidth,
      TwinWidthTreewidthExponential.Statements.Main.twinWidth
    ] using
      TwinWidth.SimpleGraph.TwinWidthTreewidthContract.exists_graph_treewidth_linear_twin_width_exponential k

end TwinWidthTreewidthExponential.Proofs.Main
