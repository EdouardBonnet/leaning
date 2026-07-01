import TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.BonnetDepresLower

namespace TwinWidthTreewidthExponentialSelfContained.Statements.Main

axiom twin_width_can_be_exponential_in_treewidth
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
                then Nat.find htww else 0)

end TwinWidthTreewidthExponentialSelfContained.Statements.Main
