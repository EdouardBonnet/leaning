import TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Equivalence.FunctionalEquivalence
import TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Graph.TreewidthContract

namespace TwinWidthTreewidthExponential.Statements.Main

def GraphParam := TwinWidth.GraphParam

noncomputable def twinWidth : GraphParam :=
  TwinWidth.SimpleGraph.twinWidth

noncomputable def treewidth : GraphParam :=
  TwinWidth.SimpleGraph.treewidth

axiom twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      treewidth (V := V) G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth (V := V) G

end TwinWidthTreewidthExponential.Statements.Main
