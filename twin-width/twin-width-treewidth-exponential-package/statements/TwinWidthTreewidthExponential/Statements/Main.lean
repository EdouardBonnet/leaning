import Mathlib.Combinatorics.SimpleGraph.Basic
import TwinWidthMixedMinorNumberEquivalence.Statements.Main

namespace TwinWidthTreewidthExponential.Statements.Main

def GraphParam := TwinWidthMixedMinorNumberEquivalence.Statements.Main.GraphParam

noncomputable def twinWidth : GraphParam :=
  TwinWidthMixedMinorNumberEquivalence.Statements.Main.twinWidth

axiom treewidth : GraphParam

axiom bonnet_depres_exponential_gap
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      treewidth (V := V) G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth (V := V) G

axiom twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      treewidth (V := V) G ≤ 2 * k + 4 ∧ 2 ^ k < twinWidth (V := V) G

end TwinWidthTreewidthExponential.Statements.Main
