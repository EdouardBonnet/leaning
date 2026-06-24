import TwinWidthTreewidthExponential.Statements.Main

namespace TwinWidthTreewidthExponential.Proofs.Main

theorem twin_width_can_be_exponential_in_treewidth
    (k : Nat) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V),
      TwinWidthTreewidthExponential.Statements.Main.treewidth (V := V) G ≤ 2 * k + 4 ∧
        2 ^ k < TwinWidthTreewidthExponential.Statements.Main.twinWidth (V := V) G :=
  TwinWidthTreewidthExponential.Statements.Main.bonnet_depres_exponential_gap k

end TwinWidthTreewidthExponential.Proofs.Main
