import Lake
open Lake DSL

package TwinWidthTreewidthExponentialRedemption.Proofs where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

require TwinWidthTreewidthExponentialRedemption.Statements from "../statements"

@[default_target]
lean_lib TwinWidthTreewidthExponentialRedemption.Proofs where
  roots := #[
    `TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Contraction.Trigraph,
    `TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Contraction.TwinWidth,
    `TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Graph.BonnetDepres,
    `TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Graph.BonnetDepresLower,
    `TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Graph.BonnetDepresLowerBasic,
    `TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Graph.Partition,
    `TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Graph.Treewidth,
    `TwinWidthTreewidthExponentialRedemption.Statements.Source.TwinWidth.Graph.TreewidthContract,
    `TwinWidthTreewidthExponentialRedemption.Proofs.Main
  ]
