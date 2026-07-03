import Lake
open Lake DSL

package TwinWidthTreewidthExponentialRedemption2.Proofs where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

require TwinWidthTreewidthExponentialRedemption2.Statements from "../statements"

@[default_target]
lean_lib TwinWidthTreewidthExponentialRedemption2.Proofs where
  roots := #[
    `TwinWidthTreewidthExponentialRedemption2.Statements.Source.TwinWidth.Contraction.Trigraph,
    `TwinWidthTreewidthExponentialRedemption2.Statements.Source.TwinWidth.Contraction.TwinWidth,
    `TwinWidthTreewidthExponentialRedemption2.Statements.Source.TwinWidth.Graph.BonnetDepres,
    `TwinWidthTreewidthExponentialRedemption2.Statements.Source.TwinWidth.Graph.BonnetDepresLower,
    `TwinWidthTreewidthExponentialRedemption2.Statements.Source.TwinWidth.Graph.BonnetDepresLowerBasic,
    `TwinWidthTreewidthExponentialRedemption2.Statements.Source.TwinWidth.Graph.Partition,
    `TwinWidthTreewidthExponentialRedemption2.Statements.Source.TwinWidth.Graph.Treewidth,
    `TwinWidthTreewidthExponentialRedemption2.Statements.Source.TwinWidth.Graph.TreewidthContract,
    `TwinWidthTreewidthExponentialRedemption2.Proofs.Main
  ]
