import Lake
open Lake DSL

package TwinWidthTreewidthExponentialTransparent.Statements where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

lean_lib TwinWidthTreewidthExponentialTransparent.Statements.Source where
  srcDir := "../source"
  roots := #[
    `TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Contraction.Trigraph,
    `TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Contraction.TwinWidth,
    `TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Graph.BonnetDepres,
    `TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Graph.BonnetDepresLower,
    `TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Graph.BonnetDepresLowerBasic,
    `TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Graph.Partition,
    `TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Graph.Treewidth,
    `TwinWidthTreewidthExponentialTransparent.Statements.Source.TwinWidth.Graph.TreewidthContract
  ]

@[default_target]
lean_lib TwinWidthTreewidthExponentialTransparent.Statements where
  roots := #[`TwinWidthTreewidthExponentialTransparent.Statements.Main]
