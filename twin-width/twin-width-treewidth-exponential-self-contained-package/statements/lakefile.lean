import Lake
open Lake DSL

package TwinWidthTreewidthExponentialSelfContained.Statements where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

lean_lib TwinWidthTreewidthExponentialSelfContained.Statements.Source where
  srcDir := "../source"
  roots := #[
    `TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Contraction.Trigraph,
    `TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Contraction.TwinWidth,
    `TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.BonnetDepres,
    `TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.BonnetDepresLower,
    `TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.BonnetDepresLowerBasic,
    `TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.Partition,
    `TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.Treewidth,
    `TwinWidthTreewidthExponentialSelfContained.Statements.Source.TwinWidth.Graph.TreewidthContract
  ]

@[default_target]
lean_lib TwinWidthTreewidthExponentialSelfContained.Statements where
  roots := #[`TwinWidthTreewidthExponentialSelfContained.Statements.Main]
