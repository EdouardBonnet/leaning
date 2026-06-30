import Lake
open Lake DSL

package TwinWidthTreewidthExponential.Statements where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

lean_lib TwinWidthTreewidthExponential.Statements.Source where
  srcDir := "../source"
  roots := #[
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Contraction.Trigraph,
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Contraction.TwinWidth,
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Equivalence.FunctionalEquivalence,
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Graph.BonnetDepres,
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Graph.BonnetDepresLower,
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Graph.BonnetDepresLowerBasic,
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Graph.Partition,
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Graph.Treewidth,
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Graph.TreewidthContract,
    `TwinWidthTreewidthExponential.Statements.Source.TwinWidth.Graph.TwinWidthTreewidthContract
  ]

@[default_target]
lean_lib TwinWidthTreewidthExponential.Statements where
  roots := #[`TwinWidthTreewidthExponential.Statements.Main]
