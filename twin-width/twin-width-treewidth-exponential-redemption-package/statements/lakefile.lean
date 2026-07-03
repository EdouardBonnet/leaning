import Lake
open Lake DSL

package TwinWidthTreewidthExponentialRedemption.Statements where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

@[default_target]
lean_lib TwinWidthTreewidthExponentialRedemption.Statements where
  roots := #[
    `TwinWidthTreewidthExponentialRedemption.Statements.ContractedBlack,
    `TwinWidthTreewidthExponentialRedemption.Statements.ContractedRed,
    `TwinWidthTreewidthExponentialRedemption.Statements.ContractionSequenceWidth,
    `TwinWidthTreewidthExponentialRedemption.Statements.ContractionStep,
    `TwinWidthTreewidthExponentialRedemption.Statements.FinalTrigraphState,
    `TwinWidthTreewidthExponentialRedemption.Statements.InitialTrigraphState,
    `TwinWidthTreewidthExponentialRedemption.Statements.Main,
    `TwinWidthTreewidthExponentialRedemption.Statements.RedDegree,
    `TwinWidthTreewidthExponentialRedemption.Statements.SingletonBags,
    `TwinWidthTreewidthExponentialRedemption.Statements.TreeDecompositionWidth,
    `TwinWidthTreewidthExponentialRedemption.Statements.Treewidth,
    `TwinWidthTreewidthExponentialRedemption.Statements.TrigraphState,
    `TwinWidthTreewidthExponentialRedemption.Statements.TwinWidth
  ]
