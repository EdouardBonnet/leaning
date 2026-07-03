import Lake
open Lake DSL

package TwinWidthTreewidthExponentialRedemption2.Statements where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

@[default_target]
lean_lib TwinWidthTreewidthExponentialRedemption2.Statements where
  roots := #[
    `TwinWidthTreewidthExponentialRedemption2.Statements.ContractedBlack,
    `TwinWidthTreewidthExponentialRedemption2.Statements.ContractedRed,
    `TwinWidthTreewidthExponentialRedemption2.Statements.ContractionSequenceWidth,
    `TwinWidthTreewidthExponentialRedemption2.Statements.ContractionStep,
    `TwinWidthTreewidthExponentialRedemption2.Statements.FinalTrigraphState,
    `TwinWidthTreewidthExponentialRedemption2.Statements.InitialTrigraphState,
    `TwinWidthTreewidthExponentialRedemption2.Statements.LeastNatural,
    `TwinWidthTreewidthExponentialRedemption2.Statements.Main,
    `TwinWidthTreewidthExponentialRedemption2.Statements.RedDegree,
    `TwinWidthTreewidthExponentialRedemption2.Statements.SingletonBags,
    `TwinWidthTreewidthExponentialRedemption2.Statements.TreeDecompositionWidth,
    `TwinWidthTreewidthExponentialRedemption2.Statements.Treewidth,
    `TwinWidthTreewidthExponentialRedemption2.Statements.TrigraphState,
    `TwinWidthTreewidthExponentialRedemption2.Statements.TwinWidth
  ]
