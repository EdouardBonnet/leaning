import Lake
open Lake DSL

package TwinWidthTreewidthExponentialSelfContained.Proofs where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

require TwinWidthTreewidthExponentialSelfContained.Statements from "../statements"

@[default_target]
lean_lib TwinWidthTreewidthExponentialSelfContained.Proofs where
  roots := #[`TwinWidthTreewidthExponentialSelfContained.Proofs.Main]
