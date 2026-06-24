import Lake
open Lake DSL

package TwinWidthTreewidthExponential.Proofs where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

require TwinWidthMixedMinorNumberEquivalence.Statements from git
  "https://github.com/EdouardBonnet/leaning.git" @ "48fe9ce5ff8a4538efaa0bf1a18a4a5f8100a2ba" / "twin-width/twin-width-mixed-minor-number-equivalence-package/statements"

require TwinWidthTreewidthExponential.Statements from "../statements"

@[default_target]
lean_lib TwinWidthTreewidthExponential.Proofs where
  roots := #[`TwinWidthTreewidthExponential.Proofs.Main]
