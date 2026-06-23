import Lake
open Lake DSL

package FragileMainResult.Proofs where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

require FragileMainResult.Statements from "../statements"

@[default_target]
lean_lib FragileMainResult.Proofs where
  roots := #[
    `Fragile.Contract,
    `Fragile.Coloring,
    `Fragile.Connectivity,
    `Fragile.Theorem3,
    `Fragile.Proofs,
    `FragileMainResult.Proofs.Main
  ]
