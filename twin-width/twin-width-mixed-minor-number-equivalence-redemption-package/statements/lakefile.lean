import Lake
open Lake DSL

package TwinWidthMixedMinorNumberEquivalenceRedemption.Statements where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

require TwinWidthTreewidthExponentialRedemption2.Statements from git
  "https://github.com/EdouardBonnet/leaning.git" @ "6cc23bec12da24170082f54dd965918a75698741" / "twin-width/twin-width-treewidth-exponential-redemption-2-package/statements"

@[default_target]
lean_lib TwinWidthMixedMinorNumberEquivalenceRedemption.Statements where
  roots := #[
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.IntervalDivision,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.VertexOrder,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.GraphParameter,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.FunctionalEquivalence,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.Cell,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedCell,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedMinor,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.MixedNumber,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacency,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Matrix.OrderedAdjacencyMixedNumber,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.SimpleGraph,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Statements.Main
  ]
