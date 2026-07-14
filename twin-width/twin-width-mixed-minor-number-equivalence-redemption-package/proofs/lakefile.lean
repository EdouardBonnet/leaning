import Lake
open Lake DSL

package TwinWidthMixedMinorNumberEquivalenceRedemption.Proofs where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

require TwinWidthMixedMinorNumberEquivalenceRedemption.Statements from "../statements"
require TwinWidthTreewidthExponentialRedemption2.Statements from git
  "https://github.com/EdouardBonnet/leaning.git" @ "6cc23bec12da24170082f54dd965918a75698741" / "twin-width/twin-width-treewidth-exponential-redemption-2-package/statements"

lean_lib TwinWidthMixedMinorNumberEquivalenceRedemption.Source where
  srcDir := "../source"
  roots := #[
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Contraction.Trigraph,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Contraction.TwinWidth,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Equivalence.FunctionalEquivalence,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Equivalence.Main,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Equivalence.MainContract,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Equivalence.MixedToTwinWidth,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Equivalence.TwinWidthToMixed,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Graph.MixedMinorNumber,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Graph.Partition,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Graph.Theorem14,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Graph.TwinDecomposition,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Cell,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Corner,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.DivisionSequence,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Fusion,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.GridMinor,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.MarcusTardos,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.MixedMinor,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.MixedNumber,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.MixedValue,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.MixedWitness,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.OrderedAdjacency,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Partition,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Symmetric,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Theorem10,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.Theorem10Defs,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Matrix.TwinWidth,
    `TwinWidthMixedMinorNumberEquivalenceRedemption.Source.TwinWidth.Order.Divisions
  ]

@[default_target]
lean_lib TwinWidthMixedMinorNumberEquivalenceRedemption.Proofs where
  roots := #[`TwinWidthMixedMinorNumberEquivalenceRedemption.Proofs.Main]
